-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_stopped_noncube_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:16:23.764003+00:00
-- url     : https://prove2.me/submissions/ef63e8df-7cbb-4ecb-973e-4c04adbbd4d7

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A015
import Theorems.Thm_OAI_CubicFirstMoment_angular_stoppedBeta_distinguished_log_saving_all
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
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeCutoffSum_eq_sum (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum f X = ∑ p ∈ primeCutoff X, f p := by
  unfold primeCutoffSum
  rw [tsum_eq_sum (s := primeCutoff X)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [mem_primeCutoff.mp hp]
  · intro p hp
    simp only [mem_primeCutoff] at hp
    simp [hp]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

@[simp] theorem primeCutoffSum_add (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p + g p) X =
      primeCutoffSum f X + primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_add_distrib]

@[simp] theorem primeCutoffSum_sub (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p - g p) X =
      primeCutoffSum f X - primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_sub_distrib]

@[simp] theorem primeCutoffSum_const_mul (z : ℂ) (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => z * f p) X = z * primeCutoffSum f X := by
  simp only [primeCutoffSum_eq_sum, Finset.mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

theorem normTwist_mul (u : ℝ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    normTwist u (a * b) = normTwist u a * normTwist u b := by
  have han : norm a ≠ 0 := (norm_eq_zero_iff.not.mpr ha)
  have hbn : norm b ≠ 0 := (norm_eq_zero_iff.not.mpr hb)
  have hn : norm (a * b) = norm a * norm b := Complex.normSq_mul _ _
  simp only [normTwist, hn, Real.log_mul han hbn, mul_add, Complex.ofReal_add,
    add_mul, Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedAbel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weighting of prime-character sums

Partial summation applies the
published unweighted Hecke prime estimate to independently specified
smooth prime weights. It also retains the derivative cost of a norm twist.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Complex partial summation with an explicit bound for the cumulative
coefficients. The right side records endpoint values and total variation. -/
theorem weighted_abel_bound (c : ℕ → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hc : ∀ t ∈ Set.Icc a b, ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ H) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  let S : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hSa : ‖S a‖ ≤ H := hc a ⟨le_rfl, hab⟩
  have hSb : ‖S b‖ ≤ H := hc b ⟨hab, le_rfl⟩
  have hp : IntegrableOn (fun t => deriv f t * S t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc c ha hderiv).mono_set Set.Ioc_subset_Icc_self
  have hd0 : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Icc a b) :=
    hderiv.norm.const_mul H
  have hd : IntegrableOn (fun t => H * ‖deriv f t‖) (Set.Ioc a b) :=
    hd0.mono_set Set.Ioc_subset_Icc_self
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖deriv f t * S t‖ ≤ H * ‖deriv f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, mul_comm H]
    exact mul_le_mul_of_nonneg_left (hc t (Set.Ioc_subset_Icc_self ht))
      (_root_.norm_nonneg _)
  have hIntegral : ‖∫ t in Set.Ioc a b, deriv f t * S t‖ ≤
      H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, ‖deriv f t * S t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, H * ‖deriv f t‖ := integral_mono_ae hp.norm hd hpoint
      _ = _ := integral_const_mul H _
  rw [sum_mul_eq_sub_sub_integral_mul c ha hab hdiff hderiv]
  change ‖f b * S b - f a * S a - ∫ t in Set.Ioc a b, deriv f t * S t‖ ≤ _
  calc
    _ ≤ ‖f b * S b - f a * S a‖ + ‖∫ t in Set.Ioc a b, deriv f t * S t‖ :=
      norm_sub_le _ _
    _ ≤ (‖f b * S b‖ + ‖f a * S a‖) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ :=
      add_le_add (norm_sub_le _ _) hIntegral
    _ ≤ (‖f b‖ * H + ‖f a‖ * H) +
        H * ∫ t in Set.Ioc a b, ‖deriv f t‖ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hSb (_root_.norm_nonneg _))
        (mul_le_mul_of_nonneg_left hSa (_root_.norm_nonneg _))) le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published prime input to smooth prime weights

Prime elements of equal norm are collected without identifying conjugate
prime ideals. Complex Abel summation then derives the smooth-weighted
estimate from `CubicPrimeSiegelWalfisz`. The weighted estimate follows by partial summation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma primeNormCoefficient_cumulative (R t : ℝ) (χ : Eisenstein → ℂ)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeNormCoefficient R χ n) = primeCutoffSum χ t := by
  simp only [primeNormCoefficient]
  rw [Finset.sum_comm, primeCutoffSum_eq_sum]
  have he (p : Eisenstein) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, if n = normNat p then χ p else 0) =
        if norm p ≤ t then χ p else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, Nat.zero_le, true_and]
    simp only [Nat.le_floor_iff ht, normNat_cast]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.trans htR⟩, hp.2⟩

lemma primeNormCoefficient_weighted (a b : ℝ) (f : ℝ → ℂ) (χ : Eisenstein → ℂ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * primeNormCoefficient b χ n) =
      ∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p := by
  simp only [primeNormCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : normNat p ≤ ⌊b⌋₊ := (Nat.le_floor_iff (ha.trans hab)).mpr
    (by rw [normNat_cast]; exact (mem_primeCutoff.mp hp).2)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_Ioc, hpb, and_true]
  simp only [Nat.floor_lt ha, normNat_cast]

/-- Weighted interval sums inherit a uniform bound for all their unweighted
prime prefixes, at the explicit cost of total variation of the weight. -/
theorem weighted_prime_bound (χ : Eisenstein → ℂ) (f : ℝ → ℂ)
    {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hderiv : IntegrableOn (deriv f) (Set.Icc a b))
    (hχ : ∀ t ∈ Set.Icc a b, ‖primeCutoffSum χ t‖ ≤ H) :
    ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p) * χ p‖ ≤
      H * (‖f a‖ + ‖f b‖ + ∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  rw [← primeNormCoefficient_weighted a b f χ ha hab]
  apply weighted_abel_bound (primeNormCoefficient b χ) f ha hab hdiff hderiv
  intro t ht
  rw [primeNormCoefficient_cumulative b t χ (ha.trans ht.1) ht.2]
  exact hχ t ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem hasDerivAt_mellinPhase (u : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (mellinPhase u)
      (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I) x := by
  have h := (((Real.hasDerivAt_log hx).const_mul u).ofReal_comp.mul_const Complex.I).cexp
  unfold mellinPhase
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

theorem hasDerivAt_weighted_mellinPhase {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (u : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => w t * mellinPhase u t)
      (w' * mellinPhase u x + w x * (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I)) x :=
  hw.mul (hasDerivAt_mellinPhase u hx)

/-- The derivative loss is linear in the Mellin height and inversely
proportional to the norm variable. -/
theorem norm_deriv_weighted_mellinPhase {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (u : ℝ) (hx : 0 < x) :
    ‖deriv (fun t => w t * mellinPhase u t) x‖ ≤
      ‖w'‖ + ‖w x‖ * (|u| / x) := by
  rw [(hasDerivAt_weighted_mellinPhase hw u hx.ne').deriv]
  calc
    _ ≤ ‖w' * mellinPhase u x‖ +
        ‖w x * (mellinPhase u x * ((u / x : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, mellinPhase_norm, Complex.norm_I, mul_one, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

private lemma eventually_loglog_small (a b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      a + b * Real.log (Real.log x) ≤ ε * Real.sqrt (Real.log x) := by
  have hlim : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hc : (fun _ : ℝ => a) =o[atTop] (fun x => Real.sqrt (Real.log x)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hlim
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    Real.tendsto_log_atTop
  have hl' : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
      (fun x => Real.sqrt (Real.log x)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl
  have h := (hc.add (hl'.const_mul_left b)).def hε
  filter_upwards [h] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx)

/-- Logarithmic conductor growth makes the published exponential error
smaller than any prescribed logarithmic saving, uniformly in the conductor. -/
lemma heckeExponentialError_logSaving {c K A D : ℝ}
    (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ K * (Real.log x) ^ A →
      heckeExponentialError c x Q ≤ 16 * x / (Real.log x) ^ D := by
  have hcond := eventually_loglog_small (Real.log K) A 1 zero_lt_one
  have hdecay := eventually_loglog_small 0 (D + 4) (c / 2) (by positivity)
  filter_upwards [hcond, hdecay, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcond hdecay hL hx Q hQ hQmax
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < Real.log x := Real.log_pos hx
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hlogQ₀ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log x) := by
    have h := Real.log_le_log hQ₀ hQmax
    rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hL₀ A).ne', Real.log_rpow hL₀] at h
    exact h.trans (by simpa only [one_mul] using hcond)
  have hroot : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hL₀
  have hd : 0 < Real.log Q + Real.sqrt (Real.log x) := by positivity
  have hratio : Real.sqrt (Real.log x) / 2 ≤
      Real.log x / (Real.log Q + Real.sqrt (Real.log x)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.sq_sqrt hL₀.le]
  have he₁ : Real.exp (-c * Real.log x / (Real.log Q + Real.sqrt (Real.log x))) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -c * (Real.log x / (Real.log Q + Real.sqrt (Real.log x))) := by ring
      _ ≤ _ := by nlinarith
  have he₂ : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      (Real.log x) ^ (-(D + 4)) := by
    rw [Real.rpow_def_of_pos hL₀]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlogprod : Real.log (x * Q) ≤ 2 * Real.log x := by
    rw [Real.log_mul hx₀.ne' hQ₀.ne']
    have hq := hlogQ.trans (Real.sqrt_le_self_iff.mpr (Or.inr hL))
    linarith
  have hpoly : (Real.log (x * Q)) ^ 4 ≤ 16 * (Real.log x) ^ 4 := by
    calc
      _ ≤ (2 * Real.log x) ^ 4 := by
        gcongr
        exact Real.log_nonneg (by nlinarith)
      _ = _ := by ring
  have hpow : (Real.log x) ^ 4 * (Real.log x) ^ (-(D + 4)) =
      1 / (Real.log x) ^ D := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL₀]
    norm_num
    rw [Real.rpow_neg hL₀.le]
  calc
    heckeExponentialError c x Q ≤
        x * (16 * (Real.log x) ^ 4) * (Real.log x) ^ (-(D + 4)) := by
      unfold heckeExponentialError
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly hx₀.le)
        (he₁.trans he₂) (Real.exp_nonneg _) (by positivity)
    _ = 16 * x / (Real.log x) ^ D := by rw [mul_assoc, mul_assoc, hpow]; ring

/-- The prime-power deletion error is also negligible at every fixed
logarithmic scale. -/
lemma sqrt_logSq_logSaving (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * (Real.log x) ^ 2 ≤ x / (Real.log x) ^ D := by
  have h := (isLittleO_log_rpow_rpow_atTop (D + 2)
    (by norm_num : (0 : ℝ) < 1 / 2)).def zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hL₀ : 0 < Real.log x := Real.log_pos hx₁
  have hsmall : (Real.log x) ^ (D + 2) ≤ Real.sqrt x := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hL₀.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _), one_mul, Real.sqrt_eq_rpow] using hx
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL₀ D)).mpr
  calc
    _ = Real.sqrt x * (Real.log x) ^ (D + 2) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hL₀]
      congr 2
      ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx₀.le

lemma angularConductorFactor_ge_one (ℓ : ℤ) : 1 ≤ angularConductorFactor ℓ := by
  unfold angularConductorFactor
  nlinarith [abs_nonneg (ℓ : ℝ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-angular prime estimates for the literal ramified numerator

This is the nonexceptional degree-two specialization of Kaneko--Thorner,
*Highly uniform prime number theorems*, Ann. Inst. Fourier 75 (2025),
Theorem 1.2, pp.1904--1905 (Iwaniec--Kowalski, Theorem 5.13), with the
fixed-type zero-free region of Rajan (1998), Proposition 1 and Section 1.
The finite character is `cubicNumeratorChar` of modulus `9*v`; its
identification on primary elements is proved from
`CubicSupplementaryPeriodicity` in `CubicNumeratorCharacter`.

The analytic conductor majorant is
`3 * N(9*v) * (|ell|/2+3) * (|ell|/2+4)`:
`N(9*v)=81*N(v)`, so its constant is 243. The nonzero angular type
excludes a principal/exceptional-real character. The raw input below
retains the exponential conductor error and the prime-power deletion
term. Logarithmic and weighted estimates are deductions, not inputs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma angularKummerConductorFactor_ge_one (ℓ : ℤ) :
    1 ≤ angularKummerConductorFactor ℓ := by
  have h := angularConductorFactor_ge_one ℓ
  unfold angularKummerConductorFactor
  linarith

lemma angularKummerAnalyticConductor_ge_one (ℓ : ℤ) {v : Eisenstein}
    (hv : v ≠ 0) : 1 ≤ angularKummerAnalyticConductor ℓ v := by
  have hn : (1:ℝ) ≤ norm v := by
    rw [←normNat_cast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hv)
  unfold angularKummerAnalyticConductor
  nlinarith [angularKummerConductorFactor_ge_one ℓ]

theorem angular_kummer_chebyshev_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (_hA : 0 < A) (_hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log x) ^ A →
        ‖primeChebyshev (angularKummerCharacter ℓ v) x‖ ≤ C * x / (Real.log x) ^ D := by
  obtain ⟨B, c, hB, hc, hbound⟩ := hEF ℓ hℓ
  have hK : 0 < angularKummerConductorFactor ℓ := zero_lt_one.trans_le (angularKummerConductorFactor_ge_one ℓ)
  have herr := heckeExponentialError_logSaving (K := angularKummerConductorFactor ℓ)
    (A := A) (D := D) hc hK
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (herr.and (sqrt_logSq_logSaving D))
  refine ⟨17 * B, max X₁ 3, by positivity, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx v hv hnc hcon
  have hx₁ : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx₃ : 3 ≤ x := (le_max_right _ _).trans hx
  have he := (hX₁ x hx₁).1 (angularKummerAnalyticConductor ℓ v)
    (angularKummerAnalyticConductor_ge_one ℓ hv)
    (mul_le_mul_of_nonneg_left hcon hK.le)
  calc
    _ ≤ B * (16 * x / (Real.log x) ^ D + x / (Real.log x) ^ D) :=
      (hbound v hv hnc x hx₃).trans
        (mul_le_mul_of_nonneg_left (add_le_add he (hX₁ x hx₁).2) hB.le)
    _ = _ := by ring

/-- Partial summation removes the logarithmic prime weight, permitting
smooth weights and norm phases. The derivative cost is retained exactly. -/
theorem weighted_angular_kummer_prime_log_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b → ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
        norm v ≤ (Real.log a) ^ A → ∀ f : ℝ → ℂ,
          (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t => f t / (Real.log t : ℂ)) t) →
          IntegrableOn (deriv (fun t => f t / (Real.log t : ℂ))) (Set.Icc a b) →
          ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
            f (norm p) * angularKummerCharacter ℓ v p‖ ≤
          (C * b / (Real.log a) ^ D) *
            (‖f a / (Real.log a : ℂ)‖ + ‖f b / (Real.log b : ℂ)‖ +
              ∫ t in Set.Ioc a b, ‖deriv (fun t => f t / (Real.log t : ℂ)) t‖) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := angular_kummer_chebyshev_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro a b ha hab v hv hnc hcon f hdiff hderiv
  have ha₁ : 1 < a := hX₀.trans_le ha
  have ha₀ : 0 < a := zero_lt_one.trans ha₁
  have hprefix : ∀ t ∈ Set.Icc a b,
      ‖primeCutoffSum (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ)) t‖ ≤
        C * b / (Real.log a) ^ D := by
    intro t ht
    have ht₀ : 0 < t := ha₀.trans_le ht.1
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha₀ ht.1
    have hcon' : norm v ≤ (Real.log t) ^ A :=
      hcon.trans (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hA.le)
    apply (hbound t (ha.trans ht.1) v hv hnc hcon').trans
    exact div_le_div₀ (mul_nonneg hC.le (ht₀.le.trans ht.2))
      (mul_le_mul_of_nonneg_left ht.2 hC.le)
      (Real.rpow_pos_of_pos (Real.log_pos ha₁) D)
      (Real.rpow_le_rpow (Real.log_pos ha₁).le hlog hD.le)
  have h := weighted_prime_bound
    (fun p => angularKummerCharacter ℓ v p * (Real.log (norm p) : ℂ))
    (fun t => f t / (Real.log t : ℂ)) ha₀.le hab hdiff hderiv hprefix
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  have hp₁ : 1 < norm p := ha₁.trans (Finset.mem_filter.mp hp).2
  have hlog : (Real.log (norm p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp₁).ne'
  field_simp


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerPrimeSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw angular Chebyshev estimate implies the ordinary prime
Siegel--Walfisz bound. A square-root initial segment is bounded directly;
partial summation on the remaining interval has bounded reciprocal-log
variation. -/
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma reciprocal_log_variation {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    (∀ t ∈ Icc a b, DifferentiableAt ℝ (fun t => (1:ℂ)/(Real.log t:ℂ)) t) ∧
    IntegrableOn (deriv (fun t => (1:ℂ)/(Real.log t:ℂ))) (Icc a b) ∧
    ‖(1:ℂ)/(Real.log a:ℂ)‖+‖(1:ℂ)/(Real.log b:ℂ)‖+
      (∫ t in Ioc a b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) ≤ 3 := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le ha
  have hla : 1 ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ha
  let f : ℝ → ℝ := fun t => 1/Real.log t
  let g : ℝ → ℝ := fun t => -(t⁻¹)/(Real.log t)^2
  have hder (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt f (g t) t := by
    convert! (hasDerivAt_const t (1:ℝ)).div
      (Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))))
      (Real.log_pos (ha1.trans_le ht.1)).ne' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g,zero_mul,one_mul,zero_sub]
  have hg : ContinuousOn g (Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans (ha1.trans_le ht.1))
    have hlt : Real.log t ≠ 0 := (Real.log_pos (ha1.trans_le ht.1)).ne'
    exact ((continuousAt_id.inv₀ ht0).neg.div ((Real.continuousAt_log ht0).pow 2)
      (pow_ne_zero 2 hlt)).continuousWithinAt
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t = (g t:ℂ) := by
    convert (hder t ht).ofReal_comp.deriv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [f,Complex.ofReal_div,Complex.ofReal_one]
  have hi : IntegrableOn (deriv (fun t => (1:ℂ)/(Real.log t:ℂ))) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).integrableOn_Icc.congr_fun
      (fun t ht => (he t ht).symm) measurableSet_Icc
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) =
      f a-f b := by
    have hn (t : ℝ) (ht : t ∈ Icc a b) :
        ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖ = -g t := by
      rw [he t ht,Complex.norm_real,Real.norm_of_nonpos]
      change -t⁻¹/(Real.log t)^2 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr
        (zero_lt_one.trans (ha1.trans_le ht.1)).le)) (sq_nonneg _)
    rw [←intervalIntegral.integral_of_le hab]
    have hc : (∫ t in a..b, ‖deriv (fun t => (1:ℂ)/(Real.log t:ℂ)) t‖) =
        ∫ t in a..b, -g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact hn t ht
    rw [hc,intervalIntegral.integral_neg]
    have hf : (∫ t in a..b, g t) = f b-f a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hg.intervalIntegrable_of_Icc hab)
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact hder t ht
    rw [hf]
    ring
  refine ⟨?_,hi,?_⟩
  · intro t ht
    simpa only [f,Complex.ofReal_div,Complex.ofReal_one] using
      (hder t ht).ofReal_comp.differentiableAt
  · have hlb : 1 ≤ Real.log b := hla.trans (Real.log_le_log
      (zero_lt_one.trans ha1) hab)
    rw [hint,norm_div,norm_div,norm_one,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (zero_le_one.trans hla),Real.norm_of_nonneg (zero_le_one.trans hlb)]
    have hfa : f a ≤ 1 := by
      simpa only [f,div_one] using one_div_le_one_div_of_le zero_lt_one hla
    have hfb : 0 ≤ f b := by dsimp [f]; positivity
    dsimp [f] at *
    linarith

lemma angularKummerCharacter_norm_le_one (ℓ : ℤ) (v : Eisenstein)
    {p : Eisenstein} (hp : primary p) : ‖angularKummerCharacter ℓ v p‖ ≤ 1 := by
  rw [angularKummerCharacter,norm_mul,norm_theta (primary_ne_zero hp),one_mul]
  exact norm_cubicSymbol_le_one hp v

/-- The unweighted prime estimate is derived from the raw published
Chebyshev error; it is not an additional analytic input. -/
theorem angular_kummer_prime_logSaving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A →
      ‖primeCutoffSum (angularKummerCharacter ℓ v) X‖ ≤ C*X/(Real.log X)^D := by
  obtain ⟨C,Y₀,hC,hY₀,hbound⟩ := weighted_angular_kummer_prime_log_bound hEF ℓ hℓ
    (2*A) (2*D) (by positivity) (by positivity)
  have hroot := Real.tendsto_sqrt_atTop.eventually_ge_atTop (max Y₀ (Real.exp 1))
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (((hroot.and (sqrt_logSq_logSaving D)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 4)).and (eventually_gt_atTop (1:ℝ)))
  refine ⟨18+3*C,max X₀ 2,by positivity,by simp,?_⟩
  intro X hX v hv hnc hNv
  obtain ⟨⟨⟨hr,hs⟩,hlog⟩,hX1⟩ := hX₀ X ((le_max_left _ _).trans hX)
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hLp : 0 < Real.log X := by linarith
  have hsp : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hsY : Y₀ ≤ Real.sqrt X := (le_max_left _ _).trans hr
  have hse : Real.exp 1 ≤ Real.sqrt X := (le_max_right _ _).trans hr
  have hsX : Real.sqrt X ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr hX1.le)
  have hls : Real.log (Real.sqrt X) = Real.log X/2 := Real.log_sqrt hXp.le
  have hls1 : 1 ≤ Real.log (Real.sqrt X) := by rw [hls]; linarith
  have hbase : Real.log X ≤ (Real.log (Real.sqrt X))^2 := by rw [hls]; nlinarith
  have hpow (E : ℝ) (hE : 0 ≤ E) : (Real.log X)^E ≤ (Real.log (Real.sqrt X))^(2*E) := by
    calc
      _ ≤ ((Real.log (Real.sqrt X))^2)^E := Real.rpow_le_rpow hLp.le hbase hE
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast_mul (zero_le_one.trans hls1) 2 E).symm
  have hcon : norm v ≤ (Real.log (Real.sqrt X))^(2*A) := hNv.trans (hpow A hA.le)
  obtain ⟨hd,hi,hvar⟩ := reciprocal_log_variation hse hsX
  have hlarge := hbound (Real.sqrt X) X hsY hsX v hv hnc hcon (fun _ => 1) hd hi
  have hbig : ‖∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
      angularKummerCharacter ℓ v p‖ ≤ 3*C*X/(Real.log X)^D := by
    simp only [one_mul] at hlarge
    apply hlarge.trans
    calc
      _ ≤ (C*X/(Real.log (Real.sqrt X))^(2*D))*3 :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      _ ≤ (C*X/(Real.log X)^D)*3 :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity)
            (Real.rpow_pos_of_pos hLp D) (hpow D hD.le)) (by norm_num)
      _ = _ := by ring
  have hsmall : ‖primeCutoffSum (angularKummerCharacter ℓ v) (Real.sqrt X)‖ ≤
      18*X/(Real.log X)^D := by
    rw [primeCutoffSum_eq_sum]
    have hcard := primary_support_card_le (primeCutoff (Real.sqrt X)) hsp.le
      (fun p hp => ⟨(mem_primeCutoff.mp hp).1.1,(mem_primeCutoff.mp hp).2⟩)
    have hsq : Real.sqrt X ≤ X/(Real.log X)^D := by
      have hx : Real.sqrt X ≤ Real.sqrt X*(Real.log X)^2 :=
        le_mul_of_one_le_right hsp.le (one_le_pow₀ (by linarith))
      exact hx.trans hs
    calc
      _ ≤ ∑ _p ∈ primeCutoff (Real.sqrt X), (1:ℝ) := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun p hp => angularKummerCharacter_norm_le_one ℓ v
          (mem_primeCutoff.mp hp).1.1)
      _ = ((primeCutoff (Real.sqrt X)).card:ℝ) := by simp
      _ ≤ 18*Real.sqrt X := hcard
      _ ≤ 18*(X/(Real.log X)^D) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = _ := by ring
  have hsplit : primeCutoffSum (angularKummerCharacter ℓ v) X =
      primeCutoffSum (angularKummerCharacter ℓ v) (Real.sqrt X)+
        ∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
          angularKummerCharacter ℓ v p := by
    rw [primeCutoffSum_eq_sum,primeCutoffSum_eq_sum]
    have he : (primeCutoff X).filter (fun p => ¬Real.sqrt X < norm p) =
        primeCutoff (Real.sqrt X) := by
      ext p
      simp only [Finset.mem_filter,mem_primeCutoff,not_lt]
      constructor
      · rintro ⟨⟨hp,_⟩,hs⟩; exact ⟨hp,hs⟩
      · rintro ⟨hp,hs⟩; exact ⟨⟨hp,hs.trans hsX⟩,hs⟩
    rw [←he]
    exact (Finset.sum_filter_add_sum_filter_not (primeCutoff X)
      (fun p => Real.sqrt X < norm p) _).symm.trans (add_comm _ _)
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hsmall hbig).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular cubic character, with the argument order of the
cubic residue symbol. Only multiplicativity in the prime variable is used;
the fixed angular factor is not duplicated in the numerator variable. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angularCubicSymbol_mul_lower (ℓ : ℤ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) (v : Eisenstein) :
    angularCubicSymbol ℓ (a*b) v = angularCubicSymbol ℓ a v*angularCubicSymbol ℓ b v := by
  simp only [angularCubicSymbol,angularKummerCharacter,theta_mul,
    cubicSymbol_mul_lower ha hb]
  ring

lemma angularCubicSymbol_norm_le_one (ℓ : ℤ) {a : Eisenstein}
    (ha : primary a) (v : Eisenstein) : ‖angularCubicSymbol ℓ a v‖ ≤ 1 :=
  angularKummerCharacter_norm_le_one ℓ v ha

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeSW
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-angular weighted and long-interval prime bounds derived from
`AngularKummerPrimeExplicitEstimate`. The surviving angular character is
literal, and the interval may begin at exp(sqrt(log X)). -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem weighted_angular_kummer_prime_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log a)^A → ∀ f : ℝ → ℂ,
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*angularKummerCharacter ℓ v p‖ ≤
        (C*b/(Real.log a)^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := angular_kummer_prime_logSaving hEF ℓ hℓ A D hA hD
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro a b ha hab v hv hn hcon f hdiff hderiv
  have ha1 : 1 < a := hX₀.trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  apply weighted_prime_bound (fun p => angularKummerCharacter ℓ v p) f ha0.le hab hdiff hderiv
  intro t ht
  have hat := Real.log_le_log ha0 ht.1
  have ht0 : 0 < t := ha0.trans_le ht.1
  have hc : norm v ≤ (Real.log t)^A := hcon.trans
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hA.le)
  apply (hbound t (ha.trans ht.1) v hv hn hc).trans
  exact div_le_div₀ (mul_nonneg hC.le (ht0.le.trans ht.2))
    (mul_le_mul_of_nonneg_left ht.2 hC.le)
    (Real.rpow_pos_of_pos (Real.log_pos ha1) D)
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hD.le)

/-- The precise raw Kummer prime input, followed by partial summation,
gives arbitrary T-power saving on every interval above a prime scale P
as soon as T <= (log P)^2. Smooth weights retain their actual variation. -/
theorem angular_long_prime_interval_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P R a b : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 → P ≤ a → a ≤ b → b ≤ R*P →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ∀ f : ℝ → ℂ, (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*angularKummerCharacter ℓ v p‖ ≤
        (C*(R*P)/T^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := weighted_angular_kummer_prime_bound hEF ℓ hℓ
    (2*A) (2*D) (by positivity) (by positivity)
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P R a b hT hP hTP hPa hab hb v hv hnc hcon f hdiff hint
  have hP1 : 1 < P := hP₀.trans_le hP
  have hP0 : 0 < P := zero_lt_one.trans hP1
  have ha0 : 0 < a := hP0.trans_le hPa
  have hb0 : 0 < b := ha0.trans_le hab
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hloga : Real.log P ≤ Real.log a := Real.log_le_log hP0 hPa
  have hsquare (E : ℝ) : ((Real.log P)^2)^E = (Real.log P)^(2*E) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hlogP.le 2 E).symm
  have hcon' : norm v ≤ (Real.log a)^(2*A) := by
    calc
      _ ≤ T^A := hcon
      _ ≤ ((Real.log P)^2)^A := Real.rpow_le_rpow hT0.le hTP hA.le
      _ = (Real.log P)^(2*A) := hsquare A
      _ ≤ (Real.log a)^(2*A) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hden : T^D ≤ (Real.log a)^(2*D) := by
    calc
      _ ≤ ((Real.log P)^2)^D := Real.rpow_le_rpow hT0.le hTP hD.le
      _ = (Real.log P)^(2*D) := hsquare D
      _ ≤ (Real.log a)^(2*D) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hfrac : C*b/(Real.log a)^(2*D) ≤ C*(R*P)/T^D :=
    div_le_div₀ (mul_nonneg hC.le (hb0.le.trans hb)) (mul_le_mul_of_nonneg_left hb hC.le)
      (Real.rpow_pos_of_pos hT0 D) hden
  apply (hbound a b (hP.trans hPa) hab v hv hnc hcon' f hdiff hint).trans
  apply mul_le_mul_of_nonneg_right hfrac
  exact add_nonneg (add_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (integral_nonneg (fun _ => _root_.norm_nonneg _))


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeWeightVariation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete total-variation control for rescaled prime weights and their
Mellin twists. This is the cost in the proved Abel summation inequality. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma contDiffOn_rescaled_mellin {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (Y u : ℝ) :
    ContDiffOn ℝ ∞ (fun t => w (t/Y)*mellinPhase u t) (Ioi 0) := by
  intro x hx
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => u*Real.log t) x :=
    contDiffAt_const.mul (Real.contDiffAt_log.mpr (ne_of_gt hx))
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => ((u*Real.log t:ℝ):ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
  have hw' : ContDiff ℝ ∞ (fun t : ℝ => w (t/Y)) := hw.comp (contDiff_id.div_const Y)
  exact (hw'.contDiffAt.mul (hc.mul contDiffAt_const).cexp).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual short Möbius, zeta and logarithmic factors occurring in
the finite ideal convolution identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryElementBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((primaryElementBall X).card : ℝ) ≤ 18*X :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (nonzeroNormBall_card_le hX)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCutoffDerivative
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete detector has a uniformly bounded radial derivative.
This supplies the actual variation cost when one prime is left free in
the stopped coefficient; it is not a sequence-cancellation assumption. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma primeDetectorCutoff_deriv_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    deriv primeDetectorCutoff x = 0 := by
  by_cases hlo : x < 1
  · have he : EqOn primeDetectorCutoff (fun _ : ℝ => (1:ℝ)) (Iio 1) :=
      fun y hy => primeDetectorCutoff_one hy.le
    simpa only [deriv_const] using he.deriv isOpen_Iio hlo
  · have hhi : 2 < x := by
      have h := not_and_or.mp hx
      rcases h with h | h
      · exact False.elim (h (le_of_not_gt hlo))
      · exact lt_of_not_ge h
    have he : EqOn primeDetectorCutoff (fun _ : ℝ => (0:ℝ)) (Ioi 2) :=
      fun y hy => primeDetectorCutoff_zero hy.le
    simpa only [deriv_const] using he.deriv isOpen_Ioi hhi

theorem primeDetectorCutoff_radial_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D := by
  have hd : Continuous (deriv primeDetectorCutoff) :=
    primeDetectorCutoff_smooth.continuous_deriv (by norm_num)
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((hd.norm.mul continuous_id).continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · have h := hD x hmem
    change ‖‖deriv primeDetectorCutoff x‖*x‖ ≤ D at h
    have hn : 0 ≤ ‖deriv primeDetectorCutoff x‖*x := mul_nonneg (_root_.norm_nonneg _) hx.le
    rw [Real.norm_eq_abs,abs_of_nonneg hn] at h
    simpa only [Real.norm_eq_abs] using h.trans (le_max_left D 0)
  · rw [primeDetectorCutoff_deriv_zero hmem,abs_zero,zero_mul]
    exact le_max_right _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cutoff weights on a free long prime. Their variation depends
on its dyadic ratio and Mellin height, not on the cutoff scales. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma radial_mellin_interval_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {P R a b M D : ℝ} (hP : 0 < P) (_hR : 1 ≤ R) (ha : P ≤ a)
    (hab : a ≤ b) (hb : b ≤ R*P) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w t*mellinPhase u t
    (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc a b) ∧
    ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|) := by
  dsimp only
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := fun _ ht => hP.trans_le (ha.trans ht.1)
  have hs : ContDiffOn ℝ ∞ (fun t => w t*mellinPhase u t) (Ioi 0) := by
    simpa only [div_one] using contDiffOn_rescaled_mellin hw 1 u
  have hd : ContinuousOn (deriv (fun t => w t*mellinPhase u t)) (Icc a b) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hs t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by norm_num)
  have hpoint (t : ℝ) (ht : t ∈ uIoc a b) :
      ‖‖deriv (fun t => w t*mellinPhase u t) t‖‖ ≤ (D+M*|u|)/P := by
    rw [uIoc_of_le hab] at ht
    have htP : P ≤ t := ha.trans ht.1.le
    have ht0 : 0 < t := hP.trans_le htP
    rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
    have hder := norm_deriv_weighted_mellinPhase
      ((hw.differentiable (by norm_num)).differentiableAt.hasDerivAt) u ht0
    have hdw : ‖deriv w t‖ ≤ D/t := (le_div_iff₀ ht0).mpr (hwd t ht0)
    calc
      _ ≤ D/t+M*(|u|/t) := hder.trans (add_le_add hdw
        (mul_le_mul_of_nonneg_right (hwm t) (div_nonneg (abs_nonneg _) ht0.le)))
      _ = (D+M*|u|)/t := by ring
      _ ≤ (D+M*|u|)/P := div_le_div_of_nonneg_left
        (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP htP
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => w t*mellinPhase u t) t‖) ≤
      (R-1)*(D+M*|u|) := by
    rw [←intervalIntegral.integral_of_le hab]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    have hn : 0 ≤ ∫ t in a..b, ‖deriv (fun t => w t*mellinPhase u t) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    apply hi.trans
    calc
      (D+M*|u|)/P*(b-a) ≤ (D+M*|u|)/P*((R-1)*P) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (div_nonneg
          (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP.le)
      _ = (R-1)*(D+M*|u|) := by field_simp
  have hnorm (x : ℝ) : ‖w x*mellinPhase u x‖ ≤ M := by
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm x
  linarith [hnorm a,hnorm b]

lemma primeDetectorCutoff_rescaled_smooth (c : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (primeDetectorCutoff (t/c):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (primeDetectorCutoff_smooth.comp (contDiff_id.div_const c))

lemma primeDetectorCutoff_rescaled_norm (c t : ℝ) :
    ‖(primeDetectorCutoff (t/c):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (primeDetectorCutoff_nonneg _)]
  exact primeDetectorCutoff_le_one _

lemma primeDetectorCutoff_rescaled_deriv {D : ℝ}
    (hD : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ‖deriv (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ)) t‖*t ≤ D := by
  have hd := (((primeDetectorCutoff_smooth.differentiable (by norm_num)).differentiableAt
    (x := t/c)).hasDerivAt.comp t ((hasDerivAt_id t).div_const c)).ofReal_comp
  change HasDerivAt (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ))
    ((deriv primeDetectorCutoff (t/c)*(1/c):ℝ):ℂ) t at hd
  rw [hd.deriv,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (div_pos zero_lt_one hc)]
  convert hD (t/c) (div_pos ht hc) using 1 <;> first | rfl | ring

/-- The same constant works for every cutoff scale. This is the actual
selected-bin prime weight, including any permitted norm twist. -/
theorem long_prime_cutoff_variation :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (c P R a b u : ℝ), 0 < c → 0 < P → 1 ≤ R →
      P ≤ a → a ≤ b → b ≤ R*P →
      let f := fun t => (primeDetectorCutoff (t/c):ℂ)*mellinPhase u t
      (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
      IntegrableOn (deriv f) (Icc a b) ∧
      ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤ 2+(R-1)*(D+|u|) := by
  obtain ⟨D,hD,hder⟩ := primeDetectorCutoff_radial_deriv_bound
  refine ⟨D,hD,?_⟩
  intro c P R a b u hc hP hR ha hab hb
  simpa only [mul_one,one_mul] using radial_mellin_interval_variation
    (primeDetectorCutoff_rescaled_smooth c) hP hR ha hab hb zero_le_one hD
    (primeDetectorCutoff_rescaled_norm c) (fun t ht => primeDetectorCutoff_rescaled_deriv
      hder hc ht) u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryPrime_product_squarefree (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) : Squarefree (∏ p ∈ U, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr (primaryPrimes_isCoprime (hU p hp) (hU q hq) hpq)
  · intro p hp
    exact (hU p hp).2.squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal primary-divisor Möbius expansion used in the small-R
branch, and its exact splitting at a prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_product (ψ : ℝ → ℝ) (w : ℝ) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p) :
    cutoffMoebius ψ w (∏ p ∈ s, p) = ∏ p ∈ s, -(ψ (norm p/w):ℂ) := by
  rw [cutoffMoebius,primaryPrimeFactors_finset_prod s hs,
    idealMoebius_prod_primaryPrimes s hs,Finset.prod_neg]
  push_cast
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit cost of the coprimality exclusion in a prime constituent.
It follows from the proved ideal-divisor bound, uniformly in the excluded
element, and will be subtracted from the prime Siegel–Walfisz estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_exclusion_difference (S : Finset Eisenstein) (e : Eisenstein)
    (w : Eisenstein → ℂ) {M : ℝ} (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*((S.filter (fun p => ¬ IsCoprime p e)).card:ℝ) := by
  have he : (∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p) =
      ∑ p ∈ S with ¬ IsCoprime p e, w p := by
    rw [Finset.sum_filter,Finset.sum_filter,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : IsCoprime p e <;> simp only [hp,ite_true, if_true,ite_false, if_false,not_true_eq_false,
      not_false_eq_true,sub_self,sub_zero]
  rw [he]
  calc
    _ ≤ ∑ p ∈ S with ¬ IsCoprime p e, ‖w p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S with ¬ IsCoprime _p e, M :=
      Finset.sum_le_sum (fun p hp => hw p (Finset.mem_filter.mp hp).1)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionLog
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic, rather than merely subpower, number of prime
exclusions. This is necessary when the free prime is exp(sqrt(log X)). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_prime_divisor_card_log (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0) :
    ((S.filter (fun p => p ∣ e)).card:ℝ) ≤ Real.log (norm e)/Real.log 2 := by
  let T := S.filter (fun p => p ∣ e)
  have hp (p : Eisenstein) (hp : p ∈ T) : primaryPrime p :=
    hS p (Finset.mem_filter.mp hp).1
  have hd : (∏ p ∈ T, p) ∣ e := by
    apply Finset.prod_dvd_of_coprime
    · intro p hpT q hqT hpq
      exact primaryPrimes_isCoprime (hp p hpT) (hp q hqT) hpq
    · intro p hpT
      exact (Finset.mem_filter.mp hpT).2
  have hprod : (2:ℝ)^T.card ≤ norm e := by
    calc
      _ = ∏ _p ∈ T, (2:ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ T, norm p := Finset.prod_le_prod (fun _ _ => by norm_num)
        (fun p hpT => primaryPrime_norm_ge_two (hp p hpT))
      _ = norm (∏ p ∈ T, p) := (norm_finset_prod _ _).symm
      _ ≤ norm e := norm_le_of_dvd_nonzero he hd
  have hn : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
  exact (Real.pow_le_iff_le_log (by norm_num : (0:ℝ) < 2) hn).mp hprod

theorem prime_exclusion_logarithmic (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0)
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*(Real.log (norm e)/Real.log 2) := by
  have hsub : S.filter (fun p => ¬IsCoprime p e) ⊆ S.filter (fun p => p ∣ e) := by
    intro p hp
    obtain ⟨hpS,hp⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    by_contra hn
    exact hp ((hS p hpS).2.irreducible.coprime_iff_not_dvd.mpr hn)
  exact (prime_exclusion_difference S e w hw).trans
    (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (primary_prime_divisor_card_log S hS e he)) hM)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete free selected-bin prime satisfies the needed prime
cancellation, uniformly in its cutoff scale and interval endpoints. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_cutoff_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P a b c u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < c →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p),
        (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        C*P/T^D*(1+|u|) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := angular_long_prime_interval_bound hEF ℓ hℓ hA hD
  obtain ⟨V,hV,hvar⟩ := long_prime_cutoff_variation
  refine ⟨2*C*(V+2),P₀,by positivity,hP₀,?_⟩
  intro T P a b c u hT hP hTP ha hab hb hc v hv hnc hNv
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le hP)
  obtain ⟨hdiff,hint,hvariation⟩ := hvar c P 2 a b u hc hP0 (by norm_num) ha hab hb
  have hVbound : 2+(2-1)*(V+|u|) ≤ (V+2)*(1+|u|) := by
    nlinarith [abs_nonneg u,mul_nonneg hV (abs_nonneg u)]
  have hf : 0 ≤ C*(2*P)/T^D := by positivity
  calc
    _ ≤ (C*(2*P)/T^D)*(2+(2-1)*(V+|u|)) :=
      (hbound T P 2 a b hT hP hTP ha hab hb v hv hnc hNv _ hdiff hint).trans
        (mul_le_mul_of_nonneg_left hvariation hf)
    _ ≤ (C*(2*P)/T^D)*((V+2)*(1+|u|)) := mul_le_mul_of_nonneg_left hVbound hf
    _ = _ := by ring

/-- The exact logarithmic deletion error is retained, so this theorem
also applies to the polynomial-norm exclusions in the stopped sequence. -/
theorem angular_long_prime_cutoff_excluded_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P a b c u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < c →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter (fun p => IsCoprime p e),
        (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v‖ ≤
        C*P/T^D*(1+|u|)+Real.log (norm e)/Real.log 2 := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := angular_long_prime_cutoff_bound hEF ℓ hℓ hA hD
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P a b c u hT hP hTP ha hab hb hc v e hv hnc hNv he
  let S := (primeCutoff b).filter (fun p => a < norm p)
  let f := fun p : Eisenstein =>
    (primeDetectorCutoff (norm p/c):ℂ)*mellinPhase u (norm p)*angularCubicSymbol ℓ p v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
  have hweight (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
    exact (mul_le_mul (primeDetectorCutoff_rescaled_norm c (norm p))
      (angularCubicSymbol_norm_le_one ℓ (hS p hp).1 v) (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have herr := prime_exclusion_logarithmic S hS e he f zero_le_one hweight
  have hnorm : ‖∑ p ∈ S with IsCoprime p e, f p‖ ≤
      ‖∑ p ∈ S, f p‖+‖(∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p)‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (∑ p ∈ S, f p)
      ((∑ p ∈ S, f p)-(∑ p ∈ S with IsCoprime p e, f p))
  exact hnorm.trans (add_le_add (hbound T P a b c u hT hP hTP ha hab hb hc v hv hnc hNv)
    (by simpa only [one_mul] using herr))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryPairCoefficient_sum (S T : Finset Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) (F : Eisenstein → ℂ) :
    (∑ b ∈ primaryPairSupport S T, primaryPairCoefficient S T w b*F b) =
      ∑ p ∈ S ×ˢ T, w p*F (p.1*p.2) := by
  unfold primaryPairCoefficient primaryPairFiber
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b ∈ primaryPairSupport S T,
        ∑ p ∈ S ×ˢ T with p.1*p.2 = b, w p*F (p.1*p.2) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem _ hp) _

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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficientBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMoebiusExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one prime from the actual unordered cutoff-Mobius product.
The remaining coefficient and character are constant on the free prime;
there is no permutation or divisor multiplicity in this identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_prime_mul (ψ : ℝ → ℝ) (w : ℝ)
    {p c : Eisenstein} (hp : primaryPrime p) (hc : primary c)
    (hs : Squarefree c) (hpc : ¬p ∣ c) :
    cutoffMoebius ψ w (p*c) = -(ψ (norm p/w):ℂ)*cutoffMoebius ψ w c := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hf : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  calc
    _ = cutoffMoebius ψ w (∏ q ∈ insert p (primaryPrimeFactors c), q) := by
      rw [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs]
    _ = ∏ q ∈ insert p (primaryPrimeFactors c), -(ψ (norm q/w):ℂ) :=
      cutoffMoebius_prime_product ψ w _ hf
    _ = -(ψ (norm p/w):ℂ)*cutoffMoebius ψ w c := by
      rw [Finset.prod_insert hpnot,←cutoffMoebius_prime_product ψ w (primaryPrimeFactors c)
        (fun q hq => (primaryPrimeFactor_spec hc hq).1),primaryPrimeFactors_prod hc hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeMoebiusExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one prime from the actual unordered cutoff-Mobius product.
The remaining coefficient and character are constant on the free prime;
there is no permutation or divisor multiplicity in this identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_cutoffMoebius_free_prime_identity (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (ψ : ℝ → ℝ) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (hs : Squarefree c) (v : Eisenstein) :
    (∑ p ∈ S with ¬p ∣ c,
      cutoffMoebius ψ w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v) =
    (-cutoffMoebius ψ w c*normTwist u c*angularCubicSymbol ℓ c v)*
      ∑ p ∈ S with ¬p ∣ c, (ψ (norm p/w):ℂ)*normTwist u p*angularCubicSymbol ℓ p v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpS,hpc⟩ := Finset.mem_filter.mp hp
  have hp' := hS p hpS
  rw [cutoffMoebius_prime_mul ψ w hp' hc hs hpc,
    normTwist_mul u hp'.2.ne_zero (primary_ne_zero hc),
    angularCubicSymbol_mul_lower ℓ hp'.2.ne_zero (primary_ne_zero hc)]
  ring

lemma angular_cutoffMoebius_free_prime_prefactor_bound (ℓ : ℤ) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w u : ℝ)
    {c : Eisenstein} (hc : primary c) (v : Eisenstein) :
    ‖-cutoffMoebius ψ w c*normTwist u c*angularCubicSymbol ℓ c v‖ ≤ 1 := by
  rw [norm_mul,norm_mul,norm_neg,norm_normTwist,mul_one]
  exact (mul_le_mul (cutoffMoebius_norm_le_one hψ w c) (angularCubicSymbol_norm_le_one ℓ hc v)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free selected-bin prime in the literal cutoff-Mobius coefficient.
All other factors remain fixed, including the coprimality exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_moebius_bound (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*P/T^D*(1+|u|)+Real.log (norm (c*e))/Real.log 2 := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_cutoff_excluded_bound hEF ℓ hℓ hA hD
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw c v e hc hs hv hnc hNv he
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter
    (fun p => IsCoprime p (c*e))
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hfilter : S.filter (fun p => ¬p ∣ c) = S := by
    apply Finset.filter_true_of_mem
    intro p hp hd
    have hpe := (Finset.mem_filter.mp hp).2
    have hpc : IsCoprime p c := hpe.of_isCoprime_of_dvd_right (dvd_mul_right c e)
    exact (hS p hp).2.not_isUnit (hpc.isUnit_of_dvd hd)
  have hid := angular_cutoffMoebius_free_prime_identity ℓ S hS primeDetectorCutoff w u hc hs v
  rw [hfilter] at hid
  have hpref := angular_cutoffMoebius_free_prime_prefactor_bound ℓ
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w u hc v
  change ‖∑ p ∈ S, _‖ ≤ _
  rw [hid,norm_mul]
  apply (mul_le_of_le_one_left (_root_.norm_nonneg _) hpref).trans
  simpa only [normTwist_eq_mellinPhase] using
    hbound T P a b w u hT hP hTP ha hab hb hw v (c*e) hv hnc hNv
      (mul_ne_zero (primary_ne_zero hc) he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimePowers
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial losses in log X are negligible on the actual long-prime
scale exp(sqrt(log X)). This includes logarithmic prime exclusions. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem long_prime_power_absorption {C D E : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∀ᶠ P : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ (Real.log P)^2 →
      C*T^E ≤ P/T^D := by
  have hs := ((isLittleO_log_rpow_rpow_atTop (2*(D+E))
    (by norm_num : (0:ℝ) < 1)).const_mul_left C).def zero_lt_one
  filter_upwards [hs,eventually_gt_atTop (1:ℝ)] with P hsmall hP T hT hTP
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hl : 0 < Real.log P := Real.log_pos hP
  have hbound : C*(Real.log P)^(2*(D+E)) ≤ P := by
    simpa only [Real.rpow_one,one_mul,Real.norm_of_nonneg (mul_nonneg hC
      (Real.rpow_nonneg hl.le _)),Real.norm_of_nonneg hP0.le] using hsmall
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT0 D)).mpr
  calc
    C*T^E*T^D = C*T^(D+E) := by rw [Real.rpow_add hT0]; ring
    _ ≤ C*((Real.log P)^2)^(D+E) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hT0.le hTP (add_nonneg hD hE)) hC
    _ = C*(Real.log P)^(2*(D+E)) := by
      rw [←Real.rpow_natCast_mul hl.le 2 (D+E)]
      norm_num
    _ ≤ P := hbound

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed power saving for the literal free prime, with the
polynomial norm-twist and excluded-prime costs already absorbed. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_moebius_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → |u| ≤ T^H →
      ∀ c v e : Eisenstein, primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ ((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_moebius_bound hEF ℓ hℓ hA (add_pos_of_pos_of_nonneg hD hH)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := (Real.log 2)⁻¹) (D := D) (E := E)
      (inv_nonneg.mpr hlog2.le) hD.le hE)
  refine ⟨2*K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw hu c v e hc hs hv hnc hNv he hNe
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  have hTH : 1 ≤ T^H := Real.one_le_rpow hT hH
  have hheight : 1+|u| ≤ 2*T^H := by linarith
  have hmain : K*P/T^(D+H)*(1+|u|) ≤ 2*K*P/T^D := by
    calc
      _ ≤ K*P/T^(D+H)*(2*T^H) :=
        mul_le_mul_of_nonneg_left hheight (by positivity)
      _ = 2*K*P/T^D := by
        rw [Real.rpow_add hT0]
        field_simp
  have herror : Real.log (norm (c*e))/Real.log 2 ≤ P/T^D := by
    calc
      _ ≤ T^E/Real.log 2 := (div_le_div_iff_of_pos_right hlog2).mpr hNe
      _ = (Real.log 2)⁻¹*T^E := by ring
      _ ≤ P/T^D := hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  apply (hbound T P a b w u hT ((le_max_left _ _).trans hP) hTP ha hab hb hw
    c v e hc hs hv hnc hNv he).trans
  calc
    _ ≤ 2*K*P/T^D+P/T^D := add_le_add hmain herror
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIntervalGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stopped crossing tests with one prime left free. A distinguished
prime enters by its actual norm; a selected-bin prime leaves every
surrogate prefix unchanged while its bin is fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- A fixed-order tie rule changes the lower norm interval at just the
single norm of the largest complementary prime. -/
lemma largestPrimePredicate_away_tie (code : Eisenstein → ℕ)
    (s : Finset Eisenstein) (p : Eisenstein) (hne : normNat p ≠ s.sup normNat) :
    largestPrimePredicate code s p ↔ s.sup normNat < normNat p := by
  constructor
  · intro h
    have hs : s.sup normNat ≤ normNat p := by
      apply Finset.sup_le
      intro q hq
      rcases h q hq with hlt | he
      · exact hlt.le
      · exact he.1.le
    exact lt_of_le_of_ne hs hne.symm
  · intro h q hq
    exact Or.inl ((Finset.le_sup (f := normNat) hq).trans_lt h)

lemma primeSurrogate_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) (ell : ℕ → ℝ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) :
    primeSurrogate (insert p s) b ell = primeSurrogate (insert q s) b ell := by
  simp only [primeSurrogate,Finset.prod_insert hp,Finset.prod_insert hq,hb]

lemma primeSurrogate_prefix_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) (ell : ℕ → ℝ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) (j : ℕ) :
    primeSurrogate (primeBinPrefix (insert p s) b j) b ell =
      primeSurrogate (primeBinPrefix (insert q s) b j) b ell := by
  by_cases hj : b p < j
  · have hqj : b q < j := by simpa only [←hb] using hj
    have hp' : p ∉ primeBinPrefix s b j := fun h => hp (Finset.mem_filter.mp h).1
    have hq' : q ∉ primeBinPrefix s b j := fun h => hq (Finset.mem_filter.mp h).1
    simp only [primeBinPrefix,Finset.filter_insert,hj,hqj,ite_true, if_true]
    exact primeSurrogate_insert_same_bin _ b ell hp' hq' hb
  · have hqj : ¬b q < j := by simpa only [←hb] using hj
    simp only [primeBinPrefix,Finset.filter_insert,hj,hqj,ite_false, if_false]

lemma primeBin_card_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) (j : ℕ) :
    (primeBin (insert p s) b j).card = (primeBin (insert q s) b j).card := by
  by_cases hj : b p = j
  · have hqj : b q = j := hb.symm.trans hj
    have hp' : p ∉ s.filter (fun r => b r = j) := fun h => hp (Finset.mem_filter.mp h).1
    have hq' : q ∉ s.filter (fun r => b r = j) := fun h => hq (Finset.mem_filter.mp h).1
    simp only [primeBin,Finset.filter_insert,hj,hqj,ite_true, if_true,
      Finset.card_insert_of_notMem hp',Finset.card_insert_of_notMem hq']
  · have hqj : ¬b q = j := fun h => hj (hb.trans h)
    simp only [primeBin,Finset.filter_insert,hj,hqj,ite_false, if_false]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeSelection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact selection of a largest prime, with a fixed injective tie code.
This is an unordered selection: inserting it into a finite sum introduces
no factor depending on the number of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeTieCode_injective : Function.Injective primeTieCode := by
  intro p q h
  have hi : Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p =
      Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q := Encodable.encode_injective h
  have hr := Function.rightInverse_invFun ofCoords_surjective
  calc
    p = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p).2 := (hr p).symm
    _ = ofCoords (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).1
      (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) q).2 := by rw [hi]
    _ = q := hr q

lemma largestPrime_unique {code : Eisenstein → ℕ} (hc : Function.Injective code)
    {s : Finset Eisenstein} {p q : Eisenstein} (hp : p ∈ s) (hq : q ∈ s)
    (hpl : largestPrimePredicate code s p) (hql : largestPrimePredicate code s q) : p = q := by
  rcases hpl q hq with hlt | he
  · rcases hql p hp with hlt' | he'
    · omega
    · omega
  · rcases hql p hp with hlt' | he'
    · omega
    · exact hc (le_antisymm he'.2 he.2)

lemma selectedLargestPrime_spec (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs ∈ s ∧
      largestPrimePredicate primeTieCode s (selectedLargestPrime s hs) :=
  Classical.choose_spec (exists_largestPrime primeTieCode s hs)

lemma selectedLargestPrime_norm (s : Finset Eisenstein) (hs : s.Nonempty) :
    normNat (selectedLargestPrime s hs) = s.sup normNat := by
  have hp := selectedLargestPrime_spec s hs
  apply le_antisymm (Finset.le_sup (f := normNat) hp.1)
  apply Finset.sup_le
  intro q hq
  rcases hp.2 q hq with hlt | he
  · exact hlt.le
  · exact he.1.le

lemma selectedLargestPrime_product_split (s : Finset Eisenstein) (hs : s.Nonempty) :
    selectedLargestPrime s hs*(∏ q ∈ s.erase (selectedLargestPrime s hs), q) =
      ∏ q ∈ s, q := by
  simpa only [mul_comm] using Finset.prod_erase_mul s (fun q => q)
    (selectedLargestPrime_spec s hs).1

/-- The actual largest prime of a squarefree primary element can be
removed once, leaving a primary squarefree factor coprime to it. -/
theorem primary_largest_prime_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) (hne : (primaryPrimeFactors n).Nonempty) :
    ∃ p c : Eisenstein, primaryPrime p ∧ primary c ∧ Squarefree c ∧
      ¬p ∣ c ∧ p*c = n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors c) p ∧
      normNat p = (primaryPrimeFactors n).sup normNat := by
  let p := selectedLargestPrime (primaryPrimeFactors n) hne
  let U := (primaryPrimeFactors n).erase p
  let c := ∏ q ∈ U, q
  have hp := selectedLargestPrime_spec (primaryPrimeFactors n) hne
  have hpP : primaryPrime p := (primaryPrimeFactor_spec hn hp.1).1
  have hU (q : Eisenstein) (hq : q ∈ U) : primaryPrime q :=
    (primaryPrimeFactor_spec hn (Finset.mem_of_mem_erase hq)).1
  have hc : primary c := primary_finset_prod U (fun q => q) (fun q hq => (hU q hq).1)
  have hf : primaryPrimeFactors c = U := primaryPrimeFactors_finset_prod U hU
  have hpc : ¬p ∣ c := by
    intro hd
    have hm := (primaryPrime_mem_factors_iff hc).mpr ⟨hpP,hd⟩
    rw [hf] at hm
    exact (Finset.mem_erase.mp hm).1 rfl
  refine ⟨p,c,hpP,hc,primaryPrime_product_squarefree U hU,hpc,?_,?_,?_⟩
  · exact (selectedLargestPrime_product_split (primaryPrimeFactors n) hne).trans
      (primaryPrimeFactors_prod hn hs)
  · rw [hf]
    exact fun q hq => hp.2 q (Finset.mem_of_mem_erase hq)
  · exact selectedLargestPrime_norm (primaryPrimeFactors n) hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeNormEndpoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint and largest-prime tie corrections. At most two primary
primes have a prescribed norm, so endpoint choices cost an absolute
constant in a bounded prime sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_eq_or_conjugate_of_norm_eq {p q : Eisenstein}
    (hp : primaryPrime p) (hq : primaryPrime q) (hn : norm p = norm q) :
    p = q ∨ p = conjugate q := by
  have hnr : (normNat p:ℝ) = normNat q := by simpa only [normNat_cast] using hn
  have hn' : normNat p = normNat q := by exact_mod_cast hnr
  have heq : p*conjugate p = q*conjugate q := by
    rw [←normNat_cast_eq_mul_conjugate,←normNat_cast_eq_mul_conjugate,hn']
  have hd : p ∣ q*conjugate q := heq ▸ dvd_mul_right p (conjugate p)
  rcases hp.2.dvd_or_dvd hd with hd | hd
  · exact Or.inl (primary_associated_eq hp.1 hq.1
      ((hp.2.dvd_prime_iff_associated hq.2).mp hd))
  · exact Or.inr (primary_associated_eq hp.1 (primaryPrime_conjugate hq).1
      ((hp.2.dvd_prime_iff_associated (primaryPrime_conjugate hq).2).mp hd))

theorem primaryPrime_norm_fiber_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (x : ℝ) :
    (S.filter (fun p => norm p = x)).card ≤ 2 := by
  let T := S.filter (fun p => norm p = x)
  by_cases hT : T.Nonempty
  · obtain ⟨q,hq⟩ := hT
    have hsub : T ⊆ {q,conjugate q} := by
      intro p hp
      have he := primaryPrime_eq_or_conjugate_of_norm_eq
        (hS p (Finset.mem_filter.mp hp).1) (hS q (Finset.mem_filter.mp hq).1)
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      simpa only [Finset.mem_insert,Finset.mem_singleton] using he
    apply (Finset.card_le_card hsub).trans
    calc
      ({q,conjugate q}:Finset Eisenstein).card ≤ ({conjugate q}:Finset Eisenstein).card+1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  · change T.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    norm_num

lemma primaryPrime_two_norm_card (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a b : ℝ) :
    (S.filter (fun p => norm p = a ∨ norm p = b)).card ≤ 4 := by
  have he : S.filter (fun p => norm p = a ∨ norm p = b) =
      S.filter (fun p => norm p = a) ∪ S.filter (fun p => norm p = b) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_union]
    tauto
  rw [he]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add (primaryPrime_norm_fiber_card S hS a)
      (primaryPrime_norm_fiber_card S hS b)).trans (by norm_num))

/-- This also covers an arbitrary fixed-order selection among equal-norm
largest primes. Away from the two boundary norms the predicates agree. -/
theorem prime_interval_endpoint_difference (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (P Q : Eisenstein → Prop) (a b : ℝ)
    (hPQ : ∀ p ∈ S, norm p ≠ a → norm p ≠ b → (P p ↔ Q p))
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S with P p, w p)-(∑ p ∈ S with Q p, w p)‖ ≤ 4*M := by
  let T := S.filter (fun p => norm p = a ∨ norm p = b)
  let f := fun p => (if P p then w p else 0)-(if Q p then w p else 0)
  have he : (∑ p ∈ S, f p) = ∑ p ∈ T, f p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hn : norm p ≠ a ∧ norm p ≠ b := by
      simpa only [T,Finset.mem_filter,hp,true_and,not_or] using hnot
    have he := hPQ p hp hn.1 hn.2
    by_cases h : P p
    · simp [f,h,he.mp h]
    · have hq : ¬Q p := fun hq => h (he.mpr hq)
      simp [f,h,hq]
  have hf (p : Eisenstein) (hp : p ∈ T) : ‖f p‖ ≤ M := by
    have hpS := (Finset.mem_filter.mp hp).1
    by_cases hP : P p <;> by_cases hQ : Q p <;>
      simp [f,hP,hQ,hM,hw p hpS]
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  change ‖∑ p ∈ S, f p‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, M := Finset.sum_le_sum hf
    _ = (T.card:ℝ)*M := by simp
    _ ≤ 4*M := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (primaryPrime_two_norm_card S hS a b)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCancellation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual largest-prime restriction costs only the two equal-norm
endpoints. The cancellation is still the published prime input, not a
sequence-condition hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrime_endpoint_difference (code : Eisenstein → ℕ)
    (C S : Finset Eisenstein) (hS : ∀ p ∈ S, primaryPrime p)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with largestPrimePredicate code C p, f p)-
      (∑ p ∈ S with ((C.sup normNat:ℕ):ℝ) < norm p, f p)‖ ≤ 4*M := by
  apply prime_interval_endpoint_difference S hS _ _
    ((C.sup normNat:ℕ):ℝ) ((C.sup normNat:ℕ):ℝ) _ f hM hf
  intro p hp hn _
  have hne : normNat p ≠ C.sup normNat := by
    intro h
    apply hn
    rw [←normNat_cast p,h]
  simpa only [←normNat_cast p,Nat.cast_lt] using
    largestPrimePredicate_away_tie code C p hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeContext
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-prime cancellation with the full fixed complementary prime
set. The selected-bin role compares against the primes of both other
factors, rather than just those of its own Möbius complement. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_context_moebius_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T P a b w u : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 →
      P ≤ a → a ≤ b → b ≤ 2*P → 0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff b).filter (fun p => a < norm p)).filter
          (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*P/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_moebius_saving hEF ℓ hℓ hA hD hH hE
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := 0)
      (by norm_num) hD.le (by norm_num))
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T P a b w u hT hP hTP ha hab hb hw hu c v e C hc hs hv hnc hNv he hNe
  have hP0 : 0 < P := zero_lt_one.trans (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := ((primeCutoff b).filter (fun p => a < norm p)).filter
    (fun p => IsCoprime p (c*e))
  let f := fun p : Eisenstein => cutoffMoebius primeDetectorCutoff w (p*c)*
    normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v
  let m : ℝ := ((C.sup normNat:ℕ):ℝ)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,norm_normTwist,mul_one]
    exact (mul_le_mul (cutoffMoebius_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w (p*c))
      (angularCubicSymbol_norm_le_one ℓ (primary_mul (hS p hp).1 hc) v)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hend := largestPrime_endpoint_difference primeTieCode C S hS
    f zero_le_one hf
  have hinterval :
      (∑ p ∈ S with m < norm p, f p) =
      ∑ p ∈ ((primeCutoff b).filter (fun p => max a m < norm p)).filter
        (fun p => IsCoprime p (c*e)), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with m < norm p, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a m ≤ b
    · exact hbound T P (max a m) b w u hT ((le_max_left _ _).trans hP) hTP
        (ha.trans (le_max_left _ _)) hm hb hw hu c v e hc hs hv hnc hNv he hNe
    · have hempty : ((primeCutoff b).filter (fun p => max a m < norm p)).filter
          (fun p => IsCoprime p (c*e)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
        exact hm (hl.le.trans (mem_primeCutoff.mp hp).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : (4:ℝ) ≤ P/T^D := by
    simpa only [Real.rpow_zero,mul_one] using
      hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  change ‖∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with m < norm p, f p‖+
        ‖(∑ p ∈ S with largestPrimePredicate primeTieCode C p, f p)-
          (∑ p ∈ S with m < norm p, f p)‖ := by
      exact norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4 := add_le_add hsum (by simpa only [mul_one] using hend)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma geometricPrimeBin_index {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p < geometricBinCount ρ B := by
  have hr := Real.log_pos hρ
  have hpn : 0 < norm p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (primaryPrime_norm_ge_two hp)
  have hpρ : ρ ≤ norm p := hρ₂.trans (primaryPrime_norm_ge_two hp)
  have hl : 1 ≤ Real.log (norm p)/Real.log ρ := by
    apply (le_div_iff₀ hr).mpr
    rw [one_mul]
    exact Real.log_le_log (zero_lt_one.trans hρ) hpρ
  have hk : 1 ≤ ⌊Real.log (norm p)/Real.log ρ⌋₊ := (Nat.one_le_floor_iff _).mpr hl
  have hkM : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ B := by
    exact (Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log hpn hpB) hr.le)).trans
        (Nat.floor_le_ceil _)
  unfold geometricPrimeBin
  omega

lemma geometricBinLower_gt_one {ρ B : ℝ} (hρ : 1 < ρ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) : 1 < geometricBinLower ρ B j := by
  exact one_lt_pow₀ hρ (by omega)

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm intervals for the concrete bins used by the stopping
construction, including their bounded endpoint convention change. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometricPrimeBin_eq_iff {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricPrimeBin ρ B p = j ↔
      geometricBinLower ρ B j ≤ norm p ∧ norm p < ρ*geometricBinLower ρ B j := by
  constructor
  · intro he
    simpa only [he] using geometricPrimeBin_cell hρ hρ₂ hp hpB
  · intro hcell
    have hr : 0 < Real.log ρ := Real.log_pos hρ
    have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
    have hn : 0 ≤ Real.log (norm p)/Real.log ρ :=
      div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
    have hlo : ((geometricBinCount ρ B-j:ℕ):ℝ) ≤ Real.log (norm p)/Real.log ρ := by
      apply (le_div_iff₀ hr).mpr
      exact (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mp hcell.1
    have hhi : Real.log (norm p)/Real.log ρ < ((geometricBinCount ρ B-j:ℕ):ℝ)+1 := by
      apply (div_lt_iff₀ hr).mpr
      have h : norm p < ρ^(geometricBinCount ρ B-j+1) := by
        simpa only [pow_succ',geometricBinLower] using hcell.2
      simpa only [Nat.cast_add,Nat.cast_one] using
        (Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)).mp h
    have hf : ⌊Real.log (norm p)/Real.log ρ⌋₊ = geometricBinCount ρ B-j :=
      (Nat.floor_eq_iff hn).mpr ⟨hlo,hhi⟩
    unfold geometricPrimeBin
    rw [hf]
    omega

lemma geometricPrimeBin_away_endpoints {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) {p : Eisenstein}
    (hp : primaryPrime p) (hpB : norm p ≤ B)
    (hlo : norm p ≠ geometricBinLower ρ B j)
    (hhi : norm p ≠ ρ*geometricBinLower ρ B j) :
    (geometricPrimeBin ρ B p = j) ↔
      geometricBinLower ρ B j < norm p ∧ norm p ≤ ρ*geometricBinLower ρ B j := by
  rw [geometricPrimeBin_eq_iff hρ hρ₂ hj hp hpB]
  constructor
  · rintro ⟨hl,hu⟩
    exact ⟨lt_of_le_of_ne hl hlo.symm,hu.le⟩
  · rintro ⟨hl,hu⟩
    exact ⟨hl.le,lt_of_le_of_ne hu hhi⟩

/-- Replacing a half-open bin by the open-closed interval used by prime
partial summation changes only the two endpoint norms. -/
theorem geometricPrimeBin_endpoint_difference {ρ B : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p ∧ norm p ≤ B)
    (f : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ p ∈ S, ‖f p‖ ≤ M) :
    ‖(∑ p ∈ S with geometricPrimeBin ρ B p = j, f p)-
      (∑ p ∈ S with geometricBinLower ρ B j < norm p ∧
        norm p ≤ ρ*geometricBinLower ρ B j, f p)‖ ≤ 4*M := by
  convert prime_interval_endpoint_difference S (fun p hp => (hS p hp).1)
    (fun p => geometricPrimeBin ρ B p = j)
    (fun p => geometricBinLower ρ B j < norm p ∧ norm p ≤ ρ*geometricBinLower ρ B j)
    (geometricBinLower ρ B j) (ρ*geometricBinLower ρ B j)
    (fun p hp hlo hhi => geometricPrimeBin_away_endpoints hρ hρ₂ hj
      (hS p hp).1 (hS p hp).2 hlo hhi) f hM hf using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  all_goals
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter]
    · intro p hp
      rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLongPrimeBox
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual geometric selected-prime bin inherits the published prime
saving. Its endpoint convention and largest-prime tie rule are retained. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_prime_geometric_interval_moebius_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u a b : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ‖∑ p ∈ (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_context_moebius_saving hEF ℓ hℓ hA hD hH hE
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    (long_prime_power_absorption (C := 4) (D := D) (E := 0)
      (by norm_num) hD.le (by norm_num))
  refine ⟨K+1,max P₀ P₁,by positivity,lt_of_lt_of_le hP₀ (le_max_left _ _),?_⟩
  intro T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
  let P := geometricBinLower ρ B j
  have hP0 : 0 < P := zero_lt_one.trans
    (hP₀.trans_le ((le_max_left _ _).trans hP))
  let S := (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
    (fun p => largestPrimePredicate primeTieCode C p)
  let f := fun p : Eisenstein => cutoffMoebius primeDetectorCutoff w (p*c)*
    normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p ∧ norm p ≤ B :=
    mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  have hf (p : Eisenstein) (hp : p ∈ S) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [norm_mul,norm_mul,norm_normTwist,mul_one]
    exact (mul_le_mul (cutoffMoebius_norm_le_one
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩) w (p*c))
      (angularCubicSymbol_norm_le_one ℓ (primary_mul (hS p hp).1.1 hc) v)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hend := geometricPrimeBin_endpoint_difference hρ hρ₂ hj S hS f zero_le_one hf
  have hinterval : (∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p) =
      ∑ p ∈ (((primeCutoff (min (min B b) (ρ*P))).filter (fun p => max a P < norm p)).filter
        (fun p => IsCoprime p (c*e))).filter
        (fun p => largestPrimePredicate primeTieCode C p), f p := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [S,Finset.mem_filter,mem_primeCutoff,le_min_iff,max_lt_iff]
    tauto
  have hsum : ‖∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p‖ ≤ K*P/T^D := by
    rw [hinterval]
    by_cases hm : max a P ≤ min (min B b) (ρ*P)
    · exact hbound T P (max a P) (min (min B b) (ρ*P)) w u hT ((le_max_left _ _).trans hP)
        hTP (le_max_right _ _) hm ((min_le_right _ _).trans (mul_le_mul_of_nonneg_right hρ₂ hP0.le))
        hw hu c v e C hc hs hv hnc hNv he hNe
    · have hempty : (((primeCutoff (min (min B b) (ρ*P))).filter (fun p => max a P < norm p)).filter
          (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hpc := Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact hm (hpc.2.le.trans (mem_primeCutoff.mp hpc.1).2)
      rw [hempty,Finset.sum_empty,norm_zero]
      positivity
  have hfour : (4:ℝ) ≤ P/T^D := by
    simpa only [Real.rpow_zero,mul_one] using
      hP₁ P ((le_max_right _ _).trans hP) T hT hTP
  have hset : (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
      (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j) =
      S.filter (fun p => geometricPrimeBin ρ B p = j) := by
    ext p
    simp only [S,Finset.mem_filter]
    tauto
  rw [hset]
  change ‖∑ p ∈ S with geometricPrimeBin ρ B p = j, f p‖ ≤ _
  calc
    _ ≤ ‖∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p‖+
        ‖(∑ p ∈ S with geometricPrimeBin ρ B p = j, f p)-
          (∑ p ∈ S with P < norm p ∧ norm p ≤ ρ*P, f p)‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ K*P/T^D+4 := add_le_add hsum (by simpa only [mul_one] using hend)
    _ ≤ K*P/T^D+P/T^D := add_le_add le_rfl hfour
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute, uncollected complementary factorization mass used
after a free prime is cancelled. No cancellation inside beta is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rough_pairAbsolute_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (v f : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    (hf : ∀ d ∈ D, ‖f d‖ ≤ 1) {b : Eisenstein}
    (hb : primary b) (hs : Squarefree b) {w : ℝ} (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) : pairAbsolute R D v f b ≤ (2^k:ℕ)*M := by
  calc
    _ ≤ ∑ _p ∈ primaryPairFiber R D b, M := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact (mul_le_mul_of_nonneg_left (hf p.2 hmem.2) (_root_.norm_nonneg _)).trans
        ((mul_one _).le.trans (hv p.1 hmem.1))
    _ = ((primaryPairFiber R D b).card:ℝ)*M := by simp
    _ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le R D hR b)) hM
    _ ≤ (2^k:ℕ)*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedComplementMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary pair mass after a selected-bin prime is removed.
The rough distinguished factor has only a bounded number of choices for
each squarefree product, so the total mass is linear in its norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_complement_mass (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    (v : Eisenstein → ℂ) {M Y w : ℝ} (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (hw : 1 ≤ w)
    (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : Y < w^k) :
    (∑ t ∈ (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y),
      ‖v t.1‖) ≤ 18*Y*((2^k:ℕ)*M) := by
  let U := (R ×ˢ D).filter (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ Y)
  let B := (primaryElementBall Y).filter Squarefree
  have hmap (t : Eisenstein × Eisenstein) (ht : t ∈ U) : t.1*t.2 ∈ B := by
    obtain ⟨ht,hpred⟩ := Finset.mem_filter.mp ht
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
      ⟨primary_mul (hR _ hr) (hD _ hd),hpred.2⟩,hpred.1⟩
  have hfiber (b : Eisenstein) (hb : b ∈ B) :
      (∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖) ≤ (2^k:ℕ)*M := by
    obtain ⟨hb,hs⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb,hbY⟩ := mem_primaryElementBall.mp hb
    have hsub : U.filter (fun t => t.1*t.2 = b) ⊆ primaryPairFiber R D b := by
      intro t ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,he⟩
    calc
      _ ≤ ∑ t ∈ primaryPairFiber R D b, ‖v t.1‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => _root_.norm_nonneg _)
      _ = pairAbsolute R D v (fun _ => 1) b := by
        simp only [pairAbsolute,norm_one,mul_one]
      _ ≤ _ := rough_pairAbsolute_bound R D hR v (fun _ => 1) hM hv
        (fun _ _ => by simp) hb hs hw hrough (hbY.trans_lt hsize)
  calc
    _ = ∑ b ∈ B, ∑ t ∈ U with t.1*t.2 = b, ‖v t.1‖ :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ _b ∈ B, (2^k:ℕ)*M := Finset.sum_le_sum hfiber
    _ = (B.card:ℝ)*((2^k:ℕ)*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (primaryElementBall_card_le hY))
      (mul_nonneg (Nat.cast_nonneg _) hM)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete selected-side stopping predicates. Replacing one prime
within its fixed bin leaves every selected-bin surrogate test unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    primaryPrimeFactors (p*c) = insert p (primaryPrimeFactors c) := by
  have hpnot : p ∉ primaryPrimeFactors c :=
    fun h => hpc (primaryPrimeFactor_spec hc h).2
  have hprime : ∀ q ∈ insert p (primaryPrimeFactors c), primaryPrime q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (primaryPrimeFactor_spec hc hq).1
  have h := primaryPrimeFactors_finset_prod (insert p (primaryPrimeFactors c)) hprime
  simpa only [Finset.prod_insert hpnot,primaryPrimeFactors_prod hc hs] using h

lemma stoppingPrimeSetTest_insert_same_bin (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {p q : Eisenstein} (hp : p ∉ s) (hq : q ∉ s) (hbin : bin p = bin q) :
    stoppingPrimeSetTest (insert p s) bin ell j k Z r ↔
      stoppingPrimeSetTest (insert q s) bin ell j k Z r := by
  have hno : (∀ t ∈ insert p s, bin t ≤ j) ↔ (∀ t ∈ insert q s, bin t ≤ j) := by
    simp only [Finset.forall_mem_insert,hbin]
  simp only [stoppingPrimeSetTest,hno,
    primeSurrogate_insert_same_bin s bin ell hp hq hbin,
    primeBin_card_insert_same_bin s bin hp hq hbin j]

theorem stoppingSideTest_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    stoppingSideTest bin ell j k Z r (p*c) ↔
      stoppingSideTest bin ell j k Z r (q*c) := by
  unfold stoppingSideTest
  rw [primaryPrimeFactors_prime_mul hp hc hs hpc,primaryPrimeFactors_prime_mul hq hc hs hqc]
  exact stoppingPrimeSetTest_insert_same_bin _ bin ell j k Z r
    (fun h => hpc (primaryPrimeFactor_spec hc h).2)
    (fun h => hqc (primaryPrimeFactor_spec hc h).2) hbin

theorem failedStage_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (h : ℕ) (Q : ℝ) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    (norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (p*c)) bin h) bin ell < Q) ↔
      norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors (q*c)) bin h) bin ell < Q := by
  rw [primaryPrimeFactors_prime_mul hp hc hs hpc,primaryPrimeFactors_prime_mul hq hc hs hqc,
    primeSurrogate_prefix_insert_same_bin _ bin ell
      (fun hp => hpc (primaryPrimeFactor_spec hc hp).2)
      (fun hq => hqc (primaryPrimeFactor_spec hc hq).2) hbin h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimePredicate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both actual stopping branches, including failure of the earlier
crossing test. Fixing the selected prime's bin fixes all these tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSideTest_free_prime_same_bin (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein)
    {c p q : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (hp : primaryPrime p) (hq : primaryPrime q) (hpc : ¬p ∣ c) (hqc : ¬q ∣ c)
    (hbin : bin p = bin q) :
    stoppedSideTest bin ell j k h Z Q early r (p*c) ↔
      stoppedSideTest bin ell j k h Z Q early r (q*c) := by
  exact and_congr
    (stoppingSideTest_free_prime_same_bin bin ell j k Z r hc hs hp hq hpc hqc hbin)
    (or_congr Iff.rfl
      (failedStage_free_prime_same_bin bin ell h Q r hc hs hp hq hpc hqc hbin))

theorem sum_stoppedSide_same_bin (S : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r : Eisenstein) {c p₀ : Eisenstein} (hc : primary c) (hsc : Squarefree c)
    (hp₀ : p₀ ∈ S) (hS : ∀ p ∈ S, primaryPrime p)
    (hcop : ∀ p ∈ S, ¬p ∣ c) (hbin : ∀ p ∈ S, bin p = bin p₀)
    (F : Eisenstein → ℂ) :
    (∑ p ∈ S with stoppedSideTest bin ell j k h Z Q early r (p*c), F p) =
      if stoppedSideTest bin ell j k h Z Q early r (p₀*c) then ∑ p ∈ S, F p else 0 := by
  rw [Finset.sum_filter]
  by_cases ht : stoppedSideTest bin ell j k h Z Q early r (p₀*c)
  · rw [ite_eq_left ht]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_left ((stoppedSideTest_free_prime_same_bin bin ell j k h Z Q early r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mpr ht)]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro p hp
    apply ite_eq_right
    intro h'
    exact ht ((stoppedSideTest_free_prime_same_bin bin ell j k h Z Q early r hc hsc
      (hS p hp) (hS p₀ hp₀) (hcop p hp) (hcop p₀ hp₀) (hbin p hp)).mp h')

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-bin free-prime row with its actual full product,
complementary exclusion and both stopping tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSelectedPrimeSet_primary (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c e : Eisenstein) {p : Eisenstein}
    (hp : p ∈ stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e) : primaryPrime p := by
  exact (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1).1).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical functions for the exact largest-prime change of variables.
They allow predicates on the original product to be rewritten after the
finite reindexing, without a choice-dependent coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_spec {n : Eisenstein} (h : (primaryPrimeFactors n).Nonempty) :
    largestPrimeChoice n ∈ primaryPrimeFactors n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors n) (largestPrimeChoice n) := by
  simpa only [largestPrimeChoice,dite_eq_left h] using selectedLargestPrime_spec (primaryPrimeFactors n) h

lemma largestPrimeChoice_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c)
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (p*c) = p ∧ largestPrimeRemainder (p*c) = c := by
  have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
  have hp_mem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
  have hne : (primaryPrimeFactors (p*c)).Nonempty := ⟨p,hp_mem⟩
  have hlarge : largestPrimePredicate primeTieCode (primaryPrimeFactors (p*c)) p := by
    rw [hf]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Or.inr ⟨rfl,le_rfl⟩
    · exact hl q hq
  have hchoice : largestPrimeChoice (p*c) = p :=
    largestPrime_unique primeTieCode_injective (largestPrimeChoice_spec hne).1 hp_mem
      (largestPrimeChoice_spec hne).2 hlarge
  refine ⟨hchoice,?_⟩
  have hnot : p ∉ primaryPrimeFactors c := fun h => hpc (primaryPrimeFactor_spec hc h).2
  rw [largestPrimeRemainder,hchoice,hf,Finset.erase_insert hnot,primaryPrimeFactors_prod hc hs]

lemma largestPrimeChoice_mul_eq_iff {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    largestPrimeChoice (p*c) = p ↔ largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  constructor
  · intro he q hq
    have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
    have hmem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
    have hl := (largestPrimeChoice_spec (show (primaryPrimeFactors (p*c)).Nonempty from ⟨p,hmem⟩)).2
    rw [he] at hl
    exact hl q (by rw [hf]; exact Finset.mem_insert_of_mem hq)
  · exact fun h => (largestPrimeChoice_prime_mul hp hc hs hpc h).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The largest prime of a squarefree stopped product occurs on exactly
one side. This is the exact split into distinguished and selected-bin
roles before reindexing the free prime. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_factor_unique_side {p r d : Eisenstein} (hp : Prime p)
    (hs : Squarefree (r*d)) (hd : p ∣ r*d) :
    (p ∣ r ∧ ¬p ∣ d) ∨ (p ∣ d ∧ ¬p ∣ r) := by
  have hcop : IsCoprime r d :=
    isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  rcases hp.dvd_or_dvd hd with hr | hd
  · exact Or.inl ⟨hr,fun hd => hp.not_isUnit (hcop.isUnit_of_dvd' hr hd)⟩
  · exact Or.inr ⟨hd,fun hr => hp.not_isUnit (hcop.isUnit_of_dvd' hr hd)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the selected-bin largest-prime role. The
largest prime of the full product is used throughout; its occurrence in
the selected divisor is proved equivalent to the free-prime row test. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_mul_union {r d : Eisenstein} (hr : primary r) (hd : primary d) :
    primaryPrimeFactors (r*d) = primaryPrimeFactors r ∪ primaryPrimeFactors d := by
  ext p
  rw [primaryPrime_mem_factors_iff (primary_mul hr hd),Finset.mem_union,
    primaryPrime_mem_factors_iff hr,primaryPrime_mem_factors_iff hd]
  constructor
  · rintro ⟨hp,hpd⟩
    rcases hp.2.dvd_or_dvd hpd with hpr | hpd
    · exact Or.inl ⟨hp,hpr⟩
    · exact Or.inr ⟨hp,hpd⟩
  · rintro (⟨hp,hpr⟩ | ⟨hp,hpd⟩)
    · exact ⟨hp,dvd_mul_of_dvd_left hpr d⟩
    · exact ⟨hp,dvd_mul_of_dvd_right hpd r⟩

lemma largestPrimeChoice_dvd_right_iff {r d : Eisenstein}
    (hr : primary r) (hd : primary d) (hne : (primaryPrimeFactors d).Nonempty) :
    largestPrimeChoice (r*d) ∣ d ↔ largestPrimeChoice (r*d) = largestPrimeChoice d := by
  have hsub : primaryPrimeFactors d ⊆ primaryPrimeFactors (r*d) := by
    rw [primaryPrimeFactors_mul_union hr hd]
    exact Finset.subset_union_right
  have hne' : (primaryPrimeFactors (r*d)).Nonempty := hne.mono hsub
  have hfull := largestPrimeChoice_spec hne'
  have hright := largestPrimeChoice_spec hne
  have hp := (primaryPrimeFactor_spec (primary_mul hr hd) hfull.1).1
  constructor
  · intro hdiv
    have hm : largestPrimeChoice (r*d) ∈ primaryPrimeFactors d :=
      (primaryPrime_mem_factors_iff hd).mpr ⟨hp,hdiv⟩
    exact largestPrime_unique primeTieCode_injective hm hright.1
      (fun q hq => hfull.2 q (hsub hq)) hright.2
  · intro he
    rw [he]
    exact (primaryPrimeFactor_spec hd hright.1).2

lemma selected_largest_free_prime_iff {r p c : Eisenstein}
    (hr : primary r) (hp : primaryPrime p) (hc : primary c)
    (hs : Squarefree (r*(p*c)))
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (r*(p*c)) ∣ p*c ↔
      largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p := by
  have hsd : Squarefree (p*c) := (squarefree_mul_iff.mp hs).2.2
  have hsc : Squarefree c := (squarefree_mul_iff.mp hsd).2.2
  have hpc : ¬p ∣ c := by
    have hcop : IsCoprime p c := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hsd).1
    exact fun h => hp.2.not_isUnit (hcop.isUnit_of_dvd h)
  have he : r*(p*c) = p*(r*c) := by ring
  have hs' : Squarefree (p*(r*c)) := he ▸ hs
  have hsrc : Squarefree (r*c) := (squarefree_mul_iff.mp hs').2.2
  have hprc : ¬p ∣ r*c := by
    have hcop : IsCoprime p (r*c) :=
      isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs').1
    exact fun h => hp.2.not_isUnit (hcop.isUnit_of_dvd h)
  have hchoice := (largestPrimeChoice_prime_mul hp hc hsc hpc hl).1
  have hne : (primaryPrimeFactors (p*c)).Nonempty := by
    rw [primaryPrimeFactors_prime_mul hp hc hsc hpc]
    exact Finset.insert_nonempty _ _
  rw [largestPrimeChoice_dvd_right_iff hr (primary_mul hp.1 hc) hne,hchoice,he]
  exact largestPrimeChoice_mul_eq_iff hp (primary_mul hr hc) hsrc hprc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SelectedPrimeGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic after removing the selected largest prime. These
identities retain the original squarefreeness, exclusion and norm range. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_decomposition {d : Eisenstein} (hd : primary d)
    (hs : Squarefree d) (hne : (primaryPrimeFactors d).Nonempty) :
    primaryPrime (largestPrimeChoice d) ∧ primary (largestPrimeRemainder d) ∧
      Squarefree (largestPrimeRemainder d) ∧
      ¬largestPrimeChoice d ∣ largestPrimeRemainder d ∧
      largestPrimeChoice d*largestPrimeRemainder d = d ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors (largestPrimeRemainder d))
        (largestPrimeChoice d) := by
  obtain ⟨p,c,hp,hc,hsc,hpc,he,hl,_⟩ := primary_largest_prime_split hd hs hne
  have hcan := largestPrimeChoice_prime_mul hp hc hsc hpc hl
  rw [he] at hcan
  rw [hcan.1,hcan.2]
  exact ⟨hp,hc,hsc,hpc,he,hl⟩

lemma selectedPrime_product_conditions (r p c e : Eisenstein) (hp : primaryPrime p) :
    (Squarefree (r*(p*c)) ∧ IsCoprime (r*(p*c)) e) ↔
      Squarefree (r*c) ∧ IsCoprime (r*c) e ∧ IsCoprime p (c*(r*e)) := by
  have he : r*(p*c) = p*(r*c) := by ring
  rw [he,squarefree_mul_iff,IsCoprime.mul_left_iff]
  constructor
  · rintro ⟨⟨hpc,_,hsrc⟩,hpe,hrce⟩
    have hpc' : IsCoprime p (r*c) := isRelPrime_iff_isCoprime.mp hpc
    refine ⟨hsrc,hrce,?_⟩
    exact hpc'.of_mul_right_right.mul_right (hpc'.of_mul_right_left.mul_right hpe)
  · rintro ⟨hsrc,hrce,hpcre⟩
    have hpc : IsCoprime p (r*c) :=
      hpcre.of_mul_right_right.of_mul_right_left.mul_right hpcre.of_mul_right_left
    exact ⟨⟨hpc.isRelPrime,hp.2.irreducible.squarefree,hsrc⟩,
      hpcre.of_mul_right_right.of_mul_right_right,hrce⟩

lemma selectedPrime_norm_interval {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (p : Eisenstein) (a b : ℝ) :
    (a < norm (r*(p*c)) ∧ norm (r*(p*c)) ≤ b) ↔
      a/norm (r*c) < norm p ∧ norm p ≤ b/norm (r*c) := by
  have hn : 0 < norm (r*c) := norm_pos_of_ne_zero (mul_ne_zero hr hc)
  have he : norm (r*(p*c)) = norm p*norm (r*c) := by
    rw [norm_mul_eq,norm_mul_eq,norm_mul_eq]
    ring
  rw [he]
  exact and_congr (div_lt_iff₀ hn).symm (le_div_iff₀ hn).symm

lemma largestPrimePredicate_complement {r c p : Eisenstein}
    (hr : primary r) (hc : primary c)
    (h : largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p) :
    largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  rw [primaryPrimeFactors_mul_union hr hc] at h
  exact fun q hq => h q (Finset.mem_union_right _ hq)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedReindex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selected-divisor sum is exactly the finite collection
of free-prime rows. Its squarefree support, global largest-prime choice,
output interval, exclusion and stopping predicates are all retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma selectedStopped_forward (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {r e d : Eisenstein} (hr : primary r)
    (hd : d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e) :
    (largestPrimeRemainder d,largestPrimeChoice d) ∈
      selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e := by
  obtain ⟨hd,hs,hne,hcop,hint,hrole,hbin,hstop⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd,hdB⟩ := mem_primaryElementBall.mp hd
  obtain ⟨hp,hc,hsc,hpc,he,hl⟩ := largestPrimeChoice_decomposition hd
    (squarefree_mul_iff.mp hs).2.2 hne
  have hfull : largestPrimeChoice (r*d) = largestPrimeChoice d :=
    (largestPrimeChoice_dvd_right_iff hr hd hne).mp hrole
  have hpB : norm (largestPrimeChoice d) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero hd) ⟨largestPrimeRemainder d,he.symm⟩).trans hdB
  have hcB : norm (largestPrimeRemainder d) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero hd)
      ⟨largestPrimeChoice d,by rw [mul_comm,he]⟩).trans hdB
  have hs' : Squarefree (r*(largestPrimeChoice d*largestPrimeRemainder d)) := by rw [he]; exact hs
  have hcop' : IsCoprime (r*(largestPrimeChoice d*largestPrimeRemainder d)) e := by
    rw [he]; exact hcop
  obtain ⟨hsrc,hrce,hpcre⟩ := (selectedPrime_product_conditions r _ _ e hp).mp ⟨hs',hcop'⟩
  have hlarge := (selected_largest_free_prime_iff hr hp hc hs' hl).mp (by rw [he]; exact hrole)
  have hinterval := (selectedPrime_norm_interval (primary_ne_zero hr) (primary_ne_zero hc)
    (largestPrimeChoice d) a b).mp (by rw [he]; exact hint)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨mem_primaryElementBall.mpr ⟨hc,hcB⟩,
    mem_primeCutoff.mpr ⟨hp,hpB⟩⟩,hsrc,hrce,?_⟩
  unfold stoppedSelectedPrimeSet
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_primeCutoff.mpr ⟨hp,hpB⟩,hinterval⟩,hpcre⟩,
      hlarge,?_⟩,?_⟩
  · simpa only [hfull] using hbin
  · simpa only [he] using hstop

lemma selectedStopped_backward (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {r e : Eisenstein} (hr : primary r) (hbB : b ≤ B) {t : Eisenstein × Eisenstein}
    (ht : t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e) :
    t.2*t.1 ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e ∧
      (largestPrimeRemainder (t.2*t.1),largestPrimeChoice (t.2*t.1)) = t := by
  obtain ⟨ht,hsrc,hrce,hrow⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc,hp⟩ := Finset.mem_product.mp ht
  obtain ⟨hc,_⟩ := mem_primaryElementBall.mp hc
  obtain ⟨hp,hpB⟩ := mem_primeCutoff.mp hp
  obtain ⟨hrow,hstop⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hrow,hlarge,hbin⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hrow,hpc⟩ := Finset.mem_filter.mp hrow
  obtain ⟨_,hint⟩ := Finset.mem_filter.mp hrow
  have hsfull := (selectedPrime_product_conditions r t.2 t.1 e hp).mpr ⟨hsrc,hrce,hpc⟩
  have hsc : Squarefree t.1 := (squarefree_mul_iff.mp hsrc).2.2
  have hpc' : ¬t.2 ∣ t.1 := fun hh => hp.2.not_isUnit (hpc.of_mul_right_left.isUnit_of_dvd hh)
  have hl := largestPrimePredicate_complement hr hc hlarge
  have hcan := largestPrimeChoice_prime_mul hp hc hsc hpc' hl
  have hne : (primaryPrimeFactors (t.2*t.1)).Nonempty := by
    rw [primaryPrimeFactors_prime_mul hp hc hsc hpc']
    exact Finset.insert_nonempty _ _
  have hrole := (selected_largest_free_prime_iff hr hp hc hsfull.1 hl).mpr hlarge
  have hfull : largestPrimeChoice (r*(t.2*t.1)) = t.2 :=
    ((largestPrimeChoice_dvd_right_iff hr (primary_mul hp.1 hc) hne).mp hrole).trans hcan.1
  have hint' := (selectedPrime_norm_interval (primary_ne_zero hr) (primary_ne_zero hc)
    t.2 a b).mpr hint
  have hdB : norm (t.2*t.1) ≤ B :=
    (norm_le_of_dvd_nonzero (primary_ne_zero (primary_mul hr (primary_mul hp.1 hc)))
      ⟨r,by ring⟩).trans (hint'.2.trans hbB)
  refine ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨primary_mul hp.1 hc,hdB⟩,
    hsfull.1,hne,hsfull.2,hint',hrole,?_,hstop⟩,?_⟩
  · simpa only [hfull] using hbin
  · exact Prod.ext hcan.2 hcan.1

/-- Every original selected-divisor term occurs exactly once. -/
theorem selectedStopped_sum_reindex (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r e : Eisenstein) (hr : primary r) (hbB : b ≤ B)
    (F : Eisenstein → ℂ) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e, F d) =
      ∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e, F (t.2*t.1) := by
  apply Finset.sum_bij (fun d _ => (largestPrimeRemainder d,largestPrimeChoice d))
  · intro d hd
    exact selectedStopped_forward B ρ a b j j₀ k h Z Q early hr hd
  · intro d hd d' hd' heq
    have hprop := (Finset.mem_filter.mp hd).2
    have hprop' := (Finset.mem_filter.mp hd').2
    have hcan := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1
      (squarefree_mul_iff.mp hprop.1).2.2 hprop.2.1
    have hcan' := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd').1).1
      (squarefree_mul_iff.mp hprop'.1).2.2 hprop'.2.1
    have hm := congrArg (fun t : Eisenstein × Eisenstein => t.2*t.1) heq
    exact hcan.2.2.2.2.1.symm.trans (hm.trans hcan'.2.2.2.2.1)
  · intro t ht
    exact ⟨t.2*t.1,(selectedStopped_backward B ρ a b j j₀ k h Z Q early hr hbB ht).1,
      (selectedStopped_backward B ρ a b j j₀ k h Z Q early hr hbB ht).2⟩
  · intro d hd
    have hp := (Finset.mem_filter.mp hd).2
    have hcan := largestPrimeChoice_decomposition (mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1
      (squarefree_mul_iff.mp hp.1).2.2 hp.2.1
    exact congrArg F hcan.2.2.2.2.1.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the selected-bin free-prime rows, and the
complementary norm cutoff forced by the lower endpoint of the prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSelectedPrimeSet_subset (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r c e : Eisenstein) :
    stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e ⊆ primeCutoff B := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp hp).1).1).1).1

lemma selectedStopped_complement_bound {B ρ a b : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c e p : Eisenstein} (hr : primary r) (hc : primary c)
    (hp : p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
      j j₀ k h Z Q early r c e) :
    norm (r*c) ≤ b/geometricBinLower ρ B j := by
  have hpP := stoppedSelectedPrimeSet_primary B ρ _ _ j j₀ k h Z Q early r c e hp
  have hpB := (mem_primeCutoff.mp (stoppedSelectedPrimeSet_subset B ρ _ _ j j₀ k h
    Z Q early r c e hp)).2
  have hrow := (Finset.mem_filter.mp hp).1
  have hbin := (Finset.mem_filter.mp hrow).2.2
  have hint := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hrow).1).1).2
  have hnorm := (geometricPrimeBin_eq_iff hρ hρ₂ hj hpP hpB).mp hbin
  have hnrc : 0 < norm (r*c) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hr) (primary_ne_zero hc))
  have hnb : norm p*norm (r*c) ≤ b := (le_div_iff₀ hnrc).mp hint.2
  apply (le_div_iff₀ (zero_lt_one.trans (geometricBinLower_gt_one hρ hj))).mpr
  calc
    norm (r*c)*geometricBinLower ρ B j ≤ norm (r*c)*norm p :=
      mul_le_mul_of_nonneg_left hnorm.1 hnrc.le
    _ ≤ b := by simpa only [mul_comm] using hnb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeLogScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-prime threshold gives the actual logarithmic parameter
range required by the published prime estimate, even after bin dilation. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem long_prime_logarithmic_window {P₀ : ℝ} (hP₀ : 1 < P₀) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X/4 ∧
      ∀ P : ℝ, Real.exp (Real.sqrt (Real.log X))/2 ≤ P →
        P₀ ≤ P ∧ Real.log X/4 ≤ (Real.log P)^2 := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop
    (max (2*Real.log 2) (Real.log (2*P₀)))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))] with X hroot hL
  have hroot₂ : 2*Real.log 2 ≤ Real.sqrt (Real.log X) := (le_max_left _ _).trans hroot
  have hrootP : Real.log (2*P₀) ≤ Real.sqrt (Real.log X) := (le_max_right _ _).trans hroot
  refine ⟨by linarith,?_⟩
  intro P hP
  have hPpos : 0 < P := (div_pos (Real.exp_pos _) (by norm_num)).trans_le hP
  have hP₀pos : 0 < 2*P₀ := by linarith
  refine ⟨?_,?_⟩
  · calc
      P₀ = Real.exp (Real.log (2*P₀))/2 := by rw [Real.exp_log hP₀pos]; ring
      _ ≤ Real.exp (Real.sqrt (Real.log X))/2 :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrootP) (by norm_num)
      _ ≤ P := hP
  · have hlog : Real.sqrt (Real.log X)-Real.log 2 ≤ Real.log P := by
      have h := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hP
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num),Real.log_exp] at h
      exact h
    have hhalf : Real.sqrt (Real.log X)/2 ≤ Real.log P := by linarith
    have hlog₀ : 0 ≤ Real.log P := (by positivity : 0 ≤ Real.sqrt (Real.log X)/2).trans hhalf
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg hlog₀ (by positivity : 0 ≤ Real.sqrt (Real.log X)/2))
    have hsqrt := Real.sq_sqrt (show 0 ≤ Real.log X by linarith)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LongPrimeParameterScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed powers of log X fit the prime parameter log X/4 after a
one-unit exponent enlargement. This is uniform in all arithmetic data. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_log_parameter_power (c A : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      0 < Real.log X/4 ∧ c*(Real.log X)^A ≤ (Real.log X/4)^(A+1) := by
  have ht : Tendsto (fun X : ℝ => Real.log X/4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num : (0:ℝ) < 4)
  filter_upwards [ht.eventually (eventually_ge_atTop (max 1 (c*4^A)))] with X hX
  have hT : 0 < Real.log X/4 := zero_lt_one.trans_le ((le_max_left _ _).trans hX)
  refine ⟨hT,?_⟩
  have he : Real.log X = 4*(Real.log X/4) := by ring
  calc
    c*(Real.log X)^A = (c*4^A)*(Real.log X/4)^A := by
      conv_lhs => rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hT.le]
      ring
    _ ≤ (Real.log X/4)*(Real.log X/4)^A :=
      mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hX) (Real.rpow_nonneg hT.le _)
    _ = (Real.log X/4)^(A+1) := by
      rw [Real.rpow_add hT,Real.rpow_one]
      ring

lemma prime_parameter_log_saving {L D b : ℝ} (hL : 0 < L) :
    b/(L/4)^D = 4^D*b/L^D := by
  rw [Real.div_rpow hL.le (by norm_num : (0:ℝ) ≤ 4)]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NarrowPrimeBinCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bin counts when the geometric ratio is allowed to approach
one. The width loss is explicit, as required for logarithmic stopping bins. -/
noncomputable section
namespace CubicFirstMoment

lemma logarithm_one_add_lower {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    δ/2 ≤ Real.log (1+δ) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ.le)
  apply (le_div_iff₀ (by positivity : 0 < δ+2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hδone hδ.le]

theorem geometricBinCount_width_bound {δ B : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hB : 1 ≤ B) :
    (geometricBinCount (1+δ) B:ℝ) ≤ 2*Real.log B/δ+1 := by
  have hlogδ := logarithm_one_add_lower hδ hδone
  have hlogpos : 0 < Real.log (1+δ) := (by positivity : 0 < δ/2).trans_le hlogδ
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hcount := (Nat.ceil_lt_add_one (div_nonneg hlogB hlogpos.le)).le
  change (geometricBinCount (1+δ) B:ℝ) ≤ _ at hcount
  apply hcount.trans
  refine add_le_add ?_ le_rfl
  calc
    Real.log B/Real.log (1+δ) ≤ Real.log B/(δ/2) :=
      div_le_div_of_nonneg_left hlogB (by positivity) hlogδ
    _ = 2*Real.log B/δ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complementary norm and exclusion bounds needed to put
stopped prime rows on the parameter log X/4. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_complement_power_bound {X C ξ P b : ℝ} {m : ℕ}
    (hX : 1 < X) (hgap : C < ξ*m) (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P) :
    b/P < (X^ξ)^m := by
  calc
    b/P ≤ b := div_le_self hb hP
    _ ≤ X^C := hbX
    _ < X^(ξ*m) := Real.rpow_lt_rpow_of_exponent_lt hX hgap
    _ = (X^ξ)^m := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans hX).le]

lemma stopped_complement_exclusion_log {r d e : Eisenstein} (hr : primary r)
    (hd : primary d) (he : e ≠ 0) {X C E b P : ℝ} (hX : 0 < X)
    (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P)
    (hrd : norm (r*d) ≤ b/P) (heX : norm e ≤ X^E) :
    Real.log (norm (r*(d*e))) ≤ (C+E)*Real.log X := by
  have hrp : 0 < norm (r*d) := zero_lt_one.trans_le
    (one_le_norm (primary_ne_zero (primary_mul hr hd)))
  have hep : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  have hrX : norm (r*d) ≤ X^C := hrd.trans ((div_le_self hb hP).trans hbX)
  calc
    Real.log (norm (r*(d*e))) = Real.log (norm (r*d))+Real.log (norm e) := by
      rw [←mul_assoc,norm_mul_eq,Real.log_mul (ne_of_gt hrp) (ne_of_gt hep)]
    _ ≤ Real.log (X^C)+Real.log (X^E) :=
      add_le_add (Real.log_le_log hrp hrX) (Real.log_le_log hep heX)
    _ = (C+E)*Real.log X := by rw [Real.log_rpow hX,Real.log_rpow hX]; ring

lemma geometricBinCount_logarithmic_width {X B δ C H : ℝ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hB : 1 ≤ B) (hBX : B ≤ X^C)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-H) ≤ δ) :
    (geometricBinCount (1+δ) B:ℝ) ≤ (2*C+1)*(Real.log X)^(H+1) := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL
  have hlogB : Real.log B ≤ C*Real.log X := by
    have he := Real.log_le_log (zero_lt_one.trans_le hB) hBX
    rwa [Real.log_rpow hX] at he
  have hinv : δ⁻¹ ≤ (Real.log X)^H := by
    have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLp (-H)) hwidth
    simpa only [one_div,Real.rpow_neg hLp.le,inv_inv] using hi
  have hone : 1 ≤ (Real.log X)^(H+1) := Real.one_le_rpow hL (by linarith)
  apply (geometricBinCount_width_bound hδ hδone hB).trans
  calc
    2*Real.log B/δ+1 ≤ (2*(C*Real.log X))*(Real.log X)^H+1 := by
      rw [div_eq_mul_inv]
      gcongr
    _ = 2*C*(Real.log X)^(H+1)+1 := by
      rw [Real.rpow_add hLp,Real.rpow_one]
      ring
    _ ≤ (2*C+1)*(Real.log X)^(H+1) := by nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedBeta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected-side prime cancellation applies to the literal
stoppedBeta coefficient, with its global-largest role selected exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma selected_largest_bin_nonempty {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {r d : Eisenstein} (hr : primary r) (hd : primary d)
    (hrole : largestPrimeChoice (r*d) ∣ d)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j) :
    (primaryPrimeFactors d).Nonempty := by
  have hne : (primaryPrimeFactors (r*d)).Nonempty := by
    by_contra hempty
    have hc : largestPrimeChoice (r*d) = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    rw [hc] at hbin
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hone] at hbin
    omega
  have hp := (primaryPrimeFactor_spec (primary_mul hr hd) (largestPrimeChoice_spec hne).1).1
  exact ⟨largestPrimeChoice (r*d),(primaryPrime_mem_factors_iff hd).mpr ⟨hp,hrole⟩⟩

lemma selectedStoppedDivisorSet_eq {B ρ a b : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool) (r e : Eisenstein)
    (hr : primary r) :
    selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e =
      (primaryElementBall B).filter (fun d =>
        (Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b) ∧
          stoppedSelectedTest B ρ j j₀ k h Z Q early r d) := by
  ext d
  constructor
  · intro hmem
    obtain ⟨hd,hs,_hne,hcop,hint,hrole,hbin,hstop⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨hd,⟨hs,hcop,hint.1,hint.2⟩,hstop,hrole,hbin⟩
  · intro hmem
    obtain ⟨hd,⟨hs,hcop,ha,hb⟩,hstop,hrole,hbin⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr
      ⟨hd,hs,selected_largest_bin_nonempty hj hr (mem_primaryElementBall.mp hd).1 hrole hbin,
        hcop,⟨ha,hb⟩,hrole,hbin,hstop⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargestRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact splitting of a valid largest-prime bin into its distinguished
and selected-divisor roles. The source stopping test is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largestPrimeChoice_prime_of_bin {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {n : Eisenstein} (hn : primary n)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice n) = j) :
    primaryPrime (largestPrimeChoice n) ∧ largestPrimeChoice n ∣ n := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have hchoice : largestPrimeChoice n = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hchoice,hone] at hbin
    omega
  exact primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1

theorem stoppedBeta_largest_bin_roles (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (w B ρ : ℝ) {j : ℕ} (hj : j < geometricBinCount ρ B)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n =
      stoppedBeta R D f primeDetectorCutoff w (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n+
      stoppedBeta R D f primeDetectorCutoff w (stoppedSelectedTest B ρ j j₀ k h Z Q early) n := by
  unfold stoppedBeta primaryPairCoefficient
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have he : t.1*t.2 = n := (Finset.mem_filter.mp ht).2
  by_cases htest : stoppedLargestBinTest B ρ j j₀ k h Z Q early t.1 t.2
  · obtain ⟨hstop,hbin⟩ := htest
    have hp := largestPrimeChoice_prime_of_bin hj hn (he ▸ hbin)
    have hsf : Squarefree (t.1*t.2) := he.symm ▸ hs
    have hdiv : largestPrimeChoice (t.1*t.2) ∣ t.1*t.2 := by simpa only [he] using hp.2
    have hp' : Prime (largestPrimeChoice (t.1*t.2)) := by simpa only [he] using hp.1.2
    rcases prime_factor_unique_side hp' hsf hdiv with ⟨hr,hnd⟩ | ⟨hd,hnr⟩
    · simp only [stoppedLargestBinTest,stoppedDistinguishedTest,stoppedSelectedTest,
        hstop,hbin,hr,hnd,and_self,and_false,and_true,ite_true, if_true,ite_false, if_false,add_zero]
    · simp only [stoppedLargestBinTest,stoppedDistinguishedTest,stoppedSelectedTest,
        hstop,hbin,hd,hnr,and_self,and_false,and_true,ite_true, if_true,ite_false, if_false,zero_add]
  · have hd : ¬stoppedDistinguishedTest B ρ j j₀ k h Z Q early t.1 t.2 := by
      rintro ⟨ha,_,hb⟩
      exact htest ⟨ha,hb⟩
    have hc : ¬stoppedSelectedTest B ρ j j₀ k h Z Q early t.1 t.2 := by
      rintro ⟨ha,_,hb⟩
      exact htest ⟨ha,hb⟩
    simp only [htest,hd,hc,ite_false, if_false,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact long-bin decomposition of a stopped coefficient. The
complementary short-bin part is supported on genuinely smooth integers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedBeta_product_predicate (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    (P : Eisenstein → Prop) (n : Eisenstein) :
    stoppedBeta R D f ψ w (fun r d => selected r d ∧ P (r*d)) n =
      if P n then stoppedBeta R D f ψ w selected n else 0 := by
  unfold stoppedBeta primaryPairCoefficient
  by_cases hP : P n
  · rw [ite_eq_left hP]
    apply Finset.sum_congr rfl
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    simp only [he,hP,and_true]
  · rw [ite_eq_right hP]
    apply Finset.sum_eq_zero
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    simp only [he,hP,and_false,ite_false, if_false]

lemma largestPrimeChoice_valid_bin {B ρ : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) (hnorm : 1 < norm n)
    (hnB : norm n ≤ B) :
    primaryPrime (largestPrimeChoice n) ∧
      geometricPrimeBin ρ B (largestPrimeChoice n) < geometricBinCount ρ B := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have he := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hp := primaryPrimeFactors_prod hn hs
    rw [he,Finset.prod_empty] at hp
    have hnormone : norm n = 1 := by rw [←hp,norm_one_eq]
    linarith
  have hp := primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1
  exact ⟨hp.1,geometricPrimeBin_index hρ hρ₂ hp.1
    ((norm_le_of_dvd_nonzero (primary_ne_zero hn) hp.2).trans hnB)⟩

theorem stoppedBeta_long_bin_decomposition (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (w B ρ y : ℝ) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (hnorm : 1 < norm n) (hnB : norm n ≤ B) :
    stoppedBeta R D f primeDetectorCutoff w
        (stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early) n =
      stoppedBeta R D f primeDetectorCutoff w (stoppedShortBinTest B ρ y j₀ k h Z Q early) n+
      ∑ j ∈ stoppedLongBins B ρ y,
        stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n := by
  let s := stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early
  let c := geometricPrimeBin ρ B (largestPrimeChoice n)
  let z := stoppedBeta R D f primeDetectorCutoff w s n
  have hc : c < geometricBinCount ρ B := (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2
  have heq (j : ℕ) :
      stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n =
        if c = j then z else 0 := by
    have hpred : stoppedLargestBinTest B ρ j j₀ k h Z Q early =
        (fun r d => s r d ∧ geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j) := by
      funext r d
      rfl
    rw [hpred]
    have hb := stoppedBeta_product_predicate R D f primeDetectorCutoff w s
      (fun x => geometricPrimeBin ρ B (largestPrimeChoice x) = j) n
    by_cases hh : geometricPrimeBin ρ B (largestPrimeChoice n) = j
    · simpa only [stoppedLargestBinTest,s,c,z,hh,ite_true, if_true] using hb
    · simpa only [stoppedLargestBinTest,s,c,z,hh,ite_false, if_false] using hb
  have hshort : stoppedBeta R D f primeDetectorCutoff w (stoppedShortBinTest B ρ y j₀ k h Z Q early) n =
      if geometricBinLower ρ B c < y/2 then z else 0 :=
    stoppedBeta_product_predicate R D f primeDetectorCutoff w s
      (fun x => geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice x)) < y/2) n
  simp_rw [heq]
  rw [hshort]
  have hsum : (∑ j ∈ stoppedLongBins B ρ y, if c = j then z else 0) =
      if c ∈ stoppedLongBins B ρ y then z else 0 := by simp
  rw [hsum]
  have hmem : c ∈ stoppedLongBins B ρ y ↔ y/2 ≤ geometricBinLower ρ B c := by
    simp only [stoppedLongBins,Finset.mem_filter,Finset.mem_range,hc,true_and]
  rw [if_congr hmem rfl rfl]
  by_cases hsmall : geometricBinLower ρ B c < y/2
  · simp only [hsmall,not_le_of_gt hsmall,ite_true, if_true,ite_false, if_false,add_zero]
    rfl
  · simp only [hsmall,le_of_not_gt hsmall,ite_true, if_true,ite_false, if_false,zero_add]
    rfl

theorem stopped_short_bin_smooth {B ρ y : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) (hnorm : 1 < norm n)
    (hnB : norm n ≤ B)
    (hshort : geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) < y/2) :
    ∀ p ∈ primaryPrimeFactors n, norm p ≤ y := by
  have hp := (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).1
  have hd := (largestPrimeChoice_prime_of_bin
    (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2 hn rfl).2
  have hcell := (geometricPrimeBin_cell hρ hρ₂ hp
    ((norm_le_of_dvd_nonzero (primary_ne_zero hn) hd).trans hnB)).2
  have hlast : norm (largestPrimeChoice n) < y := by
    have hlower : 0 < geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) := by
      exact zero_lt_one.trans (geometricBinLower_gt_one hρ
        (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2)
    nlinarith
  intro p hp
  have hne : (primaryPrimeFactors n).Nonempty := ⟨p,hp⟩
  have hlarge := (largestPrimeChoice_spec hne).2 p hp
  have hnat : normNat p ≤ normNat (largestPrimeChoice n) := by
    rcases hlarge with hl | he
    · exact hl.le
    · exact he.1.le
  have hnormle : norm p ≤ norm (largestPrimeChoice n) := by
    rw [←normNat_cast,←normNat_cast]
    exact_mod_cast hnat
  exact hnormle.trans hlast.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma stopped_largest_bin_moment_roles (U R D : Finset Eisenstein)
    (hU : ∀ n ∈ U, primary n) (f K : Eisenstein → ℂ)
    (hK : ∀ n, ¬Squarefree n → K n = 0) (w B ρ : ℝ) {j : ℕ}
    (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) :
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n*K n) =
      (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n*K n)+
      ∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n*K n := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : Squarefree n
  · rw [stoppedBeta_largest_bin_roles R D f w B ρ hj j₀ k h Z Q early (hU n hn) hs,add_mul]
  · simp only [hK n hs,mul_zero,add_zero]

theorem stopped_long_bin_moment_decomposition (U R D : Finset Eisenstein)
    (hU : ∀ n ∈ U, primary n) (f K : Eisenstein → ℂ) (B ρ y w : ℝ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hK : ∀ n, ¬(Squarefree n ∧ 1 < norm n ∧ norm n ≤ B) → K n = 0)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) :
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early) n*K n) =
    (∑ n ∈ U, stoppedBeta R D f primeDetectorCutoff w
      (stoppedShortBinTest B ρ y j₀ k h Z Q early) n*K n)+
    ∑ j ∈ stoppedLongBins B ρ y, ∑ n ∈ U,
      stoppedBeta R D f primeDetectorCutoff w
        (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n*K n := by
  calc
    _ = ∑ n ∈ U,
        (stoppedBeta R D f primeDetectorCutoff w
          (stoppedShortBinTest B ρ y j₀ k h Z Q early) n+
          ∑ j ∈ stoppedLongBins B ρ y, stoppedBeta R D f primeDetectorCutoff w
            (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n)*K n := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : Squarefree n ∧ 1 < norm n ∧ norm n ≤ B
      · rw [stoppedBeta_long_bin_decomposition R D f w B ρ y hρ hρ₂ j₀ k h Z Q early
          (hU n hn) hp.1 hp.2.1 hp.2.2]
      · simp only [hK n hp,mul_zero]
    _ = _ := by
      simp_rw [add_mul,Finset.sum_mul]
      rw [Finset.sum_add_distrib,Finset.sum_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinSaving
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual geometric-bin complexity consumes only its
explicit logarithmic power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem geometric_bin_log_saving {X B δ C H D K b : ℝ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hB : 1 ≤ B) (hBX : B ≤ X^C)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-H) ≤ δ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (geometricBinCount (1+δ) B))
    (f : ℕ → ℂ) (hf : ∀ j ∈ S, ‖f j‖ ≤ K*b/(Real.log X)^(D+H+1)) :
    ‖∑ j ∈ S, f j‖ ≤ ((2*C+1)*K)*b/(Real.log X)^D := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL
  have hcount : (S.card:ℝ) ≤ (2*C+1)*(Real.log X)^(H+1) := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card hS))
    simpa only [Finset.card_range] using
      geometricBinCount_logarithmic_width hX hL hB hBX hC hH hδ hδone hwidth
  calc
    _ ≤ ∑ _j ∈ S, K*b/(Real.log X)^(D+H+1) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hf)
    _ = (S.card:ℝ)*(K*b/(Real.log X)^(D+H+1)) := by simp
    _ ≤ ((2*C+1)*(Real.log X)^(H+1))*(K*b/(Real.log X)^(D+H+1)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      have he : (Real.log X)^(D+H+1) =
          (Real.log X)^D*(Real.log X)^(H+1) := by
        rw [show D+H+1 = D+(H+1) by ring,Real.rpow_add hLp]
      rw [he]
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeRankin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Rankin bounds for the actual primary squarefree elements.
The map to their prime-factor subsets is injective; no ideal-counting
or smooth-number estimate is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_supported_rankin_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) (σ : ℝ) :
    (∑ b ∈ S, norm b^(-σ)) ≤ ∏ p ∈ U, (1+norm p^(-σ)) := by
  rw [Finset.prod_one_add]
  apply OAI.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p := (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [hn,Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg p)]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (norm_nonneg p) _)

lemma squarefree_supported_rankin_card (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U)
    {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hsize : ∀ b ∈ S, norm b ≤ B) :
    (S.card:ℝ) ≤ B^σ*∏ p ∈ U, (1+norm p^(-σ)) := by
  calc
    _ = ∑ _b ∈ S, (1:ℝ) := by simp
    _ ≤ ∑ b ∈ S, B^σ*norm b^(-σ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        1 = norm b^σ*norm b^(-σ) := by
          rw [←Real.rpow_add hb0,add_neg_cancel,Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hb0.le (hsize b hb) hσ) (Real.rpow_nonneg hb0.le _)
    _ = B^σ*∑ b ∈ S, norm b^(-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (squarefree_supported_rankin_sum S U hS hU σ)
      (Real.rpow_nonneg hB _)

lemma finite_euler_product_le_exp (U : Finset Eisenstein) (σ : ℝ) :
    (∏ p ∈ U, (1+norm p^(-σ))) ≤ Real.exp (∑ p ∈ U, norm p^(-σ)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    exact add_nonneg zero_le_one (Real.rpow_nonneg (norm_nonneg p) _)
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (norm p^(-σ))

lemma shifted_prime_reciprocal_le {y : ℝ} (hy : 1 < y)
    {p : Eisenstein} (hp : primaryPrime p) (hpy : norm p ≤ y) :
    norm p^(-1+(Real.log y)⁻¹) ≤ Real.exp 1*(norm p)⁻¹ := by
  have hp0 := norm_pos_of_ne_zero hp.2.ne_zero
  have hl : 0 < Real.log y := Real.log_pos hy
  have hpower : y^((Real.log y)⁻¹) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hy),mul_inv_cancel₀ hl.ne']
  rw [Real.rpow_add hp0,Real.rpow_neg_one]
  calc
    _ ≤ (norm p)⁻¹*y^((Real.log y)⁻¹) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hp0.le hpy (inv_nonneg.mpr hl.le)) (inv_nonneg.mpr hp0.le)
    _ = _ := by rw [hpower,mul_comm]

theorem smooth_squarefree_rankin_bound (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) {B y : ℝ}
    (hB : 0 ≤ B) (hy : Real.exp 1 ≤ y) (hsize : ∀ b ∈ S, norm b ≤ B)
    (hsmooth : ∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, norm p ≤ y) :
    (S.card:ℝ) ≤ B^(1-(Real.log y)⁻¹)*
      Real.exp (Real.exp 1*∑ p ∈ primeCutoff y, (norm p)⁻¹) := by
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hy
  have hl : 1 ≤ Real.log y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hy
  have hσ : 0 ≤ 1-(Real.log y)⁻¹ := sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hl)
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff y := by
    intro b hb p hp
    exact mem_primeCutoff.mpr ⟨(primaryPrimeFactor_spec (hS b hb).1 hp).1,hsmooth b hb p hp⟩
  apply (squarefree_supported_rankin_card S (primeCutoff y) hS hsub hB hσ hsize).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hB _)
  apply (finite_euler_product_le_exp (primeCutoff y) (1-(Real.log y)⁻¹)).trans
  apply Real.exp_le_exp.mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  convert shifted_prime_reciprocal_le hy1 (mem_primeCutoff.mp hp).1
    (mem_primeCutoff.mp hp).2 using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothRankinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

private lemma exp_rankin_absorption {κ C D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧
      Real.exp (-κ*T)*Real.exp (C*(1+Real.log T)) ≤ T^(-D) := by
  have hsmall := ((isLittleO_rpow_exp_pos_mul_atTop (C+D) hκ).const_mul_left
    (Real.exp C)).def zero_lt_one
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with T ht hT
  refine ⟨hT,?_⟩
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have ht' : Real.exp C*T^(C+D) ≤ Real.exp (κ*T) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      (Real.rpow_nonneg hT0.le _)),Real.norm_of_nonneg (Real.exp_nonneg _),one_mul] using ht
  have heq : Real.exp (-κ*T)*Real.exp (C*(1+Real.log T)) =
      (Real.exp C*T^C)/Real.exp (κ*T) := by
    have he : Real.exp (C*(1+Real.log T)) = Real.exp C*T^C := by
      rw [Real.rpow_def_of_pos hT0,←Real.exp_add]
      congr 1
      ring
    rw [he,show -κ*T = -(κ*T) by ring,Real.exp_neg,div_eq_mul_inv]
    ring
  rw [heq,Real.rpow_neg hT0.le,←one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.rpow_pos_of_pos hT0 D)).mpr
  rw [one_mul]
  rw [mul_assoc,←Real.rpow_add hT0]
  exact ht'

theorem smooth_squarefree_log_saving (hpnt : PrimaryPrimePNT)
    {κ D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ (B : ℝ) (S : Finset Eisenstein),
      Real.exp (κ*T^2) ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, norm b ≤ B) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, norm p ≤ Real.exp T) →
      (S.card:ℝ) ≤ B*T^(-D) := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  filter_upwards [exp_rankin_absorption (C := Real.exp 1*C) (D := D) hκ]
    with T hT
  intro B S hB hS hsize hsmooth
  have hT0 : 0 < T := zero_lt_one.trans_le hT.1
  have hB0 : 0 < B := (Real.exp_pos _).trans_le hB
  have hlogB : κ*T^2 ≤ Real.log B := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hB
  have hlogdiv : κ*T ≤ Real.log B/T := by
    apply (le_div_iff₀ hT0).mpr
    nlinarith [hlogB]
  have hpower : B^(1-T⁻¹) ≤ B*Real.exp (-κ*T) := by
    calc
      _ = B*Real.exp (-(Real.log B/T)) := by
        calc
          _ = Real.exp (Real.log B*(1-T⁻¹)) := Real.rpow_def_of_pos hB0 _
          _ = Real.exp (Real.log B)*Real.exp (-(Real.log B/T)) := by
            rw [←Real.exp_add]
            congr 1
            ring
          _ = _ := by rw [Real.exp_log hB0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) hB0.le
  have hraw := smooth_squarefree_rankin_bound S hS hB0.le
    (Real.exp_le_exp.mpr hT.1) hsize hsmooth
  simp only [Real.log_exp] at hraw
  calc
    _ ≤ B^(1-T⁻¹)*Real.exp (Real.exp 1*
        ∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) := hraw
    _ ≤ (B*Real.exp (-κ*T))*Real.exp (Real.exp 1*C*(1+Real.log T)) := by
      apply mul_le_mul hpower
      · apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (hprime T hT.1) (Real.exp_nonneg 1)
        simpa only [mul_assoc] using h
      · exact Real.exp_nonneg _
      · positivity
    _ = B*(Real.exp (-κ*T)*Real.exp (Real.exp 1*C*(1+Real.log T))) := by ring
    _ ≤ B*T^(-D) := mul_le_mul_of_nonneg_left hT.2 hB0.le

/-- The manuscript's actual long-prime cutoff. The exponent D is
arbitrary, so this discards the terms having no prime above exp(sqrt(log X)). -/
theorem smooth_squarefree_discard (hpnt : PrimaryPrimePNT)
    {κ D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : ℝ) (S : Finset Eisenstein),
      X^κ ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, norm b ≤ B) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b,
        norm p ≤ Real.exp (Real.sqrt (Real.log X))) →
      (S.card:ℝ) ≤ B*(Real.log X)^(-D) := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (smooth_squarefree_log_saving (D := 2*D) hpnt hκ),
    eventually_gt_atTop (1:ℝ)] with X hsave hX
  intro B S hB hS hsize hsmooth
  have hlog : 0 < Real.log X := Real.log_pos hX
  have he : Real.exp (κ*(Real.sqrt (Real.log X))^2) = X^κ := by
    rw [Real.sq_sqrt hlog.le,Real.rpow_def_of_pos (zero_lt_one.trans hX)]
    congr 1
    ring
  have h := hsave B S (he.symm ▸ hB) hS hsize hsmooth
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hlog.le]
  congr 2
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSmoothDiscard
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth-number removal for the literal stopped coefficient family.
The uniform coefficient bound is already proved from its distinguished
rough-prime construction. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_smooth_discard (hpnt : PrimaryPrimePNT)
    {ξ C κ A : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C) (hκ : 0 < κ)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : ℝ)
      (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
      (R D U : Finset Eisenstein) (selected : Eisenstein → Eisenstein → Prop),
      X^κ ≤ B → B ≤ C*X →
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) → (∀ r ∈ R, primary r) →
      (∀ b ∈ U, primary b ∧ Squarefree b) → (∀ b ∈ U, norm b ≤ B) →
      (∀ b ∈ U, ∀ p ∈ primaryPrimeFactors b,
        norm p ≤ Real.exp (Real.sqrt (Real.log X))) →
      (∑ b ∈ U, ‖stoppedBeta R D
        (distinguishedTupleCoefficient S W ψ (X^ξ) (X^(2/5:ℝ)))
        ψ (X^ξ) selected b‖) ≤ B*(Real.log X)^(-A) := by
  obtain ⟨K,hK,hcoef⟩ := stoppedBeta_distinguished_uniform (ι := ι) hξ hξz hC
    hψ hψone hψzero
  have hlogK : ∀ᶠ X : ℝ in atTop, K ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop K)
  filter_upwards [hcoef,smooth_squarefree_discard (D := A+1) hpnt hκ,
    hlogK,eventually_gt_atTop (1:ℝ)] with X hcoef hcount hlogK hX
  intro B S W R D U selected hXB hBX hS hW hR hU hsize hsmooth
  have hB : 0 < B := (Real.rpow_pos_of_pos (zero_lt_one.trans hX) κ).trans_le hXB
  have hlog : 0 < Real.log X := Real.log_pos hX
  calc
    _ ≤ ∑ _b ∈ U, K := by
      apply Finset.sum_le_sum
      intro b hb
      exact hcoef S W R D selected hS hW hR b (hU b hb).1 (hU b hb).2
        ((hsize b hb).trans hBX)
    _ = K*(U.card:ℝ) := by simp [mul_comm]
    _ ≤ K*(B*(Real.log X)^(-(A+1))) :=
      mul_le_mul_of_nonneg_left (hcount B U hXB hU hsize hsmooth) hK.le
    _ ≤ (Real.log X)*(B*(Real.log X)^(-(A+1))) :=
      mul_le_mul_of_nonneg_right hlogK (by positivity)
    _ = B*(Real.log X)^(-A) := by
      have hp : Real.log X*(Real.log X)^(-(A+1)) = (Real.log X)^(-A) := by
        calc
          _ = (Real.log X)^1*(Real.log X)^(-(A+1)) := by rw [Real.rpow_one]
          _ = (Real.log X)^(1+(-(A+1))) := (Real.rpow_add hlog _ _).symm
          _ = _ := by congr 1; ring
      rw [mul_left_comm,hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredResidualFrequencies
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from ramified/cube frequencies to the structured pair
moments. A cube factor becomes an arithmetic exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cubicSymbol_cube_indicator {z : Eisenstein} (hz : primary z) (j : Eisenstein) :
    cubicSymbol z (j^3) = if IsCoprime z j then 1 else 0 := by
  rw [cubicSymbol_pow_upper hz]
  by_cases hj : IsCoprime z j
  · rw [ite_eq_left hj,cubicSymbol_cube_of_isCoprime hz j hj]
  · rw [ite_eq_right hj,cubicSymbol_eq_zero_of_not_isCoprime hz hj,zero_pow (by norm_num : (3:ℕ) ≠ 0)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma angularStoppedCharacterSum_cube (ℓ : ℤ) (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v j e : Eisenstein) :
    angularStoppedCharacterSum ℓ X w z a b u W selected (v*j^3) e =
      angularStoppedCharacterSum ℓ X w z a b u W selected v (e*j) := by
  unfold angularStoppedCharacterSum stoppedIntervalSupport
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : primary n := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  have hcop : IsCoprime n (e*j) ↔ IsCoprime n e ∧ IsCoprime n j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  rw [cubicSymbol_mul_upper hnp,cubicSymbol_cube_indicator hnp j]
  by_cases he : IsCoprime n e <;> by_cases hj : IsCoprime n j <;>
    simp [hcop,he,hj]

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma low_core_log_quotient {z : ℝ} (hz : 1 ≤ z) (a k : ℕ) :
    z^a/(z^(a+k+1))^2 ≤ 1/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  apply (div_le_div_iff₀ (pow_pos (pow_pos hzp _) 2) (pow_pos hzp _)).mpr
  rw [one_mul,← pow_add,← pow_mul]
  exact pow_le_pow_right₀ hz (by omega)

lemma low_core_mass_bound {M C J L z : ℝ} {n a k : ℕ}
    (hJ : 0 ≤ J) (hz : 1 ≤ z)
    (hn : (n:ℝ) ≤ 324*z^a*J)
    (hM : M ≤ (n:ℝ)*(C*L/z^(a+k+1))^2) :
    M ≤ (324*C^2)*J*L^2/z^k := by
  have hquot := low_core_log_quotient hz a k
  calc
    M ≤ (324*z^a*J)*(C*L/z^(a+k+1))^2 := hM.trans
      (mul_le_mul_of_nonneg_right hn (sq_nonneg _))
    _ = (324*C^2)*J*L^2*(z^a/(z^(a+k+1))^2) := by rw [div_pow]; ring
    _ ≤ (324*C^2)*J*L^2*(1/z^k) := mul_le_mul_of_nonneg_left hquot
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) hJ) (sq_nonneg L))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicCoreCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed complementary primary factor in a free-prime sum is a
constant of norm at most one, even when its cubic symbol vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_fixed_primary_free_prime_sum (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    (∑ p ∈ S, a p*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v) =
      (normTwist u r*angularCubicSymbol ℓ r v)*
        ∑ p ∈ S, a p*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpc : p*c ≠ 0 := mul_ne_zero (hS p hp).2.ne_zero (primary_ne_zero hc)
  rw [normTwist_mul u (primary_ne_zero hr) hpc,
    angularCubicSymbol_mul_lower ℓ (primary_ne_zero hr) hpc]
  ring


lemma angular_fixed_primary_free_prime_norm (ℓ : ℤ) (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (a : Eisenstein → ℂ)
    (r c v : Eisenstein) (hr : primary r) (hc : primary c) (u : ℝ) :
    ‖∑ p ∈ S, a p*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v‖ ≤
      ‖∑ p ∈ S, a p*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ := by
  rw [angular_fixed_primary_free_prime_sum ℓ S hS a r c v hr hc u,norm_mul,
    norm_mul,norm_normTwist,one_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (angularCubicSymbol_norm_le_one ℓ hr v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedBeta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected-side prime cancellation applies to the literal
stoppedBeta coefficient, with its global-largest role selected exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_stoppedBeta_selected_identity (ℓ : ℤ) {B ρ a b w u : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport R (primaryElementBall B),
      stoppedBeta R (primaryElementBall B) f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)) =
      ∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selectedStoppedDivisorSet_eq hj Z Q early r e (hR r hr),Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases ht : stoppedSelectedTest B ρ j j₀ k h Z Q early r d
  · by_cases hc : Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b
    · simp only [ht,hc,and_self,ite_true, if_true]
      ring
    · simp only [ht,hc,false_and,ite_false, if_false,mul_zero]
  · simp only [ht,and_false,ite_false, if_false,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedPrimeBox
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation of the actual free selected-bin prime with the complete
two-stage stopping predicate. Only the cited Kummer prime input is used;
the stopping restriction is removed by proved bin invariance. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_long_stopped_selected_interval_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ w u a b : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ (c v e : Eisenstein) (C : Finset Eisenstein), primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*e)) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein),
      ‖∑ p ∈ ((((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
          (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j)).filter
          (fun p => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
            j₀ k h Z Q early r (p*c)),
        cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_prime_geometric_interval_moebius_saving hEF ℓ hℓ hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
    j₀ k h Z Q early r
  let S := (((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter (fun p => IsCoprime p (c*e))).filter
    (fun p => largestPrimePredicate primeTieCode C p ∧ geometricPrimeBin ρ B p = j)
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p :=
    (mem_primeCutoff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1).1
  have hcop (p : Eisenstein) (hp : p ∈ S) : ¬p ∣ c := by
    have hpe := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpc : IsCoprime p c := hpe.of_isCoprime_of_dvd_right (dvd_mul_right c e)
    exact fun hd => (hS p hp).2.not_isUnit (hpc.isUnit_of_dvd hd)
  have hfull : ‖∑ p ∈ S, cutoffMoebius primeDetectorCutoff w (p*c)*
      normTwist u (p*c)*angularCubicSymbol ℓ (p*c) v‖ ≤ K*geometricBinLower ρ B j/T^D :=
    hbound T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v e C hc hs hv hnc hNv he hNe
  change ‖∑ p ∈ S with stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
    j₀ k h Z Q early r (p*c), _‖ ≤ _
  by_cases hne : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hne
    have hbin (p : Eisenstein) (hp : p ∈ S) : geometricPrimeBin ρ B p = geometricPrimeBin ρ B p₀ :=
      (Finset.mem_filter.mp hp).2.2.trans (Finset.mem_filter.mp hp₀).2.2.symm
    rw [sum_stoppedSide_same_bin S (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early r hc hs hp₀ hS hcop hbin]
    split_ifs
    · exact hfull
    · rw [norm_zero]
      have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
      positivity
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.filter_empty,Finset.sum_empty,norm_zero]
    have hP0 : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
    positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-bin free-prime row with its actual full product,
complementary exclusion and both stopping tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem angular_stopped_selected_prime_row_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      0 < w → |u| ≤ T^H →
      ∀ r c v e : Eisenstein, primary r → primary c → Squarefree c → v ≠ 0 →
        (¬∃ k : Eisenstein, k^3 = v) → norm v ≤ T^A → e ≠ 0 →
        Real.log (norm (c*(r*e))) ≤ T^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angular_stoppedSelectedPrimeRow ℓ B ρ a b w u j j₀ k h Z Q early r c v e‖ ≤
        K*geometricBinLower ρ B j/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_long_stopped_selected_interval_saving hEF ℓ hℓ hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w u j hT hρ hρ₂ hj hP hTP hw hu r c v e hr hc hs hv hnc hNv he hNe
    j₀ k h Z Q early
  unfold angular_stoppedSelectedPrimeRow
  apply (angular_fixed_primary_free_prime_norm ℓ (stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e)
    (fun p hp => stoppedSelectedPrimeSet_primary B ρ a b j j₀ k h Z Q early r c e hp)
    (fun p => cutoffMoebius primeDetectorCutoff w (p*c)) r c v hr hc u).trans
  exact hbound T B ρ w u a b j hT hρ hρ₂ hj hP hTP hw hu c v (r*e)
    (primaryPrimeFactors (r*c)) hc hs hv hnc hNv (mul_ne_zero (primary_ne_zero hr) he) hNe
    j₀ k h Z Q early r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the selected-bin free-prime rows, and the
complementary norm cutoff forced by the lower endpoint of the prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_selectedStopped_row_collection (ℓ : ℤ) (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) :
    (∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w (t.2*t.1)*normTwist u (r*(t.2*t.1))*
        angularCubicSymbol ℓ (r*(t.2*t.1)) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  unfold selectedStoppedRowPairs
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hrc : Squarefree (r*c) ∧ IsCoprime (r*c) e
  · simp only [hrc.1,hrc.2,true_and,ite_true, if_true]
    unfold angular_stoppedSelectedPrimeRow
    rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
      (stoppedSelectedPrimeSet_subset B ρ (a/norm (r*c)) (b/norm (r*c))
        j j₀ k h Z Q early r c e)]
  · have hzero (p : Eisenstein) :
        ¬(Squarefree (r*c) ∧ IsCoprime (r*c) e ∧
          p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
            j j₀ k h Z Q early r c e) := fun hp => hrc ⟨hp.1,hp.2.1⟩
    simp only [hzero,ite_false, if_false,Finset.sum_const_zero,hrc]


lemma angular_selectedStopped_row_eq_zero (ℓ : ℤ) {B ρ a b w u : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c v e : Eisenstein} (hr : primary r) (hc : primary c)
    (hbig : b/geometricBinLower ρ B j < norm (r*c)) :
    angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (r*c)) (b/norm (r*c)) w u
      j j₀ k h Z Q early r c v e = 0 := by
  unfold angular_stoppedSelectedPrimeRow
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (selectedStopped_complement_bound hρ hρ₂ hj hr hc hp) hbig).elim


theorem angular_selectedStopped_original_rows (ℓ : ℤ) (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) (hr : primary r) (hbB : b ≤ B) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  rw [selectedStopped_sum_reindex B ρ a b j j₀ k h Z Q early r e hr hbB]
  exact angular_selectedStopped_row_collection ℓ B ρ a b w u j j₀ k h Z Q early r v e

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original selected-side stopped sums, after their exact free-prime
reindexing. The complementary cutoff is derived from the actual bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_selectedStopped_original_collection (ℓ : ℤ) {B ρ a b w u : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) (hbB : b ≤ B) :
    (∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v) =
      ∑ t ∈ (R ×ˢ primaryElementBall B).filter
        (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j),
        if IsCoprime (t.1*t.2) e then f t.1*
          angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
            j j₀ k h Z Q early t.1 t.2 v e else 0 := by
  rw [Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [angular_selectedStopped_original_rows ℓ B ρ a b w u j j₀ k h Z Q early r v e (hR r hr) hbB,
    Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := (mem_primaryElementBall.mp hc).1
  by_cases hs : Squarefree (r*c)
  · by_cases he : IsCoprime (r*c) e
    · by_cases hn : norm (r*c) ≤ b/geometricBinLower ρ B j
      · simp only [hs,he,hn,and_self,ite_true, if_true]
      · have hz := angular_selectedStopped_row_eq_zero ℓ hρ hρ₂ hj (hR r hr) hc'
          (lt_of_not_ge hn) (v := v) (e := e) (a := a) (w := w) (u := u)
          (j₀ := j₀) (k := k) (h := h) (Z := Z) (Q := Q) (early := early)
        simp only [hs,he,hn,and_false,ite_false, if_false,and_true,ite_true, if_true,hz,mul_zero]
    · simp only [hs,he,and_false,ite_false, if_false]
      split_ifs <;> rfl
  · simp only [hs,false_and,ite_false, if_false]


theorem angular_stopped_selected_original_saving (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {A D H E : ℝ} (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      b ≤ B → 0 ≤ b → 1 ≤ w → |u| ≤ T^H →
      ∀ (R : Finset Eisenstein) (f : Eisenstein → ℂ) (M : ℝ) (m : ℕ),
      (∀ r ∈ R, primary r) → 0 ≤ M → (∀ r ∈ R, ‖f r‖ ≤ M) →
      (∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p) →
      b/geometricBinLower ρ B j < w^m →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ (R ×ˢ primaryElementBall B).filter
        (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j),
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v‖ ≤
        (18*((2^m:ℕ)*M)*K)*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hrow⟩ := angular_stopped_selected_prime_row_saving hEF ℓ hℓ hA hD hH hE
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro T B ρ a b w u j hT hρ hρ₂ hj hP hTP hbB hb hw hu R f M m hR hM hf hrough hsize
    v e hv hnc hNv he hlog j₀ k h Z Q early
  have hPpos : 0 < geometricBinLower ρ B j := zero_lt_one.trans (hP₀.trans_le hP)
  let U := (R ×ˢ primaryElementBall B).filter
    (fun t => Squarefree (t.1*t.2) ∧ norm (t.1*t.2) ≤ b/geometricBinLower ρ B j)
  let C := K*geometricBinLower ρ B j/T^D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (t : Eisenstein × Eisenstein) (ht : t ∈ U) :
      ‖if IsCoprime (t.1*t.2) e then f t.1*
          angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
            j j₀ k h Z Q early t.1 t.2 v e else 0‖ ≤ ‖f t.1‖*C := by
    by_cases hcop : IsCoprime (t.1*t.2) e
    · rw [ite_eq_left hcop,norm_mul]
      obtain ⟨ht,hprop⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr,hc⟩ := Finset.mem_product.mp ht
      exact mul_le_mul_of_nonneg_left
        (hrow T B ρ _ _ w u j hT hρ hρ₂ hj hP hTP (zero_lt_one.trans_le hw) hu
          t.1 t.2 v e (hR _ hr) (mem_primaryElementBall.mp hc).1
          (squarefree_mul_iff.mp hprop.1).2.2 hv hnc hNv he
          (hlog t (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hc⟩,hprop⟩))
          j₀ k h Z Q early) (_root_.norm_nonneg _)
    · rw [ite_eq_right hcop,norm_zero]
      exact mul_nonneg (_root_.norm_nonneg _) hC
  rw [angular_selectedStopped_original_collection ℓ hρ hρ₂ hj Z Q early R hR f v e hbB]
  change ‖∑ t ∈ U, _‖ ≤ _
  calc
    _ ≤ ∑ t ∈ U, ‖if IsCoprime (t.1*t.2) e then f t.1*
        angular_stoppedSelectedPrimeRow ℓ B ρ (a/norm (t.1*t.2)) (b/norm (t.1*t.2)) w u
          j j₀ k h Z Q early t.1 t.2 v e else 0‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ U, ‖f t.1‖*C := Finset.sum_le_sum hbound
    _ = (∑ t ∈ U, ‖f t.1‖)*C := (Finset.sum_mul _ _ _).symm
    _ ≤ (18*(b/geometricBinLower ρ B j)*((2^m:ℕ)*M))*C :=
      mul_le_mul_of_nonneg_right
        (stopped_complement_mass R (primaryElementBall B) hR
          (fun c hc => (mem_primaryElementBall.mp hc).1) f hM
          (div_nonneg hb hPpos.le) hf hw hrough hsize) hC
    _ = _ := by
      dsimp [C]
      field_simp [ne_of_gt hPpos]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedDistinguished
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-divisor role with the actual distinguished-tuple
coefficient. Its roughness and coefficient bound are proved internally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_selected_distinguished_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hE : 0 ≤ E) :
    ∃ K P₀ : ℝ, 0 < K ∧ 1 < P₀ ∧ ∀ (T B ρ a b w z u : ℝ) (j : ℕ),
      1 ≤ T → 1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      P₀ ≤ geometricBinLower ρ B j → T ≤ (Real.log (geometricBinLower ρ B j))^2 →
      b ≤ B → 0 ≤ b → 1 ≤ w → w ≤ z → |u| ≤ T^H →
      b/geometricBinLower ρ B j < w^m →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) → norm v ≤ T^A → e ≠ 0 →
      (∀ t ∈ orderedConvolutionSupport (fun _ : ι => primeCutoff B) ×ˢ primaryElementBall B,
        Squarefree (t.1*t.2) → norm (t.1*t.2) ≤ b/geometricBinLower ρ B j →
        Real.log (norm (t.2*(t.1*e))) ≤ T^E) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
          (primaryElementBall B),
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
          (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/T^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stopped_selected_original_saving hEF ℓ hℓ hA hD hH hE
  let M : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖*
    ((Fintype.card ι)^(Fintype.card ι):ℕ)+1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨18*((2^m:ℕ)*M)*K,P₀,by positivity,hP₀,?_⟩
  intro T B ρ a b w z u j hT hρ hρ₂ hj hP hTP hbB hb hw hwz hu hsize W hW
    v e hv hnc hNv he hNe j₀ k h Z Q early
  let S := fun _ : ι => primeCutoff B
  let R := orderedConvolutionSupport S
  let f := distinguishedTupleCoefficient S (fun l p => W l (norm p)) primeDetectorCutoff w z
  have hS : ∀ l, ∀ p ∈ S l, primaryPrime p := fun _ _ hp => (mem_primeCutoff.mp hp).1
  have hR : ∀ r ∈ R, primary r := fun _ hr =>
    orderedPrimarySupport_primary S (fun l p hp => (hS l p hp).1) hr
  have hf : ∀ r ∈ R, ‖f r‖ ≤ M := by
    intro r _
    apply (distinguishedTupleCoefficient_norm S hS (fun l p => W l (norm p))
      (fun l p _ => hW l _) (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
      w z r).trans
    dsimp [M]
    linarith
  let R₁ := R.filter (fun r => f r ≠ 0)
  have hR₁ : ∀ r ∈ R₁, primary r := fun r hr => hR r (Finset.mem_filter.mp hr).1
  have hrough : ∀ r ∈ R₁, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p := by
    intro r hr p hp
    have hp' := primaryPrimeFactor_spec (hR₁ r hr) hp
    exact (distinguishedTupleCoefficient_prime_support S hS (fun l p => W l (norm p))
      (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx)
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hp'.1 hp'.2).1.le
  have heq : (∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v) =
    ∑ r ∈ R₁, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hz : f r = 0 <;> simp only [hz,ne_eq,not_true_eq_false,not_false_eq_true,
      ite_false, if_false,ite_true, if_true,zero_mul]
  rw [angular_stoppedBeta_selected_identity ℓ hj Z Q early R hR f v e,heq]
  exact hbound T B ρ a b w u j hT hρ hρ₂ hj hP hTP hbB hb hw hu R₁ f M m hR₁ hM.le
    (fun r hr => hf r (Finset.mem_filter.mp hr).1) hrough hsize v e hv hnc hNv he
    (by
      intro t ht
      obtain ⟨ht,hs,hn⟩ := Finset.mem_filter.mp ht
      obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
      exact hNe t (Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hr).1,hd⟩) hs hn)
    j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-divisor role has the same log-X saving as the
distinguished role, for the literal stopped coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_selected_log_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      b ≤ B → 0 ≤ b → b ≤ X^C → X^ξ ≤ z → |u| ≤ (Real.log X)^H →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
          (primaryElementBall B),
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := angular_stoppedBeta_selected_distinguished_saving (ι := ι) m hEF ℓ hℓ
    (A := A+1) (D := D) (H := H+1) (E := 2)
    (by linarith) hD (by linarith) (by norm_num)
  refine ⟨K*4^D,by positivity,?_⟩
  filter_upwards [long_prime_logarithmic_window hP₀,
    eventually_log_parameter_power 1 A,eventually_log_parameter_power 1 H,
    eventually_log_parameter_power (C+E) 1,eventually_gt_atTop (1:ℝ)] with
      X hwindow hscaleA hscaleH hscaleE hX
  intro B ρ a b z u j hρ hρ₂ hj hPlong hbB hb hbX hwz hu W hW
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLp : 0 < Real.log X := Real.log_pos hX
  have hP := hwindow.2 _ hPlong
  have hw : 1 ≤ X^ξ := Real.one_le_rpow hX.le hξ.le
  have hsize : b/geometricBinLower ρ B j < (X^ξ)^m :=
    stopped_complement_power_bound hX hgap hb hbX (geometricBinLower_gt_one hρ hj).le
  have hNe (t : Eisenstein × Eisenstein)
      (ht : t ∈ orderedConvolutionSupport (fun _ : ι => primeCutoff B) ×ˢ primaryElementBall B)
      (_hs : Squarefree (t.1*t.2)) (hn : norm (t.1*t.2) ≤ b/geometricBinLower ρ B j) :
      Real.log (norm (t.2*(t.1*e))) ≤ (Real.log X/4)^(2:ℝ) := by
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
    have hprod := orderedPrimarySupport_primary (fun _ : ι => primeCutoff B)
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr
    have heq : t.2*(t.1*e) = t.1*(t.2*e) := by ring
    rw [heq]
    apply (stopped_complement_exclusion_log hprod (mem_primaryElementBall.mp hd).1 he hXp
      hb hbX (geometricBinLower_gt_one hρ hj).le hn heX).trans
    simpa only [Real.rpow_one,show (1:ℝ)+1=2 by norm_num] using hscaleE.2
  have hh := hbound (Real.log X/4) B ρ a b (X^ξ) z u j hwindow.1 hρ hρ₂ hj hP.1 hP.2
    hbB hb hw hwz (hu.trans (by simpa only [one_mul] using hscaleH.2)) hsize W hW
    v e hv hnc (hNv.trans (by simpa only [one_mul] using hscaleA.2)) he hNe
    j₀ k h Z Q early
  apply hh.trans_eq
  rw [prime_parameter_log_saving hLp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedLongBinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All long bins of the literal stopped coefficient have arbitrary
logarithmic saving. The number of bins is accounted for explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma angular_stoppedCharacterSum_largest_roles (ℓ : ℤ) (B ρ w z a b u : ℝ) (W : ι → ℝ → ℂ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (v e : Eisenstein) :
    angular_stoppedCharacterSum ℓ B w z a b u W (stoppedLargestBinTest B ρ j j₀ k h Z Q early) v e =
      angular_stoppedCharacterSum ℓ B w z a b u W (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) v e+
      angular_stoppedCharacterSum ℓ B w z a b u W (stoppedSelectedTest B ρ j j₀ k h Z Q early) v e := by
  apply stopped_largest_bin_moment_roles
  · intro n hn
    exact primaryPairSupport_primary _ _
      (fun r hr => orderedPrimarySupport_primary _ (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
      (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  · intro n hn
    simp only [hn,false_and,ite_false, if_false]
  · exact hj


theorem angular_stoppedBeta_long_bins_log_saving (m : ℕ)
    (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {A D H E F J ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hgap : 1 < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      0 ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ j ∈ stoppedLongBins X (1+δ) (Real.exp (Real.sqrt (Real.log X))),
        angular_stoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
          (stoppedLargestBinTest X (1+δ) j j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  have hD' : 0 < D+J+1 := by linarith
  obtain ⟨Kd,hKd,hd⟩ := angular_stoppedBeta_distinguished_log_saving_all (ι := ι) m hEF ℓ hℓ
    (C := 1) (D := D+J+1) (E := E) hA hD' hH hF hξ hgap
  obtain ⟨Ks,hKs,hs⟩ := angular_stoppedBeta_selected_log_saving (ι := ι) m hEF ℓ hℓ
    (C := 1) (D := D+J+1) (E := E) hA hD' hH hξ hgap
  refine ⟨3*(Kd+Ks),by positivity,?_⟩
  filter_upwards [hd,hs,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with X hd hs hX hL
  intro δ a b u V hδ hδone hwidth hb hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hXp : 0 < X := zero_lt_one.trans hX
  have hρ : 1 < 1+δ := by linarith
  have hρ₂ : 1+δ ≤ 2 := by linarith
  have hwz : X^ξ ≤ X^(2/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le hξz
  let S := stoppedLongBins X (1+δ) (Real.exp (Real.sqrt (Real.log X)))
  let f := fun j => angular_stoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
    (stoppedLargestBinTest X (1+δ) j j₀ k h Z Q early) v e
  have hS : S ⊆ Finset.range (geometricBinCount (1+δ) X) := Finset.filter_subset _ _
  have hf (j : ℕ) (hj : j ∈ S) : ‖f j‖ ≤ (Kd+Ks)*b/(Real.log X)^(D+J+1) := by
    obtain ⟨hj,hP⟩ := Finset.mem_filter.mp hj
    have hj' := Finset.mem_range.mp hj
    have hdist := hd X (1+δ) a b (X^(2/5:ℝ)) u V j hρ hρ₂ hj' hP hb
      (by simpa only [Real.rpow_one] using hbX) hwz hV hu hVF W (primaryElementBall X)
      hW hWi hWd (fun d hd => (mem_primaryElementBall.mp hd).1)
      v e hv hnc hNv he heX j₀ k h Z Q early
    have hsel := hs X (1+δ) a b (X^(2/5:ℝ)) u j hρ hρ₂ hj' hP hbX hb
      (by simpa only [Real.rpow_one] using hbX) hwz hu W hW v e hv hnc hNv he heX
      j₀ k h Z Q early
    change ‖angular_stoppedCharacterSum ℓ _ _ _ _ _ _ _ _ _ _‖ ≤ _
    rw [angular_stoppedCharacterSum_largest_roles ℓ X (1+δ) (X^ξ) (X^(2/5:ℝ)) a b u W
      hj' j₀ k h Z Q early v e]
    apply (norm_add_le _ _).trans
    apply (add_le_add hdist hsel).trans_eq
    ring
  simpa only [mul_one, show (2:ℝ)+1=3 by norm_num] using geometric_bin_log_saving hXp hL hX.le
    (by rw [Real.rpow_one]) (by norm_num : (0:ℝ) ≤ 1) hJ hδ hδone hwidth
    (add_nonneg hKd.le hKs.le) hb S hS f hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedShortBinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The discarded short bins of the literal stopped coefficient have
arbitrary logarithmic saving, by their proved smooth support. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stoppedBeta_short_bin_log_saving (ℓ : ℤ) (hpnt : PrimaryPrimePNT)
    {ξ κ D : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ (B ρ a b u : ℝ),
      1 < ρ → ρ ≤ 2 → 1 ≤ a → b ≤ B → X^κ ≤ b → b ≤ X →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D₀ : Finset Eisenstein),
      (∀ l, ∀ p ∈ S l, primaryPrime p) → (∀ l, ∀ p ∈ S l, ‖W l p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D₀, primary d) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) (v e : Eisenstein),
      ‖∑ n ∈ primaryPairSupport R D₀,
        stoppedBeta R D₀ (distinguishedTupleCoefficient S W primeDetectorCutoff
          (X^ξ) (X^(2/5:ℝ))) primeDetectorCutoff (X^ξ)
          (stoppedShortBinTest B ρ (Real.exp (Real.sqrt (Real.log X))) j₀ k h Z Q early) n*
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*angularCubicSymbol ℓ n v else 0)‖ ≤ b/(Real.log X)^D := by
  filter_upwards [stoppedBeta_smooth_discard (ι := ι) (A := D) hpnt hξ hξz
      (C := 1) (by norm_num) hκ
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
      (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx),
    eventually_gt_atTop (1:ℝ)] with X hdiscard hX
  intro B ρ a b u hρ hρ₂ ha hbB hbX hb S W R D₀ hS hW hR hD₀ j₀ k h Z Q early v e
  let y := Real.exp (Real.sqrt (Real.log X))
  let small := fun n : Eisenstein =>
    geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) < y/2
  let U := (primaryPairSupport R D₀).filter (fun n =>
    (Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b) ∧ small n)
  let f := distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let selected := stoppedShortBinTest B ρ y j₀ k h Z Q early
  let beta := stoppedBeta R D₀ f primeDetectorCutoff (X^ξ) selected
  have hprimary {n : Eisenstein} (hn : n ∈ primaryPairSupport R D₀) : primary n :=
    primaryPairSupport_primary R D₀ hR hD₀ hn
  have hzero (n : Eisenstein) (hn : ¬small n) : beta n = 0 := by
    change stoppedBeta R D₀ f primeDetectorCutoff (X^ξ)
      (fun r d => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early r d ∧ small (r*d)) n = 0
    rw [stoppedBeta_product_predicate,ite_eq_right hn]
  have heq : (∑ n ∈ primaryPairSupport R D₀, beta n*
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)) =
      ∑ n ∈ U, beta n*(normTwist u n*angularCubicSymbol ℓ n v) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
    · by_cases hs : small n
      · simp only [hc,hs,and_self,ite_true, if_true]
      · simp only [hc,hs,hzero n hs,and_false,ite_false, if_false,zero_mul]
    · simp only [hc,false_and,ite_false, if_false,mul_zero]
  have hU (n : Eisenstein) (hn : n ∈ U) : primary n ∧ Squarefree n := by
    obtain ⟨hn,hc,_⟩ := Finset.mem_filter.mp hn
    exact ⟨hprimary hn,hc.1⟩
  have hmass : (∑ n ∈ U, ‖beta n‖) ≤ b*(Real.log X)^(-D) := by
    apply hdiscard b S W R D₀ U selected hbX (by simpa only [one_mul] using hb)
      hS hW hR hU
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1.2.2.2
    · intro n hn
      obtain ⟨hn,hc,hs⟩ := Finset.mem_filter.mp hn
      exact stopped_short_bin_smooth hρ hρ₂ (hprimary hn) hc.1
        (ha.trans_lt hc.2.2.1) (hc.2.2.2.trans hbB) hs
  change ‖∑ n ∈ primaryPairSupport R D₀, beta n*_‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ n ∈ U, ‖beta n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_mul,norm_normTwist,one_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (angularCubicSymbol_norm_le_one ℓ (hU n hn).1 v)
    _ ≤ b*(Real.log X)^(-D) := hmass
    _ = _ := by rw [Real.rpow_neg (Real.log_pos hX).le,div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSequenceSW
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Kummer sequence condition for the literal stopped
coefficient: exact long/short splitting, both largest-prime roles,
all bin costs, and the smooth remainder are derived. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_sequence_kummer_sw (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ A D H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angular_stoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ξ)
  have hgap : 1 < ξ*m := by
    have ht := (div_lt_iff₀ hξ).mp hm
    simpa only [mul_comm] using ht
  obtain ⟨K,hK,hlong⟩ := angular_stoppedBeta_long_bins_log_saving (ι := ι) m hEF ℓ hℓ
    (E := E) hA hD hH hF hJ hξ hξz hgap
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [hlong,angular_stoppedBeta_short_bin_log_saving ℓ (ι := ι) (D := D)
    hpnt hξ hξz hκ,eventually_gt_atTop (1:ℝ)] with X hlong hshort hX
  intro δ a b u V hδ hδone hwidth ha hblow hbX hV hu hVF W hW hWi hWd
    v e hv hnc hNv he heX j₀ k h Z Q early
  have hρ : 1 < 1+δ := by linarith
  have hρ₂ : 1+δ ≤ 2 := by linarith
  have hb : 0 ≤ b := (Real.rpow_pos_of_pos (zero_lt_one.trans hX) κ).le.trans hblow
  let S := fun _ : ι => primeCutoff X
  let R := orderedConvolutionSupport S
  let T := primaryElementBall X
  let f := distinguishedTupleCoefficient S (fun l p => W l (norm p))
    primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let U := primaryPairSupport R T
  let F := fun n : Eisenstein =>
    if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
      then normTwist u n*angularCubicSymbol ℓ n v else 0
  have hS : ∀ l, ∀ p ∈ S l, primaryPrime p := fun _ _ hp => (mem_primeCutoff.mp hp).1
  have hR : ∀ r ∈ R, primary r := fun r hr =>
    orderedPrimarySupport_primary S (fun l p hp => (hS l p hp).1) hr
  have hT : ∀ t ∈ T, primary t := fun _ ht => (mem_primaryElementBall.mp ht).1
  have hU : ∀ n ∈ U, primary n := fun _ hn => primaryPairSupport_primary R T hR hT hn
  have hF : ∀ n, ¬(Squarefree n ∧ 1 < norm n ∧ norm n ≤ X) → F n = 0 := by
    intro n hn
    dsimp [F]
    split_ifs with hc
    · exact (hn ⟨hc.1,ha.trans_lt hc.2.2.1,hc.2.2.2.trans hbX⟩).elim
    · rfl
  have heq := stopped_long_bin_moment_decomposition U R T hU f F X (1+δ)
    (Real.exp (Real.sqrt (Real.log X))) (X^ξ) hρ hρ₂ hF j₀ k h Z Q early
  have hs : ‖angular_stoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
      (stoppedShortBinTest X (1+δ) (Real.exp (Real.sqrt (Real.log X))) j₀ k h Z Q early) v e‖ ≤
      b/(Real.log X)^D :=
    hshort X (1+δ) a b u hρ hρ₂ ha hbX hblow hbX S (fun l p => W l (norm p)) R T
      hS (fun l p _ => hW l _) hR hT j₀ k h Z Q early v e
  have hl := hlong δ a b u V hδ hδone hwidth hb hbX hV hu hVF
    W hW hWi hWd v e hv hnc hNv he heX j₀ k h Z Q early
  change ‖∑ n ∈ U, stoppedBeta R T f primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k h Z Q early) n*F n‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs hl).trans_eq
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSequenceRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the stopped largest-prime decomposition to the
squarefree coefficient row used in angular dispersion. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_stoppedCharacterSum_eq_rows (ℓ : ℤ) (X w z a b u : ℝ)
    (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) :
    angular_stoppedCharacterSum ℓ X w z a b u W selected v e =
      angularStoppedCharacterSum ℓ X w z a b u W selected v e := by
  unfold angular_stoppedCharacterSum angularStoppedCharacterSum stoppedIntervalSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
  · simp only [h,and_self,ite_true, if_true,angularStoppedRowCoefficient,stoppedRowCoefficient,
      angularCubicSymbol,angularKummerCharacter]
    ring
  · simp only [h,ite_false, if_false,mul_zero]

theorem angular_stopped_row_kummer_sw (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ A D H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  simpa only [angular_stoppedCharacterSum_eq_rows] using
    (angular_stopped_sequence_kummer_sw (ι := ι) hpnt hEF ℓ hℓ
      (E := E) hξ hξz hκ hA hD hH hF hJ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedCubeSW
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube frequencies are genuine coprimality exclusions in the angular
stopped row. The angular factor occurs only once in the coefficient. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_sequence_cube_sw (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ A D H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v j e : Eisenstein, v ≠ 0 → j ≠ 0 → (¬∃ n : Eisenstein, n^3 = v*j^3) →
      norm v ≤ (Real.log X)^A → norm j ≤ X^d → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) (v*j^3) e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,hK,hbound⟩ := angular_stopped_row_kummer_sw (ι := ι)
    (E := E+d) hpnt hEF ℓ hℓ hξ hξz hκ hA hD hH hF hJ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with X hbound hX
  intro δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v j e hv hj hnc hNv hNj he hNe j₀ k h Z Q early
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hncv : ¬∃ n : Eisenstein, n^3 = v := by
    rintro ⟨n,hn⟩
    exact hnc ⟨n*j,by rw [mul_pow,hn]⟩
  have hNej : norm (e*j) ≤ X^(E+d) := by
    rw [norm_mul_eq,Real.rpow_add hXpos]
    exact mul_le_mul hNe hNj (norm_nonneg _) (Real.rpow_nonneg hXpos.le _)
  rw [angularStoppedCharacterSum_cube ℓ]
  exact hbound δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v (e*j) hv hncv hNv (mul_ne_zero he hj) hNej j₀ k h Z Q early


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedLowCoreMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine small-core noncube mass bound for the stopped coefficient,
deduced from its proved Kummer cancellation and exact cube exclusion. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_low_core_mass (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (a k : ℕ) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V C : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      0 ≤ C → C ≤ X^d →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein), S ⊆ lowNoncubeSupport ((Real.log X)^a) C →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*C*b^2/(Real.log X)^k := by
  have ha' : (0:ℝ) < (a:ℝ) := Nat.cast_pos.mpr ha
  have hD : (0:ℝ) < (a+k+1:ℕ) := by positivity
  obtain ⟨K,hK,hbound⟩ := angular_stopped_sequence_cube_sw (ι := ι)
    (A := (a:ℝ)) (D := (a+k+1:ℕ)) (d := d) (E := E)
    hpnt hEF ℓ hℓ hξ hξz hκ ha' hD hH hF hJ
  refine ⟨324*K^2,by positivity,?_⟩
  filter_upwards [hbound,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with X hbound hlog
  intro δ l b u V C hδ hδone hwidth hl hb hbX hV hu hVF hC hCX W hW hWi hWd
    S hS e he hNe j₀ k₀ h Z Q early
  have hterm (v : Eisenstein) (hv : v ∈ S) :
      ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖ ≤ K*b/(Real.log X)^(a+k+1) := by
    obtain ⟨hnc,v₀,j,hv₀,hj,hNv₀,hNj,heq⟩ := mem_lowNoncubeSupport (hS hv)
    have hvreal : norm v₀ ≤ (Real.log X)^(a:ℝ) := by
      simpa only [Real.rpow_natCast] using hNv₀
    have ht := hbound δ l b u V hδ hδone hwidth hl hb hbX hV hu hVF
      W hW hWi hWd v₀ j e hv₀ hj (by rwa [←heq]) hvreal
      (hNj.trans hCX) he hNe j₀ k₀ h Z Q early
    rw [heq]
    simpa only [Real.rpow_natCast] using ht
  have hcard : (S.card:ℝ) ≤ 324*(Real.log X)^a*C :=
    (Nat.cast_le.mpr (Finset.card_le_card hS)).trans
      (lowNoncubeSupport_card (pow_nonneg (zero_le_one.trans hlog) _) hC)
  have hmass :
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤
      (S.card:ℝ)*(K*b/(Real.log X)^(a+k+1))^2 := by
    calc
      _ ≤ ∑ _v ∈ S, (K*b/(Real.log X)^(a+k+1))^2 := by
        apply Finset.sum_le_sum
        intro v hv
        gcongr
        exact hterm v hv
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  exact low_core_mass_bound (a := a) (k := k) hC hlog hcard hmass

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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedCoreBlocks
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem angular_stopped_noncube_core_blocks
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
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
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤
        K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        K₁*((largeCoreDyadicIndices ((Real.log X)^a) B).card:ℝ)*B^(1/3:ℝ)*
          (b*(((Real.log X)^a)/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
  obtain ⟨K₀,hK₀,hlow⟩ := angular_stopped_low_core_mass (ι := ι) (d := 1)
    hpnt hEF ℓ hℓ hξ hξz hκ hH hF hJ a k ha
  obtain ⟨M,hM,henergy⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
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
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected
  let f := fun v => ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e‖^2
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
        angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e :=
      rfl
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedNoncubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem angular_stopped_noncube_mass_oai
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
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
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₀,K₁,hK₀,hK₁,hbound⟩ := angular_stopped_noncube_core_blocks (ι := ι)
    hpnt hEF ℓ hℓ hHuxley hξ hξz hκ hH hF hJ (4*(k+2)) k (by omega)
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

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.angular_stopped_noncube_mass_oai.{u_1} := @OAI.CubicFirstMoment.angular_stopped_noncube_mass_oai.{u_1}
