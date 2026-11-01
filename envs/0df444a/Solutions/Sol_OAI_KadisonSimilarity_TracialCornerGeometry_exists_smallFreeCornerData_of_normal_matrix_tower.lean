-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:57:28.55626+00:00
-- url     : https://prove2.me/submissions/2a362701-1499-4e48-8258-466550b86719

import Mathlib
import Definitions.Def_OAIQ075A036

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DyadicPhases
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic roots of unity, with a refinement estimate. These are the
scalar coefficients for the norm-convergent Haar-unitary construction. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial
open scoped BigOperators

theorem sum_range_pairs {B : Type*} [AddCommMonoid B] (f : ℕ → B) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), f i) =
      ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [add_assoc]

theorem sum_dyadicRank {B : Type*} [AddCommMonoid B] (n : ℕ) (f : ℕ → B) :
    (∑ i : DyadicIndex n, f (dyadicRank n i)) =
      ∑ j ∈ Finset.range (2 ^ n), f j := by
  induction n generalizing f with
  | zero =>
    change (∑ _i : Unit, f 0) = ∑ j ∈ Finset.range 1, f j
    simp
  | succ n ih =>
    change (∑ i : DyadicIndex n × Bool,
      f (2 * dyadicRank n i.1 + if i.2 then 1 else 0)) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [ih (fun j => f (2 * j + 1) + f (2 * j))]
    rw [pow_succ, Nat.mul_comm, sum_range_pairs]
    apply Finset.sum_congr rfl
    intro j _
    exact add_comm _ _

theorem norm_dyadicPhase (n : ℕ) (i : DyadicIndex n) : ‖dyadicPhase n i‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem dyadicPhase_eq_root_pow (n : ℕ) (i : DyadicIndex n) :
    dyadicPhase n i =
      Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ)) ^ dyadicRank n i := by
  rw [← Complex.exp_nat_mul]
  unfold dyadicPhase
  congr 1
  push_cast
  ring

theorem sum_dyadicPhase_pow_eq_zero (n k : ℕ) (hk : 0 < k) (hkn : k < 2 ^ n) :
    (∑ i : DyadicIndex n, dyadicPhase n i ^ k) = 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ))
  have hz : IsPrimitiveRoot z (2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  have hzk : z ^ k ≠ 1 := by
    intro he
    have hdiv := (hz.pow_eq_one_iff_dvd k).mp he
    exact (not_le_of_gt hkn) (Nat.le_of_dvd hk hdiv)
  have hzpow : (z ^ k) ^ (2 ^ n) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hs : (∑ j ∈ Finset.range (2 ^ n), (z ^ k) ^ j) = 0 := by
    have h := geom_sum_mul (z ^ k) (2 ^ n)
    rw [hzpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hzk)
  calc
    (∑ i : DyadicIndex n, dyadicPhase n i ^ k) =
        ∑ i : DyadicIndex n, (z ^ k) ^ dyadicRank n i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dyadicPhase_eq_root_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    _ = ∑ j ∈ Finset.range (2 ^ n), (z ^ k) ^ j :=
      sum_dyadicRank n (fun j => (z ^ k) ^ j)
    _ = 0 := hs

theorem norm_exp_phase_sub_le (s t : ℝ) :
    ‖Complex.exp ((s : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I)‖ ≤
      |s - t| := by
  have he : Complex.exp ((s : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I) =
      (Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) - 1) *
        Complex.exp ((t : ℂ) * Complex.I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem dyadicPhase_refine_bound (n : ℕ) (i : DyadicIndex (n + 1)) :
    ‖dyadicPhase (n + 1) i - dyadicPhase n i.1‖ ≤
      Real.pi * (1 / 2 : ℝ) ^ n := by
  apply (norm_exp_phase_sub_le _ _).trans
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  change |2 * Real.pi * (dyadicRank (n + 1) i : ℝ) / 2 ^ (n + 1) -
    2 * Real.pi * (dyadicRank n i.1 : ℝ) / 2 ^ n| ≤ _
  cases hb : i.2 <;> simp only [dyadicRank, hb, Bool.false_eq_true, ↓reduceIte,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, pow_succ]
  · have he : 2 * Real.pi * (2 * (dyadicRank n i.1 : ℝ) + 0) / (2 ^ n * 2) -
        2 * Real.pi * (dyadicRank n i.1 : ℝ) / 2 ^ n = 0 := by field_simp; ring
    rw [he, abs_zero]
    positivity
  · have he : 2 * Real.pi * (2 * (dyadicRank n i.1 : ℝ) + 1) / (2 ^ n * 2) -
        2 * Real.pi * (dyadicRank n i.1 : ℝ) / 2 ^ n = Real.pi / 2 ^ n := by
      field_simp
      ring
    rw [he, abs_of_nonneg (by positivity), div_pow, one_pow]
    exact le_of_eq (by ring)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DyadicCornerHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dyadic spectral sums form contractive unital star
homomorphisms into the original corner. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped BigOperators CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

attribute [local instance] OAI.KadisonSimilarity.dyadicAlgebra_closed
theorem norm_dyadicCornerHom_le (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    ‖dyadicCornerHom τ hdiff p n c‖ ≤ C :=
  (NonUnitalStarAlgHom.norm_apply_le (dyadicCornerHom τ hdiff p n) c).trans
    ((pi_norm_le_iff_of_nonneg hC).mpr hc)

theorem dyadicCornerHom_refine (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    dyadicCornerHom τ hdiff p (n + 1) (fun i => c i.1) =
      dyadicCornerHom τ hdiff p n c :=
  Subtype.ext (dyadicEval_refine τ hdiff p n c)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DyadicHaarUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Haar unitary in each corner of a diffuse finite tracial von Neumann
algebra, constructed as a norm limit of finite dyadic spectral sums. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped BigOperators Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

attribute [local instance] OAI.KadisonSimilarity.haarAlgebra_closed
theorem dyadicUnitaryApprox_mem (p : AlgebraProjection M) (n : ℕ) :
    dyadicUnitaryApprox τ hdiff p n ∈ unitary (CStarCorner p.val p.property) := by
  have hs : star (dyadicPhase n) * dyadicPhase n = 1 := by
    funext i
    change star (dyadicPhase n i) * dyadicPhase n i = 1
    rw [Complex.star_def, Complex.conj_mul', norm_dyadicPhase]
    norm_num
  have ht : dyadicPhase n * star (dyadicPhase n) = 1 := by
    rw [mul_comm, hs]
  apply Unitary.mem_iff.mpr
  constructor
  · simpa only [dyadicUnitaryApprox, map_mul, map_star, map_one] using
      congrArg (dyadicCornerHom τ hdiff p n) hs
  · simpa only [dyadicUnitaryApprox, map_mul, map_star, map_one] using
      congrArg (dyadicCornerHom τ hdiff p n) ht

theorem dyadicUnitaryApprox_step (p : AlgebraProjection M) (n : ℕ) :
    ‖dyadicUnitaryApprox τ hdiff p (n + 1) - dyadicUnitaryApprox τ hdiff p n‖ ≤
      Real.pi * (1 / 2 : ℝ) ^ n := by
  unfold dyadicUnitaryApprox
  rw [← dyadicCornerHom_refine τ hdiff p n, ← map_sub]
  exact norm_dyadicCornerHom_le τ hdiff p (n + 1) _ _ (by positivity)
    (dyadicPhase_refine_bound n)

theorem dyadicUnitaryApprox_cauchy (p : AlgebraProjection M) :
    CauchySeq (dyadicUnitaryApprox τ hdiff p) := by
  apply cauchySeq_of_le_geometric (1 / 2) Real.pi (by norm_num)
  intro n
  rw [dist_eq_norm, norm_sub_rev]
  exact dyadicUnitaryApprox_step τ hdiff p n

theorem trace_dyadicUnitaryApprox_pow (p : AlgebraProjection M) (n k : ℕ)
    (hk : 0 < k) (hkn : k < 2 ^ n) :
    dyadicCornerTrace τ p (dyadicUnitaryApprox τ hdiff p n ^ k) = 0 := by
  unfold dyadicUnitaryApprox
  rw [← map_pow]
  change τ.trace (dyadicEval τ hdiff p n (fun i => dyadicPhase n i ^ k)) = 0
  rw [dyadicEval_trace, ← Finset.sum_mul, sum_dyadicPhase_pow_eq_zero n k hk hkn,
    zero_mul]

include hdiff in
/-- The constructed corner unitary has every nonzero integer moment zero.
No Haar-unitary existence theorem is assumed. -/
theorem exists_dyadicCornerHaar (p : AlgebraProjection M) :
    ∃ z : unitary (CStarCorner p.val p.property),
      ∀ k : ℤ, k ≠ 0 → τ.trace (haarCornerPower z k) = 0 := by
  obtain ⟨a, ha, hlim⟩ := cauchySeq_tendsto_of_isComplete isClosed_unitary.isComplete
    (dyadicUnitaryApprox_mem τ hdiff p) (dyadicUnitaryApprox_cauchy τ hdiff p)
  let z : unitary (CStarCorner p.val p.property) := ⟨a, ha⟩
  have hpows (k : ℕ) (hk : 0 < k) : dyadicCornerTrace τ p (a ^ k) = 0 := by
    have hzero : ∀ᶠ n : ℕ in atTop,
        dyadicCornerTrace τ p (dyadicUnitaryApprox τ hdiff p n ^ k) = 0 := by
      filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
        (eventually_gt_atTop k)] with n hn
      exact trace_dyadicUnitaryApprox_pow τ hdiff p n k hk hn
    exact tendsto_nhds_unique ((dyadicCornerTrace τ p).continuous.tendsto _ |>.comp
      (hlim.pow k)) (tendsto_nhds_of_eventually_eq hzero)
  have hpos (k : ℕ) (hk : 0 < k) : τ.trace (haarCornerPower z (k : ℤ)) = 0 := by
    have hc := hpows k hk
    change τ.trace ((a ^ k : CStarCorner p.val p.property) : M.toStarSubalgebra) = 0 at hc
    simpa only [haarCornerPower, zpow_natCast, SubmonoidClass.coe_pow] using hc
  refine ⟨z, ?_⟩
  intro k hk
  cases k with
  | ofNat k =>
    have hk' : 0 < k := Nat.pos_of_ne_zero (fun h => hk (by simp [h]))
    exact hpos k hk'
  | negSucc k =>
    have hp : τ.trace (haarCornerPower z (k + 1 : ℕ)) = 0 := hpos (k + 1) (by omega)
    have hstar (x : M.toStarSubalgebra) : τ.trace (star x) = star (τ.trace x) := by
      change inner ℂ τ.vector (star (x : H →L[ℂ] H) τ.vector) =
        star (inner ℂ τ.vector ((x : H →L[ℂ] H) τ.vector))
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        ← inner_conj_symm]
      rfl
    rw [show Int.negSucc k = -((k + 1 : ℕ) : ℤ) by omega,
      ← star_haarCornerPower, hstar, hp, star_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteHalfProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small projection in an actual diffuse tracial von Neumann algebra
can be completed to trace one half.  The only projection-existence step
is the proved exact-trace subprojection theorem. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions
/-- Exact trace cutting in the orthogonal complement supplies the missing
part of a half-trace projection. -/
theorem exists_concreteHalfTraceProjectionData (τ : TracialRepresentation M)
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (e : M.toStarSubalgebra) (he : IsStarProjection e)
    {t : ℝ} (hetrace : τ.trace e = (t : ℂ)) (ht : t ≤ 1 / 2) :
    Nonempty (HalfTraceProjectionData (concreteTraceLinear τ) e) := by
  have hcomplement : τ.trace (1 - e) = (1 - t : ℝ) := by
    change concreteTraceLinear τ (1 - e) = _
    rw [map_sub, concreteTraceLinear_one, concreteTraceLinear_apply, hetrace]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
  have hr : 0 ≤ 1 / 2 - t := sub_nonneg.mpr ht
  have hrp : 1 / 2 - t ≤ (τ.trace (1 - e)).re := by
    rw [hcomplement, Complex.ofReal_re]
    linarith
  obtain ⟨q, hq, hleft, _, hqtrace⟩ :=
    Generator.Tracial.exists_exact_trace_subprojection τ hdiff (1 - e) he.one_sub
      (1 / 2 - t) hr hrp
  have heq : e * q = 0 := by
    have h : q - e * q = q := by simpa only [sub_mul, one_mul] using hleft
    exact sub_eq_self.mp h
  refine ⟨halfTraceProjectionDataOfOrthogonal (concreteTraceLinear τ) he hq heq
    hetrace ?_⟩
  change τ.trace q = 1 / 2 - (t : ℂ)
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using hqtrace

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SmallFreeCornerData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small projection, its full matrix frame, the containing half
projection, and the Haar unitary all belong to the same corner. The matrix
frame is constructed from the tower. Only trace cutting and the local Haar
existence statement are required for the two remaining choices. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

/-- The frame and its trace are chosen from an actual matrix stage. The
half-projection and Haar hypotheses are the two local diffuse-corner facts,
not any estimate for a commutator. -/
theorem exists_smallFreeCornerData (τ : P →ₗ[ℂ] ℂ) (V : P →ₗ[ℂ] H)
    (M : NestedTracialMatrices (A := I) τ V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ))
      Filter.atTop Filter.atTop)
    (half : ∀ (e : P), IsStarProjection e → ∀ t : ℝ,
      τ e = (t : ℂ) → t ≤ 1 / 2 → Nonempty (HalfTraceProjectionData τ e))
    (haar : ∀ (e : P) (he : IsStarProjection e) (t : ℝ),
      0 < t → τ e = (t : ℂ) →
      ∃ z : unitary (CStarCorner e he), HaarCornerMoments τ z t)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData τ s) := by
  obtain ⟨n, hn, t, ht, hts, F, hF⟩ :=
    M.exists_small_trace_frame hsize (lt_min hs (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Q⟩ := half F.corner F.corner_projection t hF
    (le_of_lt (lt_of_lt_of_le hts (min_le_right _ _)))
  obtain ⟨z, hz⟩ := haar F.corner F.corner_projection t ht hF
  exact ⟨⟨n, hn, F, t, ht, lt_of_lt_of_le hts (min_le_left _ _), hF, Q, z, hz⟩⟩

section Concrete

open UltrapowerBridge

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {N : VonNeumannAlgebra K}

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_1
/-- Package the cited Haar statement in precisely the normalization used
by the propagation theorem. -/
theorem exists_concreteHaarCorner (τ : TracialRepresentation N)
    (published : ThielDiffuseCornerHaarInput τ)
    (q : N.toStarSubalgebra) (hq : IsStarProjection q)
    {t : ℝ} (ht : 0 < t) (htrace : τ.trace q = (t : ℂ)) :
    ∃ z : unitary (CStarCorner q hq),
      HaarCornerMoments (concreteTraceLinear τ) z t := by
  obtain ⟨z, hz⟩ := published q hq (by simpa only [htrace, Complex.ofReal_re] using ht)
  refine ⟨z, ?_⟩
  intro k hk
  change (t : ℂ)⁻¹ * τ.trace (haarCornerPower z k) = 0
  rw [hz k hk, mul_zero]

/-- Trace cutting supplies the half projection in the concrete diffuse
algebra, and the Haar input supplies the corner unitary. -/
theorem exists_concreteSmallFreeCornerData (τ : TracialRepresentation N)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (published : ThielDiffuseCornerHaarInput τ)
    (V : N.toStarSubalgebra →ₗ[ℂ] H)
    (M : NestedTracialMatrices (A := I) (concreteTraceLinear τ) V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ))
      Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData (concreteTraceLinear τ) s) :=
  exists_smallFreeCornerData (concreteTraceLinear τ) V M hsize
    (fun e he _t htrace ht => exists_concreteHalfTraceProjectionData τ hdiff e he htrace ht)
    (fun e he _t ht htrace => exists_concreteHaarCorner τ published e he ht htrace) hs

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ConcreteHaarDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise diffuse-corner Haar input used by the free-corner argument
is supplied by the constructed dyadic unitary. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K}

theorem thielDiffuseCornerHaarInput (τ : TracialRepresentation N)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) : ThielDiffuseCornerHaarInput τ := by
  intro q hq _
  exact exists_dyadicCornerHaar τ hdiff ⟨q, hq⟩

attribute [local instance] OAI.KadisonSimilarity.concreteHaar_closed
/-- A diffuse concrete source supplies the small corner, containing half
projection and Haar unitary with no independent Haar existence premise. -/
theorem exists_concreteSmallFreeCornerData_of_diffuse
    (τ : TracialRepresentation N)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q)
    {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Nonempty (I j)]
    (V : N.toStarSubalgebra →ₗ[ℂ] H)
    (M : NestedTracialMatrices (A := I) (concreteTraceLinear τ) V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ))
      Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData (concreteTraceLinear τ) s) :=
  exists_concreteSmallFreeCornerData τ hdiff (thielDiffuseCornerHaarInput τ hdiff)
    V M hsize hs

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixDiffuse
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily small full-matrix corners and comparison split every
nonzero projection in the source algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
/-- A nonzero projection contains a proper nonzero subprojection. -/
theorem proper_subprojection_of_matrix_tower
    (hf : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (p : P) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : P, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  have hv : G.vector p ≠ 0 := by
    intro h
    exact hp0 (hf (h.trans (map_zero G.vector).symm))
  have hpnorm : ‖G.vector p‖ ^ 2 = (G.trace p).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.inner_vector,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    rfl
  have hppos : 0 < (G.trace p).re := by
    rw [← hpnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨n, _, t, ht, htp, F, hF⟩ := M.exists_small_trace_frame hsize hppos
  have hFp : (G.trace F.corner).re ≤ (G.trace p).re := by
    rw [hF, Complex.ofReal_re]
    exact htp.le
  obtain ⟨v, hv, hpv⟩ := comparison p F.corner hp F.corner_projection hFp
  let q := v * star v
  have hq : IsStarProjection q := range_projection_of_initial_projection
    F.corner v F.corner_projection hv
  have hτq : G.trace q = (t : ℂ) := by
    change G.trace (v * star v) = _
    rw [G.tracial, hv, hF]
  have hq0 : q ≠ 0 := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, map_zero] at hh
    simp only [Complex.zero_re, Complex.ofReal_re] at hh
    exact (ne_of_gt ht) hh.symm
  have hqp : q ≠ p := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, Complex.ofReal_re] at hh
    exact (ne_of_lt htp) hh.symm
  refine ⟨q, hq, hq0, hqp, hpv, ?_⟩
  have hpq : p * q = q := hpv
  have h := congrArg star hpq
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalSmallCorners
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct small diffuse corners in the original algebra through its
actual faithful normal range, then transport the entire frame back. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

local instance normalCorners_closed (N : VonNeumannAlgebra H) :
    IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed N

include M in
/-- The normal represented source has no nonzero minimal projection. -/
theorem normalRange_diffuse_of_matrix_tower
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop) :
    ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q := by
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have comparison := G.projectionComparison_of_normal_range h1 hf N hN
    (G.scalar_center_of_matrix_tower M hf)
  intro p hp hp0
  let a := e.symm p
  have ha : IsStarProjection a := hp.map e.symm
  have hea : e a = p := e.apply_symm_apply p
  have ha0 : a ≠ 0 := by
    intro h
    apply hp0
    rw [← hea, h, map_zero]
  obtain ⟨q, hq, hq0, hqa, haq, hqa'⟩ :=
    G.proper_subprojection_of_matrix_tower M hf comparison hsize a ha ha0
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hq0 (e.injective (h.trans (map_zero e).symm))
  · intro h
    exact hqa (e.injective (h.trans hea.symm))
  · rw [← hea, ← map_mul, haq]
  · rw [← hea, ← map_mul, hqa']

include M in
/-- All small-frame, half-projection and Haar data are constructed together. -/
theorem exists_smallFreeCornerData_of_normal_matrix_tower_oai
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra H) (hN : G.left.range = N.toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData G.trace s) := by
  let τ := G.normalTracialRepresentation h1 hf N hN
  let e := equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  have hdiff := G.normalRange_diffuse_of_matrix_tower M h1 hf N hN hsize
  obtain ⟨Q⟩ := exists_concreteSmallFreeCornerData_of_diffuse τ hdiff (Generator.Tracial.baseVector τ)
    (G.normalMatrixTower M h1 hf N hN) hsize hs
  have htrace (a : N.toStarSubalgebra) : G.trace (e.symm a) = concreteTraceLinear τ a := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm a)
    change τ.trace (e (e.symm a)) = G.trace (e.symm a) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  exact ⟨Q.transport e.symm.toStarAlgHom (concreteTraceLinear τ) G.trace htrace⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower_oai.{u_1, u_2, u_3} := @OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower_oai.{u_1, u_2, u_3}
