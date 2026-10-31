-- Prove2me | solution 1 for OAI.CubicFirstMoment.bounded_cubic_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:53:47.376383+00:00
-- url     : https://prove2.me/submissions/ba509c55-6c28-4e74-928c-7b8612522f21

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A010
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma finiteCubicBound_nonneg (S H : Finset Eisenstein) : 0 ≤ finiteCubicBound S H :=
  sq_nonneg _

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

private lemma euclideanConj_norm {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖euclideanConj v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, euclideanConj]

private lemma matrixHilbertOperator_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (v : EuclideanSpace ℂ κ) :
    matrixHilbertOperator (A.map star) v =
      euclideanConj (matrixHilbertOperator A (euclideanConj v)) := by
  apply PiLp.ext
  intro i
  change (∑ j, star (A i j) * v j) = star (∑ j, A i j * star (v j))
  simp [star_sum, star_mul, mul_comm]

private lemma matrixHilbertOperator_conj_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator (A.map star)‖ ≤ ‖matrixHilbertOperator A‖ := by
  apply (ContinuousLinearMap.opNorm_le_iff (f := matrixHilbertOperator (A.map star))
    (_root_.norm_nonneg (matrixHilbertOperator A))).mpr
  intro v
  rw [matrixHilbertOperator_conj, euclideanConj_norm]
  simpa only [euclideanConj_norm] using
    (matrixHilbertOperator A).le_opNorm (euclideanConj v)

private lemma matrixHilbertOperator_conj_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator (A.map star)‖ = ‖matrixHilbertOperator A‖ := by
  apply le_antisymm (matrixHilbertOperator_conj_norm_le A)
  have he : (A.map star).map star = A := by ext i j; simp
  have h := matrixHilbertOperator_conj_norm_le (A.map star)
  rwa [he] at h

private lemma matrixHilbertOperator_transpose_norm {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator A.transpose‖ = ‖matrixHilbertOperator A‖ := by
  have hc : A.transpose = (A.conjTranspose).map star := by
    ext i j
    simp
  rw [hc, matrixHilbertOperator_conj_norm]
  change ‖LinearMap.toContinuousLinearMap A.conjTranspose.toEuclideanLin‖ = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem finiteCubicBound_symm (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hH : ∀ h ∈ H, primary h) :
    finiteCubicBound S H = finiteCubicBound H S := by
  let A : Matrix H S ℂ := fun h a => cubicSymbol a.val h.val
  have hmat : (fun (a : S) (h : H) => cubicSymbol h.val a.val) = A.transpose := by
    funext a h
    exact cubic_reciprocity (hH h.val h.property) (hS a.val a.property)
  unfold finiteCubicBound finiteCubicOperator
  rw [hmat]
  exact congrArg (fun x : ℝ => x^2) (matrixHilbertOperator_transpose_norm A).symm

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma mem_cubeDyadTriples {j i t c : ℕ} :
    (i,t,c) ∈ cubeDyadTriples j ↔ i+2*t+3*c ≤ j+1 := by
  simp [cubeDyadTriples,Finset.mem_product,Finset.mem_range]
  omega

lemma cubeDyadTriples_card (j : ℕ) : (cubeDyadTriples j).card ≤ (j+2)^3 := by
  have h := Finset.card_filter_le (s := (Finset.range (j+2)).product
    ((Finset.range (j+2)).product (Finset.range (j+2))))
    (p := fun z : ℕ×ℕ×ℕ => z.1+2*z.2.1+3*z.2.2 ≤ j+1)
  simpa [cubeDyadTriples,Finset.card_product,Finset.card_range,pow_succ,mul_assoc] using h

lemma frequencyDyad_subset_cubeCover (j : ℕ) : frequencyDyad j ⊆ cubeFrequencyCover j := by
  intro n hn
  obtain ⟨r,s,t,c,hr0,hr,hs,ht,hss,hst,hcop,hc0,he⟩ :=
    full_cube_decomposition (mem_frequencyDyad.mp hn).1
  let i := Nat.log 2 (normNat s)
  let l := Nat.log 2 (normNat t)
  let k := Nat.log 2 (normNat c)
  have hsi : s ∈ frequencyDyad i := mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩
  have htl : t ∈ frequencyDyad l := mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩
  have hck : c ∈ frequencyDyad k := mem_frequencyDyad.mpr ⟨hc0,rfl⟩
  have hprod : (2 : ℝ)^i*((2 : ℝ)^l)^2*((2 : ℝ)^k)^3 ≤ norm n := by
    calc
      _ ≤ norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have htn := norm_nonneg t
        have hcn := norm_nonneg c
        gcongr <;> exact (frequencyDyad_norm ‹_›).1
      _ ≤ norm r*norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have hcn := norm_nonneg c
        have hprim : 0 ≤ norm s*(norm t)^2*(norm c)^3 := by positivity [norm_nonneg s]
        have hmul := le_mul_of_one_le_left hprim (one_le_norm hr0)
        nlinarith
      _ = norm n := by rw [he]; simp only [norm_mul_eq,eisenstein_norm_pow]
  have hexp : i+2*l+3*k ≤ j+1 := by
    apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    have heq : (2 : ℝ)^(i+2*l+3*k) = 2^i*(2^l)^2*(2^k)^3 := by
      simp only [pow_add,pow_mul,mul_comm 2 l,mul_comm 3 k]
    rw [heq]
    exact hprod.trans ((frequencyDyad_norm hn).2.trans_eq (by rw [pow_succ]; ring))
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,l,k),mem_cubeDyadTriples.mpr hexp,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r,mem_nonzeroNormBall.mpr ⟨hr,hr0⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨s*t^2*c^3,Finset.mem_image.mpr ⟨(s,t,c),?_ ,rfl⟩,?_⟩
  · exact Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨hsi,hs,hss⟩,
      Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨htl,ht,hst⟩,hck⟩⟩
  · rw [he]; ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveExponent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cube and dual bounds under a sieve exponent. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dyadic_polynomial_small_power (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ((j : ℝ)+2)^d ≤ C*((2 : ℝ)^j)^ε := by
  let r : ℝ := (2^ε)⁻¹
  have hp : (1 : ℝ) < 2^ε := Real.one_lt_rpow (by norm_num) hε
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hp
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d (r := r) (by simpa only [Real.norm_eq_abs,abs_of_pos hr] using hr1)
  let D : ℝ := (∑' n : ℕ, (n : ℝ)^d*r^n)+1
  have hD : 0 < D := by
    have hh : 0 ≤ ∑' n : ℕ, (n : ℝ)^d*r^n := tsum_nonneg (fun n => by positivity)
    dsimp [D]; linarith
  refine ⟨D*(2^ε)^2,by positivity,?_⟩
  intro j
  have hh := hs.le_tsum (j+2) (fun n _ => by positivity)
  have hh' : (((j : ℝ)+2)^d*r^j)*r^2 ≤ D := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,pow_add,mul_assoc] using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  have he : (2^ε)^j = ((2 : ℝ)^j)^ε := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have he' : r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = 1 := by
    rw [← he]
    dsimp [r]
    rw [inv_pow,inv_pow]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2^ε)^2*((2 : ℝ)^j)^ε)
  have he'' : ((j : ℝ)+2)^d*r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = ((j : ℝ)+2)^d := by
    calc
      _ = ((j : ℝ)+2)^d*(r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε)) := by ring
      _ = _ := by rw [he',mul_one]
  rw [he''] at hmul
  exact hmul.trans_eq (by ring)

lemma squarefreePrimaryDyad_card_le (j : ℕ) :
    ((squarefreePrimaryDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (frequencyDyad_card_le j)

lemma cubeDyad_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2 : ℝ)^z.1*((2 : ℝ)^z.2.1)^2*((2 : ℝ)^z.2.2)^3 ≤ 2*(2 : ℝ)^j := by
  have hh := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mem_cubeDyadTriples.mp hz))
  calc
    _ = (2 : ℝ)^(z.1+2*z.2.1+3*z.2.2) := by
      simp only [pow_add,pow_mul,mul_comm 2 z.2.1,mul_comm 3 z.2.2]
    _ ≤ 2^(j+1) := hh
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_scaled_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2*(2 : ℝ)^z.1)*(2*(2 : ℝ)^z.2.1)^2*(2*(2 : ℝ)^z.2.2)^3 ≤ 128*(2 : ℝ)^j := by
  have h := mul_le_mul_of_nonneg_left (cubeDyad_sizes hz) (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith only [h]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveImprovement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification, iteration to exponent four-thirds and the cubic large sieve. -/

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma small_four_thirds_le_mixed {M N : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  calc
    _ = (N*N)^(2/3 : ℝ) := by
      rw [← pow_two,← Real.rpow_natCast_mul hN]
      norm_num
    _ ≤ _ := by gcongr

theorem finiteCubicBound_sharp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := sieveExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM).le
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  have hmixed : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
  rcases le_total N M with hNM | hMN
  · have hs := small_four_thirds_le_mixed hN0 hNM
    have hh : M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    exact (hbound S H M N hM hN hS hH).trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  · rw [finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun b hb => (hH b hb).1)]
    have hs := small_four_thirds_le_mixed hM0 hMN
    rw [mul_comm N M] at hs
    have hh : N+(M*N)^(2/3 : ℝ)+M^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    have hb := hbound H S N M hN hM hH hS
    rw [mul_comm N M] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_InnerExtension
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma innerCubeBlock_fixed_mass (P S : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ s ∈ S, primary s)
    (r : Eisenstein) (v : Eisenstein → ℂ) :
    (∑ a ∈ P, ‖∑ s ∈ S, v s*cubicSymbol a (r*s)‖^2) ≤
      finiteCubicBound S P * ∑ s ∈ S, ‖v s‖^2 := by
  apply le_trans _ (finiteCubicBound_controls_mass S P v)
  apply Finset.sum_le_sum
  intro a ha
  have he : (∑ s ∈ S, v s*cubicSymbol a (r*s)) =
      cubicSymbol a r * ∑ s ∈ S, v s*cubicSymbol s a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [cubicSymbol_mul_upper (hP a ha),cubic_reciprocity (hP a ha) (hS s hs)]
    ring
  rw [he,norm_mul,mul_pow]
  apply mul_le_of_le_one_left (sq_nonneg _)
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hP a ha) r) 2).trans_eq (by norm_num)

theorem innerCubeBlock_mass (P S T C : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hS : ∀ s ∈ S, primary s)
    (r : Eisenstein) (v : Eisenstein → Eisenstein → Eisenstein → ℂ)
    (D : ℝ) (_hD : 0 ≤ D) (hv : ∀ s ∈ S, ∀ t ∈ T, ∀ c ∈ C, ‖v s t c‖ ≤ D) :
    (∑ a ∈ P, ‖∑ t ∈ T, ∑ c ∈ C, ∑ s ∈ S,
      v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2) ≤
      ((T.card : ℝ)*C.card)^2 * finiteCubicBound S P * S.card * D^2 := by
  have hrow (t : Eisenstein) (ht : t ∈ T) (c : Eisenstein) (hc : c ∈ C) :
      (∑ a ∈ P, ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2) ≤
      finiteCubicBound S P * S.card * D^2 := by
    have he : ∀ s : Eisenstein, r*(s*t^2*c^3) = (r*t^2*c^3)*s := by intro s; ring
    simp_rw [he]
    apply (innerCubeBlock_fixed_mass P S hP hS _ (fun s => v s t c)).trans
    have hh : (∑ s ∈ S, ‖v s t c‖^2) ≤ (S.card : ℝ)*D^2 := by
      calc
        _ ≤ ∑ s ∈ S, D^2 := Finset.sum_le_sum (fun s hs =>
          pow_le_pow_left₀ (_root_.norm_nonneg _) (hv s hs t ht c hc) 2)
        _ = _ := by simp
    exact (mul_le_mul_of_nonneg_left hh (finiteCubicBound_nonneg _ _)).trans_eq (by ring)
  have htriangle (a : Eisenstein) :
      ‖∑ t ∈ T, ∑ c ∈ C, ∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 ≤
      ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C,
        ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 := by
    simpa only [Finset.product_eq_sprod,Finset.sum_product,Finset.card_product,Nat.cast_mul] using
      complex_norm_sum_sq_le (T.product C)
        (fun z => ∑ s ∈ S, v s z.1 z.2*cubicSymbol a (r*(s*z.1^2*z.2^3)))
  calc
    _ ≤ ∑ a ∈ P, ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C,
        ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 :=
      Finset.sum_le_sum (fun a _ => htriangle a)
    _ = ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C, ∑ a ∈ P,
        ‖∑ s ∈ S, v s t c*cubicSymbol a (r*(s*t^2*c^3))‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm (s := P) (t := T)]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ ≤ ((T.card : ℝ)*C.card)*∑ t ∈ T, ∑ c ∈ C,
        finiteCubicBound S P * S.card * D^2 := by
      gcongr with t ht c hc
      exact hrow t ht c hc
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

lemma finiteCoverCoefficient_norm_le {ι : Type*} (I : Finset ι) (f : ι → Eisenstein)
    (H : Finset Eisenstein) (v : Eisenstein → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ n ∈ H, ‖v n‖ ≤ D) {x : ι} (hx : x ∈ I) :
    ‖finiteCoverCoefficient I f H v x‖ ≤ D := by
  unfold finiteCoverCoefficient
  split_ifs with h
  · have hc : 1 ≤ (I.filter (fun y => f y = f x)).card :=
      Finset.one_le_card.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_self (_root_.norm_nonneg _) (by exact_mod_cast hc)).trans (hv _ h)
  · simpa using hD

lemma finiteCoverCoefficient_sum {ι : Type*} (I : Finset ι) (f : ι → Eisenstein)
    (H : Finset Eisenstein) (hcover : H ⊆ I.image f)
    (v k : Eisenstein → ℂ) :
    (∑ x ∈ I, finiteCoverCoefficient I f H v x * k (f x)) =
      ∑ n ∈ H, v n*k n := by
  classical
  have he : (∑ x ∈ I, finiteCoverCoefficient I f H v x * k (f x)) =
      ∑ x ∈ I with f x ∈ H,
        (v (f x) / ((I.filter (fun y => f y = f x)).card : ℂ))*k (f x) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [finiteCoverCoefficient,ite_mul,zero_mul]
  rw [he,← Finset.sum_fiberwise_eq_sum_filter' I H f
    (fun n => (v n / ((I.filter (fun y => f y = n)).card : ℂ))*k n)]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : (I.filter (fun y => f y = n)).card ≠ 0 := by
    obtain ⟨x,hx,hfx⟩ := Finset.mem_image.mp (hcover hn)
    exact Finset.card_ne_zero.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hfx⟩⟩
  have hc' : ((I.filter (fun y => f y = n)).card : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [Finset.sum_const,nsmul_eq_mul]
  field_simp

lemma frequencyDyad_subset_innerCubeImage (j : ℕ) :
    frequencyDyad j ⊆ (innerCubeIndices j).image innerCubeValue := by
  intro n hn
  have hh := frequencyDyad_subset_cubeCover j hn
  obtain ⟨z,hz,hm⟩ := Finset.mem_biUnion.mp hh
  obtain ⟨r,hr,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hm
  obtain ⟨⟨s,t,c⟩,hstc,hem⟩ := Finset.mem_image.mp hm
  obtain ⟨hs,htc⟩ := Finset.mem_product.mp hstc
  obtain ⟨ht,hc⟩ := Finset.mem_product.mp htc
  refine Finset.mem_image.mpr ⟨⟨z,r,s,t,c⟩,?_,?_⟩
  · exact Finset.mem_sigma.mpr ⟨hz,Finset.mem_product.mpr ⟨hr,
      Finset.mem_product.mpr ⟨hs,Finset.mem_product.mpr ⟨ht,hc⟩⟩⟩⟩
  · dsimp [innerCubeValue]
    rw [← he,← hem]

lemma innerCubeCoefficient_sum (j : ℕ) (v : Eisenstein → ℂ) (a : Eisenstein) :
    (∑ n ∈ frequencyDyad j, v n*cubicSymbol a n) =
      ∑ z ∈ cubeDyadTriples j, ∑ r ∈ nonzeroNormBall 729,
        innerCubeBlockSum j v a z r := by
  rw [← finiteCoverCoefficient_sum (innerCubeIndices j) innerCubeValue (frequencyDyad j)
    (frequencyDyad_subset_innerCubeImage j) v (cubicSymbol a)]
  simp only [innerCubeIndices,Finset.sum_sigma,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only [innerCubeBlockSum,innerCubeValue,innerCubeCoefficient]
  rw [Finset.sum_comm (s := squarefreePrimaryDyad z.1) (t := squarefreePrimaryDyad z.2.1)]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.sum_comm

lemma innerCubeCoefficient_block_mass (P : Finset Eisenstein) (hP : ∀ a ∈ P, primary a)
    (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D)
    (z : ℕ×ℕ×ℕ) (hz : z ∈ cubeDyadTriples j) (r : Eisenstein)
    (hr : r ∈ nonzeroNormBall 729) :
    (∑ a ∈ P, ‖innerCubeBlockSum j v a z r‖^2) ≤
      (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
        finiteCubicBound (squarefreePrimaryDyad z.1) P *
          (squarefreePrimaryDyad z.1).card * D^2 := by
  apply innerCubeBlock_mass P _ _ _ hP
    (fun s hs => (mem_squarefreePrimaryDyad.mp hs).2.1) r
    (fun s t c => innerCubeCoefficient j v ⟨z,r,s,t,c⟩) D hD
  intro s hs t ht c hc
  apply finiteCoverCoefficient_norm_le _ _ _ _ D hD hv
  exact Finset.mem_sigma.mpr ⟨hz,Finset.mem_product.mpr ⟨hr,
    Finset.mem_product.mpr ⟨hs,Finset.mem_product.mpr ⟨ht,hc⟩⟩⟩⟩

lemma complex_mass_sum_sq_le {ι κ : Type*} (I : Finset ι) (P : Finset κ)
    (F : κ → ι → ℂ) :
    (∑ a ∈ P, ‖∑ i ∈ I, F a i‖^2) ≤
      (I.card : ℝ)*∑ i ∈ I, ∑ a ∈ P, ‖F a i‖^2 := by
  calc
    _ ≤ ∑ a ∈ P, (I.card : ℝ)*∑ i ∈ I, ‖F a i‖^2 :=
      Finset.sum_le_sum (fun a _ => complex_norm_sum_sq_le I (F a))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem innerCubeCover_mass (P : Finset Eisenstein) (hP : ∀ a ∈ P, primary a)
    (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) :
    (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol a n‖^2) ≤
      (cubeDyadTriples j).card * ((nonzeroNormBall 729).card : ℝ)^2 *
      ∑ z ∈ cubeDyadTriples j,
        (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
          finiteCubicBound (squarefreePrimaryDyad z.1) P *
            (squarefreePrimaryDyad z.1).card * D^2 := by
  have htriangle := complex_mass_sum_sq_le
    ((cubeDyadTriples j).product (nonzeroNormBall 729)) P
    (fun a q => innerCubeBlockSum j v a q.1 q.2)
  simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.card_product,Nat.cast_mul]
    at htriangle
  simp_rw [innerCubeCoefficient_sum j v]
  apply htriangle.trans
  calc
    _ ≤ ((cubeDyadTriples j).card : ℝ)*(nonzeroNormBall 729).card *
        ∑ z ∈ cubeDyadTriples j, ∑ r ∈ nonzeroNormBall 729,
        (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
          finiteCubicBound (squarefreePrimaryDyad z.1) P *
            (squarefreePrimaryDyad z.1).card * D^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun z hz => Finset.sum_le_sum (fun r hr =>
        innerCubeCoefficient_block_mass P hP j v D hD hv z hz r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]; ring

theorem innerCubeBlock_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      ∀ (j : ℕ) (z : ℕ×ℕ×ℕ), z ∈ cubeDyadTriples j →
        (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
          finiteCubicBound (squarefreePrimaryDyad z.1) P *
            (squarefreePrimaryDyad z.1).card ≤
        C*(N*(128*(2 : ℝ)^j))^ε*(128*(2 : ℝ)^j)*
          (N+128*(2 : ℝ)^j+(N*(128*(2 : ℝ)^j))^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hsharp⟩ := finiteCubicBound_sharp ε hε
  refine ⟨18^5*C,by positivity,?_⟩
  intro P N hN hP j z hz
  let S : ℝ := 2*(2 : ℝ)^z.1
  let T : ℝ := 2*(2 : ℝ)^z.2.1
  let K : ℝ := 2*(2 : ℝ)^z.2.2
  let J : ℝ := 128*(2 : ℝ)^j
  have htwo (i : ℕ) : (1 : ℝ) ≤ 2*2^i := by
    have hh : (1 : ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
    linarith
  have hS : 1 ≤ S := htwo _
  have hT : 1 ≤ T := htwo _
  have hK : 1 ≤ K := htwo _
  have hp : S*T^2*K^3 ≤ J := cube_scaled_sizes hz
  have hSJ : S ≤ J := by
    apply le_trans _ hp
    exact (le_mul_of_one_le_right (by positivity : 0 ≤ S) (one_le_pow₀ hT)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hK))
  have hsf : ∀ s ∈ squarefreePrimaryDyad z.1,
      primary s ∧ Squarefree s ∧ norm s ≤ S := by
    intro s hs
    exact ⟨(mem_squarefreePrimaryDyad.mp hs).2.1,(mem_squarefreePrimaryDyad.mp hs).2.2,
      (frequencyDyad_norm (mem_squarefreePrimaryDyad.mp hs).1).2⟩
  have hb : finiteCubicBound (squarefreePrimaryDyad z.1) P ≤
      C*(N*J)^ε*(N+J+(N*J)^(2/3 : ℝ)) := by
    apply (hsharp _ _ N S hN hS hsf hP).trans
    gcongr
  have hcardS : ((squarefreePrimaryDyad z.1).card : ℝ) ≤ 18*S := by
    dsimp [S]; nlinarith [squarefreePrimaryDyad_card_le z.1]
  have hcardT : ((squarefreePrimaryDyad z.2.1).card : ℝ) ≤ 18*T := by
    dsimp [T]; nlinarith [squarefreePrimaryDyad_card_le z.2.1]
  have hcardK : ((frequencyDyad z.2.2).card : ℝ) ≤ 18*K := by
    dsimp [K]; nlinarith [frequencyDyad_card_le z.2.2]
  have hf : (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
      (squarefreePrimaryDyad z.1).card ≤ 18^5*J := by
    calc
      _ ≤ ((18*T)*(18*K))^2*(18*S) := by gcongr
      _ = 18^5*(S*T^2*K^2) := by ring
      _ ≤ 18^5*(S*T^2*K^3) := by
        gcongr
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  calc
    _ = ((((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card)^2 *
        (squarefreePrimaryDyad z.1).card)*finiteCubicBound (squarefreePrimaryDyad z.1) P := by ring
    _ ≤ (18^5*J)*(C*(N*J)^ε*(N+J+(N*J)^(2/3 : ℝ))) :=
      mul_le_mul hf hb (finiteCubicBound_nonneg _ _) (by positivity)
    _ = _ := by dsimp [J]; ring

theorem cubic_inner_extension_scaled {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      ∀ (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol a n‖^2) ≤
        C*(N*(128*(2 : ℝ)^j))^ε*(128*(2 : ℝ)^j)*
          (N+128*(2 : ℝ)^j+(N*(128*(2 : ℝ)^j))^(2/3 : ℝ))*D^2 := by
  obtain ⟨B,hB,hblock⟩ := innerCubeBlock_sharp (show 0 < ε/2 by linarith)
  obtain ⟨E,hE,hpoly⟩ := dyadic_polynomial_small_power 6 (show 0 < ε/2 by linarith)
  let R : ℝ := (nonzeroNormBall 729).card
  refine ⟨(R+1)^2*B*E,by dsimp [R]; positivity,?_⟩
  intro P N hN hP j v D hD hv
  let J : ℝ := 128*(2 : ℝ)^j
  let F : ℝ := N+J+(N*J)^(2/3 : ℝ)
  have hJpos : 0 < J := by dsimp [J]; positivity
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR' : R ≤ R+1 := by linarith
  have hcount : ((cubeDyadTriples j).card : ℝ)^2 ≤ E*J^(ε/2) := by
    have hc : ((cubeDyadTriples j).card : ℝ) ≤ ((j : ℝ)+2)^3 := by
      exact_mod_cast cubeDyadTriples_card j
    calc
      _ ≤ (((j : ℝ)+2)^3)^2 := by gcongr
      _ = ((j : ℝ)+2)^6 := by ring
      _ ≤ E*((2 : ℝ)^j)^(ε/2) := hpoly j
      _ ≤ _ := by
        gcongr
        dsimp [J]
        have hh : (0 : ℝ) ≤ 2^j := by positivity
        linarith
  have heps : J^(ε/2)*(N*J)^(ε/2) ≤ (N*J)^ε := by
    calc
      _ ≤ (N*J)^(ε/2)*(N*J)^(ε/2) := by
        gcongr
        exact le_mul_of_one_le_left hJpos.le hN
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hh := innerCubeCover_mass P (fun a ha => (hP a ha).1) j v D hD hv
  apply hh.trans
  calc
    _ ≤ (cubeDyadTriples j).card * R^2 *
        ∑ z ∈ cubeDyadTriples j, B*(N*J)^(ε/2)*J*F*D^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right (hblock P N hN hP j z hz) (sq_nonneg D)
    _ = ((cubeDyadTriples j).card : ℝ)^2 * R^2 * B*(N*J)^(ε/2)*J*F*D^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ (E*J^(ε/2)) * (R+1)^2 * B*(N*J)^(ε/2)*J*F*D^2 := by
      gcongr
    _ = ((R+1)^2*B*E)* (J^(ε/2)*(N*J)^(ε/2))*J*F*D^2 := by ring
    _ ≤ ((R+1)^2*B*E)* (N*J)^ε*J*F*D^2 := by gcongr
    _ = _ := rfl

theorem cubic_inner_extension {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      ∀ (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol a n‖^2) ≤
        C*(N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ))*D^2 := by
  obtain ⟨C,hC,h⟩ := cubic_inner_extension_scaled hε
  refine ⟨C*128^ε*128^2,by positivity,?_⟩
  intro P N hN hP j v D hD hv
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hJ0 : 0 < (2 : ℝ)^j := by positivity
  have hp : (128 : ℝ)^(2/3 : ℝ) ≤ 128 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (2/3 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hm : (N*(128*(2 : ℝ)^j))^(2/3 : ℝ) ≤
      128*((N*(2 : ℝ)^j)^(2/3 : ℝ)) := by
    rw [show N*(128*(2 : ℝ)^j) = 128*(N*(2 : ℝ)^j) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hb : N+128*(2 : ℝ)^j+(N*(128*(2 : ℝ)^j))^(2/3 : ℝ) ≤
      128*(N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)) := by nlinarith
  have he : (N*(128*(2 : ℝ)^j))^ε = 128^ε*(N*(2 : ℝ)^j)^ε := by
    rw [show N*(128*(2 : ℝ)^j) = 128*(N*(2 : ℝ)^j) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  apply (h P N hN hP j v D hD hv).trans
  rw [he]
  calc
    _ ≤ C*(128^ε*(N*(2 : ℝ)^j)^ε)*(128*(2 : ℝ)^j)*
        (128*(N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)))*D^2 := by gcongr
    _ = _ := by ring

end CubicFirstMoment
end
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpPrimaryMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp bounded-coefficient cubic sieve, specialized to actual
primary convolutions. The pointwise divisor bound is essential here. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma finite_polynomial_dyad_partition (H : Finset Eisenstein)
    (hH : ∀ n ∈ H, n ≠ 0) (v : Eisenstein → ℂ) (a : Eisenstein) :
    (∑ n ∈ H, v n*cubicSymbol a n) =
      ∑ j ∈ H.image (fun n => Nat.log 2 (normNat n)),
        ∑ n ∈ frequencyDyad j, (if n ∈ H then v n else 0)*cubicSymbol a n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun n hn => Finset.mem_image_of_mem (fun n => Nat.log 2 (normNat n)) hn)]
  apply Finset.sum_congr rfl
  intro j hj
  have hsub : H.filter (fun n => Nat.log 2 (normNat n) = j) ⊆ frequencyDyad j := by
    intro n hn
    exact mem_frequencyDyad.mpr ⟨hH n (Finset.mem_filter.mp hn).1,(Finset.mem_filter.mp hn).2⟩
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [(Finset.mem_filter.mp hn).1,ite_true, if_true]
  · intro n hn hnot
    have hnH : n ∉ H := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨h,(mem_frequencyDyad.mp hn).2⟩)
    simp [hnH]

/-- Sharp cutoff form of the proved bounded-coefficient inner extension.
The coefficient support may contain cubes and need not be squarefree. -/
theorem bounded_cubic_moment_oai {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Y D : ℝ),
      1 ≤ N → 1 ≤ Y → 0 ≤ D →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ n ∈ H, n ≠ 0 ∧ norm n ≤ Y) → ∀ v : Eisenstein → ℂ,
      (∀ n ∈ H, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ H, v n*cubicSymbol a n‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*D^2 := by
  obtain ⟨C,hC,hdyad⟩ := cubic_inner_extension (show 0 < ε/2 by linarith)
  obtain ⟨E,hE,hlog⟩ := natLog_power_bound 2 (show 0 < ε/2 by linarith)
  refine ⟨C*E,mul_pos hC hE,?_⟩
  intro P H N Y D hN hY hD hP hH v hv
  let J := H.image (fun n => Nat.log 2 (normNat n))
  let w : Eisenstein → ℂ := fun n => if n ∈ H then v n else 0
  let F : ℝ := N+Y+(N*Y)^(2/3:ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hcount : (J.card:ℝ)^2 ≤ E*Y^(ε/2) := by
    have hsub : J ⊆ Finset.range (Nat.log 2 ⌊Y⌋₊+1) := by
      intro j hj
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_range.mpr
      have hnY : normNat n ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa only [normNat_cast] using (hH n hn).2)
      exact Nat.lt_succ_of_le (Nat.log_mono_right hnY)
    calc
      _ ≤ ((Nat.log 2 ⌊Y⌋₊+1:ℕ):ℝ)^2 := pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast (show J.card ≤ Nat.log 2 ⌊Y⌋₊+1 by
          simpa only [Finset.card_range] using Finset.card_le_card hsub)) _
      _ ≤ E*(⌊Y⌋₊:ℝ)^(ε/2) := hlog _ ((Nat.one_le_floor_iff Y).mpr hY)
      _ ≤ E*Y^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY0.le) (by positivity)) hE.le
  have hrow (j : ℕ) (hj : j ∈ J) :
      (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, w n*cubicSymbol a n‖^2) ≤
        C*(N*Y)^(ε/2)*Y*F*D^2 := by
    obtain ⟨n,hn,hnj⟩ := Finset.mem_image.mp hj
    have hnD : n ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨(hH n hn).1,hnj⟩
    have hjY : (2:ℝ)^j ≤ Y := (frequencyDyad_norm hnD).1.trans (hH n hn).2
    have hw : ∀ n ∈ frequencyDyad j, ‖w n‖ ≤ D := by
      intro n _
      dsimp only [w]
      split_ifs with hn
      · exact hv n hn
      · simpa using hD
    apply (hdyad P N hN hP j w D hD hw).trans
    dsimp only [F]
    gcongr
  have hsplit (a : Eisenstein) : (∑ n ∈ H, v n*cubicSymbol a n) =
      ∑ j ∈ J, ∑ n ∈ frequencyDyad j, w n*cubicSymbol a n :=
    finite_polynomial_dyad_partition H (fun n hn => (hH n hn).1) v a
  simp_rw [hsplit]
  apply (complex_mass_sum_sq_le J P
    (fun a j => ∑ n ∈ frequencyDyad j, w n*cubicSymbol a n)).trans
  calc
    _ ≤ (J.card:ℝ)*∑ _j ∈ J, C*(N*Y)^(ε/2)*Y*F*D^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = (J.card:ℝ)^2*C*(N*Y)^(ε/2)*Y*F*D^2 := by simp; ring
    _ ≤ (E*Y^(ε/2))*C*(N*Y)^(ε/2)*Y*F*D^2 := by gcongr
    _ = (C*E)*(Y^(ε/2)*(N*Y)^(ε/2))*Y*F*D^2 := by ring
    _ ≤ (C*E)*(N*Y)^ε*Y*F*D^2 := by
      have he : Y^(ε/2)*(N*Y)^(ε/2) ≤ (N*Y)^ε := by
        calc
          _ ≤ (N*Y)^(ε/2)*(N*Y)^(ε/2) := by
            gcongr
            exact le_mul_of_one_le_left hY0.le hN
          _ = _ := by rw [← Real.rpow_add (mul_pos hN0 hY0)]; congr 1; ring
      gcongr

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.bounded_cubic_moment_oai := @OAI.CubicFirstMoment.bounded_cubic_moment_oai
