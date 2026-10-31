-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.four_comparison_of_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:21:54.513996+00:00
-- url     : https://prove2.me/submissions/897c8020-4155-42e3-880c-847cbe838cd8

import Mathlib
import Definitions.Def_LaughlinGap
import Definitions.Def_OAIQ030L035
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_four_comparison_pointwise

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Occupation
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.basisContraction_apply_empty _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.extendLocal_add _root_.OAI.LaughlinGap.Occupation.extendLocal_adjoint _root_.OAI.LaughlinGap.Occupation.extendLocal_mul _root_.OAI.LaughlinGap.Occupation.extendLocal_one _root_.OAI.LaughlinGap.Occupation.extendLocal_smul _root_.OAI.LaughlinGap.Occupation.extendLocal_zero _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorInclusion_apply _root_.OAI.LaughlinGap.Occupation.sectorInclusion_apply_label _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.slice_apply _root_.OAI.LaughlinGap.Occupation.slice_extendLocal _root_.OAI.LaughlinGap.Occupation.vacuum_norm _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation. -/

noncomputable section


namespace LaughlinGap
namespace Occupation
open scoped BigOperators InnerProduct

theorem transition_norm_le {n : ℕ} (j : Fin n) (ε : Bool) (x : Hilbert n) :
    ‖transition j ε x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    (∑ A, ‖transition j ε x A‖ ^ 2) ≤ ∑ A, ‖x (flip j A)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro A _
      rw [transition_apply]
      split_ifs
      · simp
      · simp
    _ = _ := Equiv.sum_comp (flip j) (fun A => ‖x A‖ ^ 2)

theorem double_annihilation_norm_le {n : ℕ} (j k : Fin n) (x : Hilbert n) :
    ‖annihilation k (annihilation j x)‖ ≤ ‖x‖ :=
  (transition_norm_le k false _).trans (transition_norm_le j false x)

lemma weight_nonneg {n : ℕ} {d : Fin n → ℝ} (hd : ∀ j, 0 ≤ d j) (A : Finset (Fin n)) :
    0 ≤ weight d A := Finset.prod_nonneg (fun j _ => hd j)

lemma weight_le_one {n : ℕ} {d : Fin n → ℝ} (hd₀ : ∀ j, 0 ≤ d j) (hd₁ : ∀ j, d j ≤ 1)
    (A : Finset (Fin n)) : weight d A ≤ 1 :=
  Finset.prod_le_one (fun index _ => hd₀ index) (fun index _ => hd₁ index)

theorem diagonal_norm_le {n : ℕ} {d : Fin n → ℝ} (hd₀ : ∀ j, 0 ≤ d j)
    (hd₁ : ∀ j, d j ≤ 1) (x : Hilbert n) : ‖diagonal d x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, diagonal_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (weight_nonneg hd₀ _)]
  apply Finset.sum_le_sum
  intro A _
  exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg hd₀ A) (norm_nonneg _))
    (mul_le_of_le_one_left (norm_nonneg _) (weight_le_one hd₀ hd₁ A)) 2

theorem diagonal_comp {n : ℕ} (d e : Fin n → ℝ) :
    diagonal d ∘ₗ diagonal e = diagonal (fun j => d j * e j) := by
  ext x A
  simp [diagonal_apply, weight, Finset.prod_mul_distrib, mul_assoc]

theorem diagonal_comp_inv {n : ℕ} (d : Fin n → ℝ) (hd : ∀ j, d j ≠ 0) :
    diagonal d ∘ₗ diagonal (fun j => (d j)⁻¹) = LinearMap.id := by
  rw [diagonal_comp]
  have h : (fun j => d j * (d j)⁻¹) = (fun _ : Fin n => (1 : ℝ)) := by
    funext j
    exact mul_inv_cancel₀ (hd j)
  rw [h, diagonal_one]

theorem annihilation_diagonal {n : ℕ} (d : Fin n → ℝ) (j : Fin n) :
    annihilation j ∘ₗ diagonal d = (d j : ℂ) • (diagonal d ∘ₗ annihilation j) := by
  ext x A
  change annihilation j (diagonal d x) A = (d j : ℂ) * diagonal d (annihilation j x) A
  by_cases hj : j ∈ A
  · simp [transition_apply, hj]
  · simp [transition_apply, hj, weight, Finset.prod_insert, mul_assoc, mul_comm, mul_left_comm]

theorem word_diagonal {n : ℕ} (d : Fin n → ℝ) (js : List (Fin n)) :
    word js ∘ₗ diagonal d = ((js.map (fun j => (d j : ℂ))).prod) • (diagonal d ∘ₗ word js) := by
  induction js with
  | nil => simp [word]
  | cons j js ih =>
    rw [word, LinearMap.comp_assoc, annihilation_diagonal,
      LinearMap.comp_smul, ← LinearMap.comp_assoc, ih]
    simp only [List.map_cons, List.prod_cons, LinearMap.smul_comp, smul_smul,
      LinearMap.comp_assoc]

lemma pairAnnihilator_smul_real {n : ℕ} (v : Fin n → Fin n → ℂ) (r : ℝ) :
    pairAnnihilator (fun x y => (r : ℂ) * v x y) = (r : ℂ) • pairAnnihilator v := by
  simp only [pairAnnihilator, Finset.smul_sum, smul_ite, smul_zero, star_mul,
    Complex.star_def, Complex.conj_ofReal, smul_smul, mul_comm]

theorem pairAnnihilator_diagonal {n : ℕ} (d : Fin n → ℝ) (v : Fin n → Fin n → ℂ) :
    pairAnnihilator v * diagonal d =
      diagonal d * pairAnnihilator (fun x y => (d x * d y : ℝ) * v x y) := by
  simp only [pairAnnihilator, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x < y
  · simp only [ite_eq_left hxy, smul_mul_assoc, mul_smul_comm, star_mul, Complex.ofReal_mul,
      Complex.star_def, Complex.conj_ofReal]
    have hw := word_diagonal d [x,y]
    simp only [word, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
      mul_one, LinearMap.id_comp] at hw
    change starRingEnd ℂ (v x y) • ((annihilation y ∘ₗ annihilation x) ∘ₗ diagonal d) = _
    rw [hw, smul_smul]
    simp only [mul_comm]
    rfl
  · simp [hxy]

theorem pairAnnihilator_conjugation {n : ℕ} (d : Fin n → ℝ) (hd : ∀ j, d j ≠ 0)
    (v : Fin n → Fin n → ℂ) (r : ℝ) :
    pairAnnihilator (fun x y => (r : ℂ) * ((d x * d y : ℝ) * v x y)) =
      (r : ℂ) • (diagonal (fun j => (d j)⁻¹) * pairAnnihilator v * diagonal d) := by
  rw [pairAnnihilator_smul_real]
  congr 1
  rw [mul_assoc, pairAnnihilator_diagonal, ← mul_assoc]
  have hd' : ∀ j, (d j)⁻¹ ≠ 0 := fun j => inv_ne_zero (hd j)
  have hinv := diagonal_comp_inv (fun j => (d j)⁻¹) hd'
  simp only [inv_inv] at hinv
  change _ = (diagonal (fun j => (d j)⁻¹) ∘ₗ diagonal d) * _
  rw [hinv]
  exact (one_mul _).symm

theorem fourAnnihilator_conjugation {n : ℕ} (d : Fin n → ℝ) (hd : ∀ j, d j ≠ 0)
    (v : Fin n → Fin n → ℂ) (r : ℝ) (j k : Fin n) :
    annihilation k * annihilation j *
      pairAnnihilator (fun x y => (r : ℂ) * ((d x * d y : ℝ) * v x y)) =
      ((r / (d j * d k) : ℝ) : ℂ) •
        (diagonal (fun s => (d s)⁻¹) * (annihilation k * annihilation j * pairAnnihilator v) * diagonal d) := by
  rw [pairAnnihilator_conjugation d hd v r, mul_smul_comm, ← mul_assoc, ← mul_assoc]
  have hw := word_diagonal (fun s => (d s)⁻¹) [j,k]
  simp only [word, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil,
    mul_one, LinearMap.id_comp] at hw
  change (r : ℂ) • ((((annihilation k ∘ₗ annihilation j) ∘ₗ diagonal (fun s => (d s)⁻¹)) *
    pairAnnihilator v) * diagonal d) = _
  rw [hw]
  simp only [← Module.End.mul_eq_comp, smul_mul_assoc, smul_smul, mul_assoc,
    Complex.ofReal_inv, Complex.ofReal_mul, mul_inv_rev, div_eq_mul_inv, mul_comm]

theorem pairAnnihilator_energy_transfer {n : ℕ} (d : Fin n → ℝ)
    (hd₀ : ∀ j, 0 ≤ d j) (hd₁ : ∀ j, d j ≤ 1)
    (v : Fin n → Fin n → ℂ) {r : ℝ} (hr : 1 ≤ r) (x : Hilbert n) :
    ‖pairAnnihilator v (diagonal d x)‖ ^ 2 ≤
      ‖pairAnnihilator (fun i j => (r : ℂ) * ((d i * d j : ℝ) * v i j)) x‖ ^ 2 := by
  have hc := LinearMap.congr_fun (pairAnnihilator_diagonal d v) x
  change pairAnnihilator v (diagonal d x) =
    diagonal d (pairAnnihilator (fun i j => (d i * d j : ℝ) * v i j) x) at hc
  rw [hc, pairAnnihilator_smul_real, LinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith : 0 ≤ r)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (diagonal_norm_le hd₀ hd₁ _).trans (le_mul_of_one_le_left (norm_nonneg _) hr)

end Occupation
end LaughlinGap
namespace LaughlinGap
open scoped BigOperators Topology
open Filter

lemma orbitalDiagonalFactor_nonneg (Q x : ℕ) : 0 ≤ orbitalDiagonalFactor Q x :=
  Real.sqrt_nonneg _

lemma orbitalDiagonalFactor_pos {Q x : ℕ} (hQ : 0 < Q) (hx : x ≤ Q) :
    0 < orbitalDiagonalFactor Q x := by
  apply Real.sqrt_pos_of_pos
  have : (0 : ℝ) < (Q.descFactorial x : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hx
  positivity

lemma orbitalDiagonalFactor_le_one (Q x : ℕ) : orbitalDiagonalFactor Q x ≤ 1 := by
  rw [orbitalDiagonalFactor, Real.sqrt_le_one]
  by_cases hQ : (Q : ℝ)^x = 0
  · simp [hQ]
  · rw [div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hQ))]
    exact_mod_cast Nat.descFactorial_le_pow Q x

lemma one_le_pairRescalingFactor {Q p : ℕ} (hp : p ≤ 2*Q-2) :
    1 ≤ pairRescalingFactor Q p := by
  rw [pairRescalingFactor, Real.one_le_sqrt]
  have hd : (0 : ℝ) < ((2*Q-2).descFactorial p : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hp
  rw [le_div_iff₀ hd, one_mul]
  exact_mod_cast (Nat.descFactorial_le_pow (2*Q-2) p).trans
    (Nat.pow_le_pow_left (by omega : 2*Q-2 ≤ 2*Q) p)

theorem sphericalExteriorPairCoefficient_factor {Q p : ℕ} (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : ℕ) :
    sphericalExteriorPairCoefficient Q p x y =
      pairRescalingFactor Q p * orbitalDiagonalFactor Q x * orbitalDiagonalFactor Q y *
        limitingExteriorPairCoefficient p x y := by
  by_cases hxy : x + y = p + 1
  · have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    have hD0 : ((2*Q-2).descFactorial p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hp))
    have hx0 : (x.factorial : ℝ) ≠ 0 := by exact_mod_cast x.factorial_ne_zero
    have hy0 : (y.factorial : ℝ) ≠ 0 := by exact_mod_cast y.factorial_ne_zero
    have hpow : (Q : ℝ)^x * (Q : ℝ)^y = (Q : ℝ)^p * Q := by
      rw [← pow_add, hxy, pow_succ]
    have hr : Real.sqrt
        ((Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * (p.factorial : ℝ) /
          ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.factorial : ℝ) * (y.factorial : ℝ))) =
        pairRescalingFactor Q p * orbitalDiagonalFactor Q x * orbitalDiagonalFactor Q y *
          Real.sqrt ((p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by
        unfold pairRescalingFactor orbitalDiagonalFactor; positivity)).mp
      simp only [pairRescalingFactor, orbitalDiagonalFactor, mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ (Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * (p.factorial : ℝ) /
          ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.factorial : ℝ) * (y.factorial : ℝ)) from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (2:ℝ)^p * (Q : ℝ)^p / ((2*Q-2).descFactorial p : ℝ) from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (Q.descFactorial x : ℝ) / (Q : ℝ)^x from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (Q.descFactorial y : ℝ) / (Q : ℝ)^y from by positivity),
        Real.sq_sqrt (show (0 : ℝ) ≤ (p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ)) from by positivity)]
      field_simp
      calc
        _ = (Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * ((Q:ℝ)^x * (Q:ℝ)^y) := by ring
        _ = _ := by rw [hpow]; ring
    simp only [sphericalExteriorPairCoefficient, limitingExteriorPairCoefficient, ite_eq_left hxy]
    rw [hr]
    ring
  · simp [sphericalExteriorPairCoefficient, limitingExteriorPairCoefficient, hxy]

lemma normalizedFallingFactorial_eq_prod (Q x : ℕ) :
    (Q.descFactorial x : ℝ) / (Q : ℝ)^x =
      ∏ k ∈ Finset.range x, ((Q - k : ℕ) : ℝ) / (Q : ℝ) := by
  simp [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma normalizedFallingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => ((Q - k : ℕ) : ℝ) / (Q : ℝ)) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ Q)]
  field_simp

theorem orbitalDiagonalFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => orbitalDiagonalFactor Q x) atTop (𝓝 1) := by
  have h := tendsto_finsetProd (Finset.range x) (fun k _ => normalizedFallingFactor_tendsto k)
  simp only [Finset.prod_const_one, ← normalizedFallingFactorial_eq_prod] at h
  simpa only [Real.sqrt_one, orbitalDiagonalFactor, Function.comp_def] using Real.continuous_sqrt.tendsto 1 |>.comp h

lemma pairRescalingFactor_sq_eq_prod (Q p : ℕ) :
    (2 * (Q : ℝ))^p / ((2*Q-2).descFactorial p : ℝ) =
      ∏ k ∈ Finset.range p, (2*(Q : ℝ)) / ((2*Q-2-k : ℕ) : ℝ) := by
  simp [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma rescalingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => (2*(Q : ℝ)) / ((2*Q-2-k : ℕ) : ℝ)) atTop (𝓝 1) := by
  have ht : Tendsto (fun Q : ℕ => (2 : ℝ) / (2 - ((k : ℝ)+2)/Q)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)+2))) (by norm_num : (2 : ℝ)-0 ≠ 0)
    simpa only [Pi.div_def, sub_zero, div_self (by norm_num : (2:ℝ) ≠ 0)] using h
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k+3)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring

theorem pairRescalingFactor_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairRescalingFactor Q p) atTop (𝓝 1) := by
  have h := tendsto_finsetProd (Finset.range p) (fun k _ => rescalingFactor_tendsto k)
  simp only [Finset.prod_const_one, ← pairRescalingFactor_sq_eq_prod] at h
  simpa only [Real.sqrt_one, pairRescalingFactor, Function.comp_def] using Real.continuous_sqrt.tendsto 1 |>.comp h

end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators Topology
open Filter

lemma diagonalCLM_eq_matrix {n : ℕ} (d : Fin n → ℝ) :
    diagonalCLM d = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Finset (Fin n)) (Matrix.diagonal (fun A => (weight d A : ℂ))) := by
  ext x A
  change (diagonalCLM d x).ofLp A = _
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  rfl

theorem diagonalCLM_tendsto {n : ℕ} {ι : Type*} {l : Filter ι}
    {d : ι → Fin n → ℝ} {e : Fin n → ℝ}
    (hd : ∀ j, Tendsto (fun q => d q j) l (𝓝 (e j))) :
    Tendsto (fun q => diagonalCLM (d q)) l (𝓝 (diagonalCLM e)) := by
  have hw (A : Finset (Fin n)) : Tendsto (fun q => weight (d q) A) l (𝓝 (weight e A)) :=
    tendsto_finsetProd A (fun j _ => hd j)
  have hM : Tendsto (fun q => Matrix.diagonal (fun A => (weight (d q) A : ℂ))) l
      (𝓝 (Matrix.diagonal (fun A => (weight e A : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro A
    apply tendsto_pi_nhds.mpr
    intro B
    by_cases hAB : A = B
    · subst B
      simpa only [Matrix.diagonal_apply_eq, Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp (hw A)
    · simpa [Matrix.diagonal, hAB] using (tendsto_const_nhds (x := (0 : ℂ)))
  have hc : Continuous (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Finset (Fin n))) :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Finset (Fin n))).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  simp_rw [diagonalCLM_eq_matrix]
  exact hc.continuousAt.tendsto.comp hM

theorem diagonalCLM_inv_tendsto_one {n : ℕ} {ι : Type*} {l : Filter ι}
    {d : ι → Fin n → ℝ} (hd : ∀ j, Tendsto (fun q => d q j) l (𝓝 1)) :
    Tendsto (fun q => diagonalCLM (fun j => (d q j)⁻¹)) l (𝓝 1) := by
  have hi (j : Fin n) : Tendsto (fun q => (d q j)⁻¹) l (𝓝 1) := by
    simpa using (hd j).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa using diagonalCLM_tendsto hi

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq )
open scoped BigOperators

section PairNormalization
open Polynomial

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q + 1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  by_cases hs : x.val + y.val = p + 1
  · simp only [hs, Nat.add_comm y.val x.val, ↓reduceIte]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    ring
  · simp [hs, Nat.add_comm]

end PairNormalization

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct ComplexConjugate

section Compression
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem compression_positive_iff (W : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E)
    (hC : C.IsSymmetric) :
    (W ∘ₗ C ∘ₗ W.adjoint).IsPositive ↔
      ∀ x ∈ W.adjoint.range, 0 ≤ RCLike.re (inner 𝕜 (C x) x) := by
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    simpa only [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right] using
      h.re_inner_nonneg_left y
  · intro h
    refine ⟨hC.conj_adjoint W, fun y => ?_⟩
    simpa only [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right] using
      h (W.adjoint y) (LinearMap.mem_range_self W.adjoint y)

theorem gram_compression_positive_iff (W : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E)
    (hC : C.IsSymmetric) :
    ((W.adjoint ∘ₗ W) ∘ₗ C ∘ₗ (W.adjoint ∘ₗ W)).IsPositive ↔
      (W ∘ₗ C ∘ₗ W.adjoint).IsPositive := by
  have hG : (W.adjoint ∘ₗ W).IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self W
  have h := compression_positive_iff (W.adjoint ∘ₗ W) C hC
  rw [hG.adjoint_eq, LinearMap.range_adjoint_comp_self] at h
  exact h.trans (compression_positive_iff W C hC).symm

end Compression

section AnnihilatorBound
variable {ι κ E F : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F]

theorem annihilator_collection_bound (p : ι → κ) (B : κ → E → F)
    (A : ι → F → F) {M : ℕ}
    (hM : ∀ k, (Finset.univ.filter (fun b => p b = k)).card ≤ M)
    (hA : ∀ b y, ‖A b y‖ ≤ ‖y‖) (x : E) :
    ∑ b, ‖A b (B (p b) x)‖ ^ 2 ≤ (M : ℝ) * ∑ k, ‖B k x‖ ^ 2 := by
  classical
  calc
    (∑ b, ‖A b (B (p b) x)‖ ^ 2) ≤ ∑ b, ‖B (p b) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      exact pow_le_pow_left₀ (norm_nonneg _) (hA b _) 2
    _ = ∑ k, ((Finset.univ.filter (fun b => p b = k)).card : ℝ) * ‖B k x‖ ^ 2 := by
      rw [← Finset.sum_fiberwise' Finset.univ p (fun k => ‖B k x‖ ^ 2)]
      simp
    _ ≤ ∑ k, (M : ℝ) * ‖B k x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM k) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end AnnihilatorBound

section Perturbation
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem quadratic_perturbation_abs_le (T S : E →L[𝕜] E) (x : E) :
    |RCLike.re (inner 𝕜 x (T x)) - RCLike.re (inner 𝕜 x (S x))| ≤
      ‖T - S‖ * ‖x‖ ^ 2 := by
  have h₁ := RCLike.norm_re_le_norm (inner 𝕜 x ((T - S) x))
  have h₂ := norm_inner_le_norm (𝕜 := 𝕜) x ((T - S) x)
  have h₃ := mul_le_mul_of_nonneg_left ((T - S).le_opNorm x) (norm_nonneg x)
  have h := (h₁.trans h₂).trans h₃
  simpa only [sub_apply, inner_sub_right, map_sub, Real.norm_eq_abs,
    mul_left_comm ‖x‖ ‖T - S‖ ‖x‖, ← pow_two, mul_assoc] using h

theorem quadratic_perturbation_lower_bound (T S : E →L[𝕜] E) (x : E)
    (hS : 0 ≤ RCLike.re (inner 𝕜 x (S x))) :
    -‖T - S‖ * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (T x)) := by
  have h := (abs_le.mp (quadratic_perturbation_abs_le T S x)).1
  nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in

theorem relative_column_perturbation_bound {ι : Type*} [Fintype ι]
    (A : ι → E → F) (Δ : E → E) (eStar eQ : E → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hA : ∀ x, (∑ b, ‖A b x‖ ^ 2) ≤ C₀ * eStar x)
    (hΔ : ∀ x, eStar (Δ x) ≤ eQ x)
    (T S : (PiLp 2 (fun _ : ι => F)) →L[𝕜] (PiLp 2 (fun _ : ι => F)))
    (hS : ∀ x, 0 ≤ RCLike.re (inner 𝕜 (WithLp.toLp 2 (fun b => A b x))
      (S (WithLp.toLp 2 (fun b => A b x))))) (x : E) :
    -(C₀ * ‖T - S‖) * eQ x ≤
      RCLike.re (inner 𝕜 (WithLp.toLp 2 (fun b => A b (Δ x)))
        (T (WithLp.toLp 2 (fun b => A b (Δ x))))) := by
  let v : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun b => A b (Δ x))
  have hv : ‖v‖ ^ 2 ≤ C₀ * eQ x := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact (hA (Δ x)).trans (mul_le_mul_of_nonneg_left (hΔ x) hC₀)
  have hp := quadratic_perturbation_lower_bound T S v (hS (Δ x))
  calc
    -(C₀ * ‖T - S‖) * eQ x = -‖T - S‖ * (C₀ * eQ x) := by ring
    _ ≤ -‖T - S‖ * ‖v‖ ^ 2 := by
      exact mul_le_mul_of_nonpos_left hv (neg_nonpos.mpr (norm_nonneg _))
    _ ≤ _ := hp

theorem relative_column_error_tendsto {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : ℕ → G →L[𝕜] G} {S : G →L[𝕜] G} {C₀ : ℝ}
    (hT : Filter.Tendsto T Filter.atTop (nhds S)) :
    Filter.Tendsto (fun Q => C₀ * ‖T Q - S‖) Filter.atTop (nhds 0) := by
  simpa using (((hT.sub (tendsto_const_nhds (x := S))).norm).const_mul C₀)

end Perturbation

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairEnergy
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.fullContraction_add _root_.OAI.LaughlinGap.Occupation.fullContraction_single _root_.OAI.LaughlinGap.Occupation.fullContraction_smul _root_.OAI.LaughlinGap.Occupation.fullContraction_zero _root_.OAI.LaughlinGap.Occupation.inner_vacuum_left _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.Occupation.word_cons _root_.OAI.LaughlinGap.Occupation.word_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Energy. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators Topology
open Filter

lemma localPair_eq_factored {n Q p : ℕ} (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    localPair n Q p = pairAnnihilator (fun x y : Fin n =>
      (pairRescalingFactor Q p : ℂ) *
        ((orbitalDiagonalFactor Q x.val * orbitalDiagonalFactor Q y.val : ℝ) *
          (limitingExteriorPairCoefficient p x.val y.val : ℂ))) := by
  unfold localPair
  congr 1
  funext x y
  rw [sphericalExteriorPairCoefficient_factor hQ hp]
  push_cast
  ring

theorem localFour_conjugation {n Q p : ℕ} (hQ : 0 < Q) (hn : n ≤ Q+1)
    (hp : p ≤ 2*Q-2) (j k : Fin n) :
    annihilation k * annihilation j * localPair n Q p =
      ((pairRescalingFactor Q p / (orbitalDiagonalFactor Q j.val *
        orbitalDiagonalFactor Q k.val) : ℝ) : ℂ) •
      ((localDeltaInv n Q).toLinearMap *
        (annihilation k * annihilation j * localPairStar n p) * (localDelta n Q).toLinearMap) := by
  rw [localPair_eq_factored hQ hp]
  apply fourAnnihilator_conjugation
  intro j
  exact ne_of_gt (orbitalDiagonalFactor_pos hQ (by have := j.is_lt; omega))

theorem localDeltaInv_tendsto (n : ℕ) :
    Tendsto (localDeltaInv n) atTop (𝓝 1) :=
  diagonalCLM_inv_tendsto_one (fun j => orbitalDiagonalFactor_tendsto j.val)

theorem localPairEnergy_transfer {n L Q : ℕ} (hQ : 0 < Q) (hL : L ≤ 2*Q-1)
    (x : Hilbert n) :
    localPairEnergyStar n L (localDelta n Q x) ≤ localPairEnergy n L Q x := by
  apply Finset.sum_le_sum
  intro p _
  have hp : p.val ≤ 2*Q-2 := by have := p.is_lt; omega
  rw [localPair_eq_factored hQ hp]
  exact pairAnnihilator_energy_transfer _
    (fun j => orbitalDiagonalFactor_nonneg Q j.val)
    (fun j => orbitalDiagonalFactor_le_one Q j.val) _ (one_le_pairRescalingFactor hp) x

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma join_eq_map {n m : ℕ} (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join A R = Finset.map finSumFinEquiv.toEmbedding (A.disjSum R) := rfl

@[simp] lemma mem_join_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    Fin.castAdd m j ∈ join A R ↔ j ∈ A := by
  rw [join_eq_map, ← finSumFinEquiv_apply_left]
  simp

@[simp] lemma mem_join_right {n m : ℕ} (j : Fin m) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    Fin.natAdd n j ∈ join A R ↔ j ∈ R := by
  rw [join_eq_map, ← finSumFinEquiv_apply_right]
  simp

@[simp] lemma join_card {n m : ℕ} (A : Finset (Fin n)) (R : Finset (Fin m)) :
    (join A R).card = A.card + R.card := by simp [join_eq_map]

lemma prefix_ne_suffix {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hv := congrArg Fin.val h
  have := i.is_lt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma join_erase_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join (A.erase j) R = (join A R).erase (Fin.castAdd m j) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl i => simp
  | inr i => simp [Ne.symm (prefix_ne_suffix j i)]

lemma join_insert_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join (insert j A) R = insert (Fin.castAdd m j) (join A R) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl i => simp
  | inr i => simp [Ne.symm (prefix_ne_suffix j i)]

lemma join_flip_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    join (flip j A) R = flip (Fin.castAdd m j) (join A R) := by
  by_cases hi : j ∈ A
  · simp [hi, join_erase_left]
  · simp [hi, join_insert_left]

lemma join_filter_prefix {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    (join A R).filter (fun k => k < Fin.castAdd m j) =
      join (A.filter (fun k => k < j)) (∅ : Finset (Fin m)) := by
  ext x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, Finset.mem_filter, mem_join_left]
    rfl
  | inr i =>
    have h : ¬ Fin.natAdd n i < Fin.castAdd m j := by
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
      have := j.is_lt
      omega
    simp [h]

theorem sign_join_left {n m : ℕ} (j : Fin n) (A : Finset (Fin n)) (R : Finset (Fin m)) :
    sign (Fin.castAdd m j) (join A R) = sign j A := by
  simp [sign, join_filter_prefix]

theorem norm_sq_eq_sum_slice {n m : ℕ} (x : Hilbert (n+m)) :
    ‖x‖ ^ 2 = ∑ R : Finset (Fin m), ‖slice R x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, slice_apply]
  rw [← Equiv.sum_comp (joinEquiv n m) (fun A => ‖x A‖ ^ 2), Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

theorem slice_transition {n m : ℕ} (R : Finset (Fin m)) (j : Fin n) (ε : Bool)
    (x : Hilbert (n+m)) :
    slice R (transition (Fin.castAdd m j) ε x) = transition j ε (slice R x) := by
  ext A
  simp [transition_apply, slice_apply, sign_join_left, ← join_flip_left]

@[simp] theorem extendLocal_transition {n m : ℕ} (j : Fin n) (ε : Bool) :
    extendLocal (m := m) (transition j ε) = transition (Fin.castAdd m j) ε := by
  apply LinearMap.ext
  intro x
  apply eq_of_slice_eq
  intro R
  rw [slice_extendLocal, slice_transition]

end LaughlinGap.Occupation

namespace LaughlinGap
open scoped BigOperators InnerProduct ComplexOrder

section PositiveLifting
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem matrixLift_rankOne (B : ι → Module.End ℂ E) (v w : ι → ℂ) :
    matrixLift B (Matrix.vecMulVec v (star w)) =
      (contractCombination B v).adjoint * contractCombination B w := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply,
    Pi.star_apply, contractCombination, map_sum, map_smulₛₗ,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Complex.star_def, Complex.conj_conj, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrixLift_positive (B : ι → Module.End ℂ E) {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) : (matrixLift B M).IsPositive := by
  classical
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  rw [map_sum]
  apply LinearMap.isPositive_sum
  intro i _
  rw [matrixLift_rankOne]
  exact LinearMap.isPositive_adjoint_comp_self _

theorem matrixLift_columns {κ : Type*} [Fintype κ]
    (B : ι → Module.End ℂ E) (W : Matrix ι κ ℂ) (C : Matrix κ κ ℂ) :
    matrixLift B (W * C * W.conjTranspose) =
      matrixLift (fun r => contractCombination B (fun i => W i r)) C := by
  classical
  have hm : W * C * W.conjTranspose =
      ∑ r, ∑ s, C r s • Matrix.vecMulVec (fun i => W i r) (star (fun i => W i s)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hm]
  simp only [map_sum, map_smul, matrixLift_rankOne]
  rfl

theorem matrixLift_gram_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    [DecidableEq ι] (B : ι → Module.End ℂ E) (W : Matrix ι κ ℂ)
    (C : Matrix κ κ ℂ) (hC : C.IsHermitian)
    (hG : ((W.conjTranspose * W) * C * (W.conjTranspose * W)).PosSemidef) :
    (matrixLift (fun r => contractCombination B (fun i => W i r)) C).IsPositive := by
  rw [← matrixLift_columns]
  apply matrixLift_positive
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  rw [← Matrix.isPositive_toEuclideanLin_iff] at hG
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hG ⊢
  exact (gram_compression_positive_iff W.toEuclideanLin C.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hC)).mp hG

end PositiveLifting

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Contraction
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.coordinatesFromTensor_apply _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.Spin.spinTripleWedge_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct Topology

section BlockOperator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma blockOperator_inner (M : Matrix ι ι ℂ) (T : E →L[ℂ] E)
    (x y : ColumnSpace ι E) :
    inner ℂ x (blockOperator M T y) = ∑ b, ∑ c, M b c * inner ℂ (x b) (T (y c)) := by
  simp only [PiLp.inner_apply, blockOperator_apply, inner_sum, inner_smul_right]

theorem blockOperator_tendsto {M : ℕ → Matrix ι ι ℂ} {M₀ : Matrix ι ι ℂ}
    {T : ℕ → E →L[ℂ] E} {T₀ : E →L[ℂ] E}
    (hM : ∀ b c, Filter.Tendsto (fun Q => M Q b c) Filter.atTop (𝓝 (M₀ b c)))
    (hT : Filter.Tendsto T Filter.atTop (𝓝 T₀)) :
    Filter.Tendsto (fun Q => blockOperator (M Q) (T Q)) Filter.atTop (𝓝 (blockOperator M₀ T₀)) := by
  apply tendsto_finsetSum
  intro b _
  apply tendsto_finsetSum
  intro c _
  apply (hM b c).smul
  have hf : Continuous (fun T : E →L[ℂ] E =>
      (columnInclusion b).comp (T.comp (columnProjection c))) := by fun_prop
  exact hf.continuousAt.tendsto.comp hT

theorem matrixLift_inner_eq_block (A : ι → Module.End ℂ E) (M : Matrix ι ι ℂ) (x : E) :
    inner ℂ x (matrixLift A M x) =
      inner ℂ (WithLp.toLp 2 (fun b => A b x))
        (blockOperator M (1 : E →L[ℂ] E) (WithLp.toLp 2 (fun b => A b x))) := by
  rw [blockOperator_inner]
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sum, inner_smul_right,
    LinearMap.adjoint_inner_right, one_apply_eq_self]

theorem conjugated_matrix_transfer
    (A : ι → Module.End ℂ E) (Δ : ℕ → E → E)
    (eStar : E → ℝ) (eQ : ℕ → E → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hA : ∀ x, (∑ b, ‖A b x‖ ^ 2) ≤ C₀ * eStar x)
    (hΔ : ∀ᶠ Q in Filter.atTop, ∀ x, eStar (Δ Q x) ≤ eQ Q x)
    (U : ℕ → E →L[ℂ] E) (M : ℕ → Matrix ι ι ℂ) (M₀ : Matrix ι ι ℂ)
    (hU : Filter.Tendsto U Filter.atTop (𝓝 1))
    (hM : ∀ b c, Filter.Tendsto (fun Q => M Q b c) Filter.atTop (𝓝 (M₀ b c)))
    (h₀ : (matrixLift A M₀).IsPositive) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ x,
        -(ρ Q) * eQ Q x ≤
          (∑ b, ∑ c, M Q b c * inner ℂ (U Q (A b (Δ Q x)))
            (U Q (A c (Δ Q x)))).re := by
  let S := blockOperator M₀ (1 : E →L[ℂ] E)
  let T := fun Q => blockOperator (M Q) ((U Q).adjoint * U Q)
  have hAdj : Filter.Tendsto (fun Q => (U Q).adjoint) Filter.atTop (𝓝 1) := by
    simpa only [Function.comp_def, ContinuousLinearMap.adjoint_one] using
      ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hU
  have hT : Filter.Tendsto T Filter.atTop (𝓝 S) := by
    exact blockOperator_tendsto hM (by simpa using hAdj.mul hU)
  refine ⟨fun Q => C₀ * ‖T Q - S‖, fun Q => mul_nonneg hC₀ (norm_nonneg _),
    relative_column_error_tendsto hT, ?_⟩
  filter_upwards [hΔ] with Q hΔQ
  intro x
  have hp := relative_column_perturbation_bound (fun b x => A b x) (Δ Q) eStar (eQ Q)
    hC₀ hA hΔQ (T Q) S (fun x => ?_) x
  · simpa only [T, blockOperator_inner, PiLp.toLp_apply, mul_apply_eq_comp,
      ContinuousLinearMap.adjoint_inner_right, RCLike.re_eq_complex_re] using hp
  · rw [← matrixLift_inner_eq_block]
    exact h₀.re_inner_nonneg_right x

omit [DecidableEq ι] in

theorem matrixLift_conjugated_inner (A : ι → Module.End ℂ E) (M : Matrix ι ι ℂ)
    (U D : Module.End ℂ E) (x : E) :
    inner ℂ x (matrixLift (fun b => U * A b * D) M x) =
      ∑ b, ∑ c, M b c * inner ℂ (U (A b (D x))) (U (A c (D x))) := by
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, inner_sum, inner_smul_right,
    LinearMap.adjoint_inner_right]

omit [Fintype ι] [DecidableEq ι] in

theorem matrix_compression_tendsto {κ : Type*} [Fintype κ]
    {W : ℕ → Matrix ι κ ℂ} {W₀ : Matrix ι κ ℂ}
    {C : ℕ → Matrix κ κ ℂ} {C₀ : Matrix κ κ ℂ}
    (hW : ∀ b r, Filter.Tendsto (fun Q => W Q b r) Filter.atTop (𝓝 (W₀ b r)))
    (hC : ∀ r s, Filter.Tendsto (fun Q => C Q r s) Filter.atTop (𝓝 (C₀ r s)))
    (b c : ι) :
    Filter.Tendsto (fun Q => (W Q * C Q * (W Q).conjTranspose) b c)
      Filter.atTop (𝓝 ((W₀ * C₀ * W₀.conjTranspose) b c)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply tendsto_finsetSum
  intro r _
  apply Filter.Tendsto.mul
  · apply tendsto_finsetSum
    intro s _
    exact (hW b s).mul (hC s r)
  · exact (hW c r).star

end BlockOperator
end LaughlinGap

namespace LaughlinGap.Occupation
open scoped BigOperators Topology InnerProduct

theorem extendLocal_relative_energy_bound {n m : ℕ} {ι : Type*} [Fintype ι]
    (S : Module.End ℂ (Hilbert n)) (B : ι → Module.End ℂ (Hilbert n)) (c : ℝ)
    (h : ∀ x, c * (∑ b, ‖B b x‖ ^ 2) ≤ (inner ℂ x (S x)).re) (x : Hilbert (n+m)) :
    c * (∑ b, ‖extendLocal (B b) x‖ ^ 2) ≤ (inner ℂ x (extendLocal S x)).re := by
  rw [inner_eq_sum_slice]
  simp_rw [norm_sq_eq_sum_slice, slice_extendLocal]
  rw [Complex.re_sum, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun R _ => h (slice R x))

theorem local_relative_matrix_transfer {n L : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Fin L) (j k : ι → Fin n)
    (M : ℕ → Matrix ι ι ℂ) (M₀ : Matrix ι ι ℂ)
    (hM : ∀ b c, Filter.Tendsto (fun Q => M Q b c) Filter.atTop (𝓝 (M₀ b c)))
    (h₀ : (matrixLift (fun b => annihilation (k b) * annihilation (j b) *
      localPairStar n (p b).val) M₀).IsPositive) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (x : Hilbert (n+m)),
        -(ρ Q) * (∑ a : Fin L, ‖extendLocal (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendLocal (matrixLift
            (fun b => (localDeltaInv n Q).toLinearMap *
              (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val) *
                (localDelta n Q).toLinearMap) (M Q)) x)).re := by
  let A : ι → Module.End ℂ (Hilbert n) :=
    fun b => annihilation (k b) * annihilation (j b) * localPairStar n (p b).val
  have hA (x : Hilbert n) :
      ∑ b, ‖A b x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * localPairEnergyStar n L x := by
    apply annihilator_collection_bound p (fun a : Fin L => localPairStar n a.val)
      (fun b y => annihilation (k b) (annihilation (j b) y))
    · intro a
      simpa only [Finset.card_univ] using Finset.card_le_card
        (Finset.filter_subset (fun b => p b = a) Finset.univ)
    · intro b y
      exact double_annihilation_norm_le (j b) (k b) y
  have hΔ : ∀ᶠ Q in Filter.atTop, ∀ x,
      localPairEnergyStar n L (localDelta n Q x) ≤ localPairEnergy n L Q x := by
    filter_upwards [Filter.eventually_ge_atTop (L+2)] with Q hQ
    intro x
    exact localPairEnergy_transfer (by omega) (by omega) x
  obtain ⟨ρ, hρ, ht, hq⟩ := conjugated_matrix_transfer A (fun Q x => localDelta n Q x)
    (localPairEnergyStar n L) (fun Q => localPairEnergy n L Q)
    (C₀ := (Fintype.card ι : ℝ)) (Nat.cast_nonneg _) hA hΔ
    (localDeltaInv n) M M₀ (localDeltaInv_tendsto n) hM h₀
  refine ⟨ρ, hρ, ht, ?_⟩
  filter_upwards [hq] with Q hqQ
  intro m x
  apply extendLocal_relative_energy_bound _ (fun a : Fin L => localPair n Q a.val) (-ρ Q) ?_ x
  intro y
  rw [matrixLift_conjugated_inner]
  exact hqQ y

theorem localFour_factor_tendsto (p j k : ℕ) :
    Filter.Tendsto (fun Q => pairRescalingFactor Q p /
      (orbitalDiagonalFactor Q j * orbitalDiagonalFactor Q k)) Filter.atTop (𝓝 1) := by
  simpa only [Pi.div_def, Pi.mul_def, one_mul, div_one] using (pairRescalingFactor_tendsto p).div
    ((orbitalDiagonalFactor_tendsto j).mul (orbitalDiagonalFactor_tendsto k)) (by norm_num)

theorem local_four_family_transfer {n L : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ι → Fin L) (j k : ι → Fin n)
    (s : ℕ → κ → ι → ℝ) (s₀ : κ → ι → ℝ)
    (C : ℕ → Matrix κ κ ℂ) (C₀ : Matrix κ κ ℂ)
    (hs : ∀ r b, Filter.Tendsto (fun Q => s Q r b) Filter.atTop (𝓝 (s₀ r b)))
    (hC : ∀ r t, Filter.Tendsto (fun Q => C Q r t) Filter.atTop (𝓝 (C₀ r t)))
    (h₀ : (matrixLift (fun r => ∑ b, (s₀ r b : ℂ) •
      (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val)) C₀).IsPositive) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (x : Hilbert (n+m)),
        -(ρ Q) * (∑ a : Fin L, ‖extendLocal (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendLocal (matrixLift
            (fun r => ∑ b, (s Q r b : ℂ) •
              (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q)) x)).re := by
  let A : ι → Module.End ℂ (Hilbert n) :=
    fun b => annihilation (k b) * annihilation (j b) * localPairStar n (p b).val
  let w : ℕ → Matrix ι κ ℂ := fun Q b r =>
    ((s Q r b * (pairRescalingFactor Q (p b).val /
      (orbitalDiagonalFactor Q (j b).val * orbitalDiagonalFactor Q (k b).val)) : ℝ) : ℂ)
  let w₀ : Matrix ι κ ℂ := fun b r => (s₀ r b : ℂ)
  have hw : ∀ b r, Filter.Tendsto (fun Q => w Q b r) Filter.atTop (𝓝 (w₀ b r)) := by
    intro b r
    have h := (hs r b).mul (localFour_factor_tendsto (p b).val (j b).val (k b).val)
    simpa only [Function.comp_def, mul_one, w, w₀] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hM₀ : (matrixLift A (w₀ * C₀ * w₀.conjTranspose)).IsPositive := by
    rw [matrixLift_columns]
    simpa only [contractCombination, w₀, Complex.star_def, Complex.conj_ofReal] using h₀
  obtain ⟨ρ, hρ, ht, hq⟩ := local_relative_matrix_transfer p j k
    (fun Q => w Q * C Q * (w Q).conjTranspose) (w₀ * C₀ * w₀.conjTranspose)
    (matrix_compression_tendsto hw hC) hM₀
  refine ⟨ρ, hρ, ht, ?_⟩
  filter_upwards [hq, Filter.eventually_ge_atTop (n+L+2)] with Q hqQ hQ
  intro m x
  have hf (r : κ) :
      contractCombination (fun b => (localDeltaInv n Q).toLinearMap * A b *
        (localDelta n Q).toLinearMap) (fun b => w Q b r) =
      ∑ b, (s Q r b : ℂ) • (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val) := by
    unfold contractCombination
    apply Finset.sum_congr rfl
    intro b _
    have hqb : (p b).val ≤ 2*Q-2 := by have := (p b).is_lt; omega
    rw [localFour_conjugation (by omega : 0 < Q) (by omega : n ≤ Q+1) hqb]
    simp [w, A, smul_smul]
  have heq : matrixLift
      (fun r => ∑ b, (s Q r b : ℂ) •
        (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q) =
      matrixLift (fun b => (localDeltaInv n Q).toLinearMap * A b *
        (localDelta n Q).toLinearMap) (w Q * C Q * (w Q).conjTranspose) := by
    rw [matrixLift_columns]
    simp only [hf]
  rw [heq]
  exact hqQ m x

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct Topology ComplexOrder

lemma word_perm_scalar {n : ℕ} {js ks : List (Fin n)} (h : js.Perm ks) :
    ∃ c : ℂ, word js = c • word ks := by
  induction h with
  | nil => exact ⟨1, by simp⟩
  | cons j h ih =>
    obtain ⟨c,hc⟩ := ih
    exact ⟨c, by simp only [word_cons, hc, smul_mul_assoc]⟩
  | swap i j js =>
    refine ⟨-1, ?_⟩
    rw [word_cons, word_cons, word_cons, word_cons]
    rw [mul_assoc, annihilation_anticommute i j, mul_neg, ← mul_assoc]
    simp only [neg_smul, one_smul]
  | trans h h' ih ih' =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := ih'
    exact ⟨c*d, by rw [hc, hd, smul_smul]⟩

lemma word_eq_zero_of_not_nodup {n : ℕ} (js : List (Fin n)) (h : ¬ js.Nodup) :
    word js = 0 := by
  induction js with
  | nil => simp at h
  | cons j js ih =>
    by_cases hj : js.Nodup
    · have hm : j ∈ js := by simpa only [List.nodup_cons, hj, and_true, not_not] using h
      obtain ⟨c,hc⟩ := word_perm_scalar (List.perm_cons_erase hm)
      rw [word_cons, hc, word_cons, smul_mul_assoc, mul_assoc]
      have hz : annihilation j * annihilation j = 0 := transition_square j false
      rw [hz, mul_zero, smul_zero]
    · rw [word_cons, ih hj, zero_mul]

theorem word_normal_form {n : ℕ} (js : List (Fin n)) :
    ∃ c : ℂ, word js = c • word (js.toFinset.sort (· ≤ ·)) := by
  by_cases hn : js.Nodup
  · apply word_perm_scalar
    exact ((js.toFinset.sort_perm_toList (· ≤ ·)).trans (List.toFinset_toList hn)).symm
  · exact ⟨0, by rw [word_eq_zero_of_not_nodup js hn, zero_smul]⟩

theorem basisContraction_adjoint_vacuum {n k : ℕ} (A : BasisLabel n k) :
    (basisContraction A).adjoint (vacuum n) = EuclideanSpace.single A.val 1 := by
  apply ext_inner_right ℂ
  intro x
  rw [LinearMap.adjoint_inner_left, inner_vacuum_left, basisContraction_apply_empty]
  simp [EuclideanSpace.inner_single_left]

@[simp] lemma reconstruct_allBasisContraction {n : ℕ} (A : Finset (Fin n)) :
    reconstruct (allBasisContraction A) = allBasisContraction A := by
  change fullContraction ((basisContraction (⟨A,rfl⟩ : BasisLabel n A.card)).adjoint (vacuum n)) = _
  rw [basisContraction_adjoint_vacuum, fullContraction_single]
  simp

theorem reconstruct_word {n : ℕ} (js : List (Fin n)) : reconstruct (word js) = word js := by
  obtain ⟨c,hc⟩ := word_normal_form js
  rw [hc]
  change reconstruct (c • allBasisContraction js.toFinset) = c • allBasisContraction js.toFinset
  rw [map_smul, reconstruct_allBasisContraction]

theorem reconstruct_four_pair {n : ℕ} (v : Fin n → Fin n → ℂ) (j k : Fin n) :
    reconstruct (annihilation k * annihilation j * pairAnnihilator v) =
      annihilation k * annihilation j * pairAnnihilator v := by
  simp only [pairAnnihilator, Finset.mul_sum, mul_ite, mul_zero, mul_smul_comm,
    map_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : x < y
  · rw [ite_eq_left h, map_smul]
    congr 1
    have he : annihilation k * annihilation j * (annihilation y * annihilation x) =
        word [x,y,j,k] := by simp only [word_cons, word_nil, one_mul, mul_assoc]
    rw [he, reconstruct_word]
  · rw [ite_eq_right h, map_zero]

theorem annihilator_gram_positive {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Module.End ℂ (Hilbert n)) (hB : ∀ r, reconstruct (B r) = B r)
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian)
    (hG : (createdGram B * C * createdGram B).PosSemidef) :
    (matrixLift B C).IsPositive := by
  let W : Matrix (Finset (Fin n)) ι ℂ := fun A r => (B r).adjoint (vacuum n) A
  have heq : W.conjTranspose * W = createdGram B := by
    ext r s
    change (∑ A : Finset (Fin n), star (W A r) * W A s) = _
    simp only [W, createdGram, PiLp.inner_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl (fun A _ => mul_comm _ _)
  have hp := matrixLift_gram_positive allBasisContraction W C hC (by rwa [heq])
  have hf (r : ι) : contractCombination allBasisContraction (fun A => W A r) = B r := hB r
  simpa only [hf] using hp

theorem local_four_family_transfer_of_gram {n L : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : ι → Fin L) (j k : ι → Fin n)
    (s : ℕ → κ → ι → ℝ) (s₀ : κ → ι → ℝ)
    (C : ℕ → Matrix κ κ ℂ) (C₀ : Matrix κ κ ℂ)
    (hs : ∀ r b, Filter.Tendsto (fun Q => s Q r b) Filter.atTop (𝓝 (s₀ r b)))
    (hC : ∀ r t, Filter.Tendsto (fun Q => C Q r t) Filter.atTop (𝓝 (C₀ r t)))
    (hC₀ : C₀.IsHermitian)
    (hG : let B := fun r => ∑ b, (s₀ r b : ℂ) •
        (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val)
      (createdGram B * C₀ * createdGram B).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (𝓝 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (x : Hilbert (n+m)),
        -(ρ Q) * (∑ a : Fin L, ‖extendLocal (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendLocal (matrixLift
            (fun r => ∑ b, (s Q r b : ℂ) •
              (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q)) x)).re := by
  apply local_four_family_transfer p j k s s₀ C C₀ hs hC
  apply annihilator_gram_positive _ _ C₀ hC₀ hG
  intro r
  simp only [map_sum, map_smul, localPairStar, reconstruct_four_pair]

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NormalOrder
attribute [-simp] _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Order. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma sum_increasing_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    2 * (∑ a : PairLabel n, f a.val.1 a.val.2) = ∑ i, ∑ j, f i j := by
  classical
  have htri : (∑ a : PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
      (by simp) (fun a => f a.1 a.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  rw [htri]
  conv_rhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]
  ring

lemma sphericalExteriorPairCoefficient_eq_tensor (Q p : ℕ) (i j : Fin (Q+1)) :
    sphericalExteriorPairCoefficient Q p i.val j.val = Real.sqrt 2 * pairCoefficient Q p i j := by
  unfold sphericalExteriorPairCoefficient pairCoefficient
  split_ifs
  · have h : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  · simp

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Creation
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma sum_symmetric_triangle {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → Fin n → A) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
  classical
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  conv_lhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]

lemma orderedPair_contraction (Q p : ℕ) :
    (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), (pairCoefficient Q p i j : ℂ) •
      (annihilation j * annihilation i)) =
    (Real.sqrt 2 : ℂ) • localPair (Q+1) Q p := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  let T : Module.End ℂ (Hilbert (Q+1)) := ∑ i, ∑ j, if i < j then
    (pairCoefficient Q p i j : ℂ) • (annihilation j * annihilation i) else 0
  have he : localPair (Q+1) Q p = (Real.sqrt 2 : ℂ) • T := by
    simp only [localPair, pairAnnihilator, sphericalExteriorPairCoefficient_eq_tensor,
      Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul, mul_smul, T,
      Finset.smul_sum, smul_ite, smul_zero]
  rw [sum_symmetric_triangle, he, smul_smul, hs]
  · change T + T = (2:ℂ) • T
    module
  · intro i j
    rw [pairCoefficient_swap Q p i j, annihilation_anticommute i j]
    simp
  · intro i
    simp [pairCoefficient]

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Occupation. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complexify_injective : Function.Injective (complexify (ι := ι)) := by
  intro A B h
  apply_fun Matrix.toEuclideanLin.symm at h
  simp only [complexify, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearEquiv.symm_apply_apply] at h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Lift. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma lift_transpose [DecidableEq ι] [DecidableEq κ]
    (B : ι → Matrix κ κ ℝ) (A : Matrix ι ι ℝ) :
    (lift B A).transpose = lift B A.transpose := by
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_sum,
    Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
lemma complexify_combination [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (a : ι → ℝ) :
    complexify (combination B a) = ∑ i, (a i : ℂ) • complexify (B i) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact_mod_cast (rfl : a i • complexify (B i) = a i • complexify (B i))

omit [DecidableEq ι] in
lemma complexify_lift [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (A : Matrix ι ι ℝ) :
    complexify (lift B A) = matrixLift (fun i => complexify (B i)) (A.map (algebraMap ℝ ℂ)) := by
  simp only [lift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    map_mul, complexify_transpose, Matrix.map_apply]
  rfl

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Work. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Topology
open Filter

theorem highestFactor_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z k : ℕ) :
    Tendsto (fun q => highestFactor (n q) (m q) z k) atTop (𝓝 r) := by
  have hquot : Tendsto
      (fun q => ((m q : ℝ) / n q + (-(z : ℝ) + k + 1) / n q) /
        (1 - (k : ℝ) / n q)) atTop (𝓝 r) := by
    simpa only [add_zero, sub_zero, div_one, Pi.div_def] using
      (hmn.add (hn.const_div_atTop (-(z : ℝ) + k + 1))).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (hn.const_div_atTop (k : ℝ)))
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
  apply hquot.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (k : ℝ))] with q hq
  have hN : (n q : ℝ) ≠ 0 := by
    have hk : (0 : ℝ) ≤ k := by positivity
    linarith
  have hNk : (n q : ℝ) - k ≠ 0 := by linarith
  dsimp [highestFactor]
  field_simp
  ring

theorem highestWeight_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestWeight (n q) (m q) z p) atTop
      (𝓝 ((z.choose p : ℝ) * r ^ p)) := by
  have h := (tendsto_const_nhds (x := (z.choose p : ℝ))).mul
    (tendsto_finsetProd (Finset.range p) (fun k _ => highestFactor_tendsto hn hmn z k))
  simpa only [Finset.prod_const, Finset.card_range, highestWeight] using h

theorem highestNormalization_tendsto {n m : ℕ → ℕ} {r : ℝ}
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z : ℕ) :
    Tendsto (fun q => highestNormalization (n q) (m q) z) atTop (𝓝 ((r+1)^z)) := by
  have hsum : (∑ p ∈ Finset.range (z+1), (z.choose p : ℝ) * r^p) = (r+1)^z := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro p hp
    simp [mul_comm]
  simpa only [highestNormalization, hsum] using
    tendsto_finsetSum (Finset.range (z+1)) (fun p _ => highestWeight_tendsto hn hmn z p)

theorem highestCoefficient_tendsto_ratio {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestCoefficient (n q) (m q) z p) atTop
      (𝓝 ((-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * r^p) /
        Real.sqrt ((r+1)^z))) := by
  have hpos : 0 < (r+1)^z := pow_pos (by linarith) z
  exact ((tendsto_const_nhds.mul (highestWeight_tendsto hn hmn z p).sqrt).div
    (highestNormalization_tendsto hn hmn z).sqrt (Real.sqrt_pos.mpr hpos).ne')

lemma sqrt_nat_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  induction k with
  | zero => simp
  | succ k hk => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), hk, pow_succ]

lemma highest_ratio_eq {r : ℝ} (hr : 0 ≤ r) (z p : ℕ) :
    (-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * r^p) /
      Real.sqrt ((r+1)^z) =
    limitingHighestCoefficient (Real.sqrt r / Real.sqrt (r+1))
      (1 / Real.sqrt (r+1)) z p := by
  by_cases hp : p ≤ z
  · have he : z = p + (z-p) := (Nat.add_sub_of_le hp).symm
    have hpos : Real.sqrt (r+1) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    rw [Real.sqrt_mul (by positivity), sqrt_nat_pow hr,
      sqrt_nat_pow (by linarith : 0 ≤ r+1)]
    unfold limitingHighestCoefficient
    rw [div_pow, div_pow, one_pow]
    rw [show Real.sqrt (r+1)^z = Real.sqrt (r+1)^p * Real.sqrt (r+1)^(z-p) by
      rw [← pow_add, Nat.add_sub_of_le hp]]
    ring
  · simp [Nat.choose_eq_zero_of_lt (by omega : z < p), limitingHighestCoefficient]

theorem highestCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z p : ℕ) :
    Tendsto (fun q => highestCoefficient (n q) (m q) z p) atTop
      (𝓝 (limitingHighestCoefficient (Real.sqrt r / Real.sqrt (r+1))
        (1 / Real.sqrt (r+1)) z p)) := by
  simpa only [highest_ratio_eq hr] using highestCoefficient_tendsto_ratio hr hn hmn z p

lemma firstAffineRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => ((n q : ℝ) + a) / ((n q : ℝ) + m q + b)) atTop
      (𝓝 (1 / (1+r))) := by
  have h : Tendsto (fun q => (1 + a / (n q : ℝ)) /
      (1 + (m q : ℝ) / n q + b / n q)) atTop (𝓝 (1 / (1+r))) := by
    simpa only [add_zero, Pi.div_def] using
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hn.const_div_atTop a)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).add hmn).add (hn.const_div_atTop b))
        (by linarith : 1 + r + 0 ≠ 0)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  simpa only [add_div, div_self hq.ne'] using
    div_div_div_cancel_right₀ hq.ne' ((n q : ℝ) + a) ((n q : ℝ) + m q + b)

lemma secondAffineRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => ((m q : ℝ) + a) / ((n q : ℝ) + m q + b)) atTop
      (𝓝 (r / (1+r))) := by
  have h : Tendsto (fun q => ((m q : ℝ) / n q + a / n q) /
      (1 + (m q : ℝ) / n q + b / n q)) atTop (𝓝 (r / (1+r))) := by
    simpa only [add_zero, Pi.div_def] using
      (hmn.add (hn.const_div_atTop a)).div
        (((tendsto_const_nhds (x := (1 : ℝ))).add hmn).add (hn.const_div_atTop b))
        (by linarith : 1 + r + 0 ≠ 0)
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with q hq
  simpa only [add_div, div_self hq.ne'] using
    div_div_div_cancel_right₀ hq.ne' ((m q : ℝ) + a) ((n q : ℝ) + m q + b)

lemma firstSqrtRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => Real.sqrt ((n q : ℝ) + a) /
      Real.sqrt ((n q : ℝ) + m q + b)) atTop (𝓝 (1 / Real.sqrt (1+r))) := by
  have h := (firstAffineRatio_tendsto hr hn hmn a b).sqrt
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (-b))] with q hq
  have hm : (0 : ℝ) ≤ m q := by positivity
  rw [Real.sqrt_div' _ (by linarith)]

lemma secondSqrtRatio_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (a b : ℝ) :
    Tendsto (fun q => Real.sqrt ((m q : ℝ) + a) /
      Real.sqrt ((n q : ℝ) + m q + b)) atTop
      (𝓝 (Real.sqrt r / Real.sqrt (1+r))) := by
  have h := (secondAffineRatio_tendsto hr hn hmn a b).sqrt
  rw [Real.sqrt_div hr] at h
  apply h.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (-b))] with q hq
  have hm : (0 : ℝ) ≤ m q := by positivity
  rw [Real.sqrt_div' _ (by linarith)]

lemma firstLoweringCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => firstLoweringCoefficient (n q) (m q) z l p) atTop
      (𝓝 (Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) / Real.sqrt (1+r))) := by
  have h := (firstSqrtRatio_tendsto hr hn hmn (1-(p : ℝ)) (-2*(z : ℝ)-l)).const_mul
    (Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1))
  have hf (q : ℕ) : firstLoweringCoefficient (n q) (m q) z l p =
      Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt ((n q : ℝ)+(1-(p : ℝ))) /
          Real.sqrt ((n q : ℝ)+m q+(-2*(z : ℝ)-l))) := by
    simp only [firstLoweringCoefficient, Real.sqrt_mul (Nat.cast_nonneg p),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)]
    ring_nf
  simpa only [hf, mul_one_div] using h

lemma secondLoweringCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ)
    (hp : p ≤ z+l+1) :
    Tendsto (fun q => secondLoweringCoefficient (n q) (m q) z l p) atTop
      (𝓝 (Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt r / Real.sqrt (1+r)))) := by
  have hp' : (0 : ℝ) ≤ (z : ℝ)+l-p+1 := by
    have h : (p : ℝ) ≤ (z : ℝ)+l+1 := by exact_mod_cast hp
    linarith
  have h := (secondSqrtRatio_tendsto hr hn hmn (-(z : ℝ)-l+p) (-2*(z : ℝ)-l)).const_mul
    (Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1))
  have hf (q : ℕ) : secondLoweringCoefficient (n q) (m q) z l p =
      Real.sqrt ((z : ℝ)+l-p+1) / Real.sqrt ((l : ℝ)+1) *
        (Real.sqrt ((m q : ℝ)+(-(z : ℝ)-l+p)) /
          Real.sqrt ((n q : ℝ)+m q+(-2*(z : ℝ)-l))) := by
    simp only [secondLoweringCoefficient, Real.sqrt_mul hp',
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)]
    ring_nf
  simpa only [hf] using h

lemma coupledCoefficient_eq_zero {n m z l p : ℕ} (hp : z+l < p) :
    coupledCoefficient n m z l p = 0 := by
  induction l generalizing p with
  | zero => exact highestCoefficient_eq_zero (by omega)
  | succ l ih =>
    simp [coupledCoefficient, ih (show z+l < p-1 by omega), ih (show z+l < p by omega)]

lemma limitingCoupledCoefficient_eq_zero {u v : ℝ} {z l p : ℕ} (hp : z+l < p) :
    limitingCoupledCoefficient u v z l p = 0 := by
  induction l generalizing p with
  | zero => simp [limitingCoupledCoefficient, limitingHighestCoefficient,
      Nat.choose_eq_zero_of_lt (show z < p by omega)]
  | succ l ih =>
    simp [limitingCoupledCoefficient, ih (show z+l < p-1 by omega), ih (show z+l < p by omega)]

theorem coupledCoefficient_tendsto {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (limitingCoupledCoefficient (Real.sqrt r / Real.sqrt (1+r))
        (1 / Real.sqrt (1+r)) z l p)) := by
  induction l generalizing p with
  | zero => simpa only [coupledCoefficient, limitingCoupledCoefficient, add_comm 1 r] using
      highestCoefficient_tendsto hr hn hmn z p
  | succ l ih =>
    by_cases hp : p ≤ z+l+1
    · have h₁ : Tendsto (fun q => if p = 0 then (0 : ℝ) else
          firstLoweringCoefficient (n q) (m q) z l p * coupledCoefficient (n q) (m q) z l (p-1))
        atTop (𝓝 (if p = 0 then 0 else
          Real.sqrt (p : ℝ) / Real.sqrt ((l : ℝ)+1) / Real.sqrt (1+r) *
            limitingCoupledCoefficient (Real.sqrt r / Real.sqrt (1+r))
              (1 / Real.sqrt (1+r)) z l (p-1))) := by
        split_ifs with hp0
        · exact tendsto_const_nhds
        · exact (firstLoweringCoefficient_tendsto hr hn hmn z l p).mul (ih (p-1))
      have h₂ := (secondLoweringCoefficient_tendsto hr hn hmn z l p hp).mul (ih p)
      convert h₁.add h₂ using 1
      · rfl
      · congr 1
        simp only [limitingCoupledCoefficient]
        split_ifs <;> ring
    · simpa only [coupledCoefficient_eq_zero (show z+(l+1) < p by omega),
        limitingCoupledCoefficient_eq_zero (show z+(l+1) < p by omega)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

open Polynomial

lemma binomial_linear_coeff (u v : ℝ) (z p : ℕ) :
    ((C u * X - C v)^z).coeff p = (z.choose p : ℝ) * u^p * (-v)^(z-p) := by
  have h := comp_C_mul_X_coeff (p := (X + C (-v))^z) (r := u) (n := p)
  simp only [pow_comp, add_comp, X_comp, C_comp, coeff_X_add_C_pow] at h
  rw [map_neg] at h
  rw [sub_eq_add_neg]
  rw [h]
  ring

lemma monomialWeight_choose {z p : ℕ} (hp : p ≤ z) :
    monomialWeight z p * (z.choose p : ℝ) / Real.sqrt (z.factorial : ℝ) =
      Real.sqrt (z.choose p : ℝ) := by
  have hc : (z.choose p : ℝ) * (p.factorial : ℝ) * ((z-p).factorial : ℝ) =
      (z.factorial : ℝ) := by exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hp)
  have hs : Real.sqrt (z.choose p : ℝ) * monomialWeight z p =
      Real.sqrt (z.factorial : ℝ) := by
    rw [monomialWeight, ← Real.sqrt_mul (by positivity)]
    congr 1
    simpa only [mul_assoc] using hc
  apply (div_eq_iff (Real.sqrt_pos.mpr (by exact_mod_cast z.factorial_pos)).ne').mpr
  rw [← hs]
  have he : Real.sqrt (z.choose p : ℝ) ^ 2 = (z.choose p : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    _ = monomialWeight z p * Real.sqrt (z.choose p : ℝ) ^ 2 := by rw [he]
    _ = _ := by ring

lemma highestCoefficient_eq_polynomial (u v : ℝ) (z p : ℕ) :
    limitingHighestCoefficient u v z p =
      monomialWeight z p * (couplingPolynomial u v z 0).coeff p := by
  simp only [couplingPolynomial, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one,
    mul_one, pow_zero, coeff_C_mul, binomial_linear_coeff]
  by_cases hp : p ≤ z
  · rw [show (-v)^(z-p) = (-1 : ℝ)^(z-p)*v^(z-p) by rw [← mul_pow]; congr 1; ring]
    calc
      limitingHighestCoefficient u v z p =
          (monomialWeight z p * (z.choose p : ℝ) / Real.sqrt (z.factorial : ℝ)) *
            (-1 : ℝ)^(z-p)*u^p*v^(z-p) := by
        rw [monomialWeight_choose hp]
        unfold limitingHighestCoefficient
        ring
      _ = _ := by ring
  · simp [limitingHighestCoefficient, Nat.choose_eq_zero_of_lt (show z < p by omega)]

lemma couplingPolynomial_step (u v : ℝ) (z l : ℕ) :
    couplingPolynomial u v z (l+1) =
      C (1 / Real.sqrt ((l : ℝ)+1)) *
        ((C v * X + C u) * couplingPolynomial u v z l) := by
  have hf : Real.sqrt ((l+1).factorial : ℝ) =
      Real.sqrt ((l : ℝ)+1) * Real.sqrt (l.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.sqrt_mul (by positivity)]
  have hn : 1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt ((l+1).factorial : ℝ)) =
      (1 / Real.sqrt ((l : ℝ)+1)) *
        (1 / (Real.sqrt (z.factorial : ℝ) * Real.sqrt (l.factorial : ℝ))) := by
    rw [hf]
    ring
  unfold couplingPolynomial
  rw [hn, map_mul, pow_succ]
  ring

lemma couplingPolynomial_natDegree_le (u v : ℝ) (z l : ℕ) :
    (couplingPolynomial u v z l).natDegree ≤ z+l := by
  have ha : (C u * X - C v : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  have hb : (C v * X + C u : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  unfold couplingPolynomial
  apply natDegree_mul_le.trans
  apply add_le_add
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by nlinarith))
  · exact natDegree_pow_le.trans (by nlinarith)

lemma couplingPolynomial_coeff_eq_zero {u v : ℝ} {z l p : ℕ} (hp : z+l < p) :
    (couplingPolynomial u v z l).coeff p = 0 :=
  coeff_eq_zero_of_natDegree_lt ((couplingPolynomial_natDegree_le u v z l).trans_lt hp)

lemma monomialWeight_first {T p : ℕ} (hp : 0 < p) (hpT : p ≤ T+1) :
    monomialWeight (T+1) p = Real.sqrt (p : ℝ) * monomialWeight T (p-1) := by
  have hpp : (p-1)+1 = p := by omega
  have hfac : p.factorial = p * (p-1).factorial := by
    simpa only [hpp] using Nat.factorial_succ (p-1)
  have hTp : (T+1)-p = T-(p-1) := by omega
  simp only [monomialWeight, hfac, Nat.cast_mul, hTp]
  rw [← Real.sqrt_mul (Nat.cast_nonneg p)]
  congr 1
  ring

lemma monomialWeight_second {T p : ℕ} (hp : p ≤ T) :
    monomialWeight (T+1) p =
      Real.sqrt ((T : ℝ)-p+1) * monomialWeight T p := by
  have hTp : (T+1)-p = (T-p)+1 := by omega
  simp only [monomialWeight, hTp, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hp]
  rw [← Real.sqrt_mul (by
    have h : (p : ℝ) ≤ T := by exact_mod_cast hp
    linarith : (0 : ℝ) ≤ (T : ℝ)-p+1)]
  congr 1
  ring

lemma couplingPolynomial_step_coeff (u v : ℝ) (z l p : ℕ) :
    (couplingPolynomial u v z (l+1)).coeff p =
      ((if p = 0 then 0 else v * (couplingPolynomial u v z l).coeff (p-1)) +
        u * (couplingPolynomial u v z l).coeff p) / Real.sqrt ((l : ℝ)+1) := by
  rw [couplingPolynomial_step, coeff_C_mul, add_mul, mul_assoc (C v), coeff_add]
  simp only [coeff_C_mul]
  cases p with
  | zero => simp [div_eq_mul_inv, mul_comm]
  | succ p => simp [coeff_X_mul, mul_add, mul_comm, div_eq_mul_inv, mul_left_comm]

theorem limitingCoupledCoefficient_eq_polynomial (u v : ℝ) (z l p : ℕ) :
    limitingCoupledCoefficient u v z l p =
      monomialWeight (z+l) p * (couplingPolynomial u v z l).coeff p := by
  induction l generalizing p with
  | zero => simpa only [Nat.add_zero, limitingCoupledCoefficient] using
      highestCoefficient_eq_polynomial u v z p
  | succ l ih =>
    by_cases hp : p ≤ z+l+1
    · have hfirst : monomialWeight (z+l+1) p *
          (if p = 0 then 0 else v * (couplingPolynomial u v z l).coeff (p-1)) =
        (if p = 0 then 0 else Real.sqrt (p : ℝ) * v *
          (monomialWeight (z+l) (p-1) * (couplingPolynomial u v z l).coeff (p-1))) := by
        split_ifs with hp0
        · simp
        · rw [monomialWeight_first (by omega : 0 < p) hp]
          ring
      have hsecond : monomialWeight (z+l+1) p *
          (u * (couplingPolynomial u v z l).coeff p) =
        Real.sqrt ((z : ℝ)+l-p+1) * u *
          (monomialWeight (z+l) p * (couplingPolynomial u v z l).coeff p) := by
        by_cases hpT : p ≤ z+l
        · rw [monomialWeight_second hpT, Nat.cast_add]
          ring
        · rw [couplingPolynomial_coeff_eq_zero (by omega : z+l < p)]
          ring
      simp only [limitingCoupledCoefficient, ih, couplingPolynomial_step_coeff,
        ← Nat.add_assoc]
      rw [← mul_div_assoc, mul_add, hfirst, hsecond]
    · rw [limitingCoupledCoefficient_eq_zero (by omega : z+(l+1) < p),
        couplingPolynomial_coeff_eq_zero (by omega : z+(l+1) < p), mul_zero]

theorem coupledCoefficient_tendsto_polynomial {n m : ℕ → ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hn : Tendsto (fun q => (n q : ℝ)) atTop atTop)
    (hmn : Tendsto (fun q => (m q : ℝ) / n q) atTop (𝓝 r)) (z l p : ℕ) :
    Tendsto (fun q => coupledCoefficient (n q) (m q) z l p) atTop
      (𝓝 (monomialWeight (z+l) p *
        (couplingPolynomial (Real.sqrt r / Real.sqrt (1+r))
          (1 / Real.sqrt (1+r)) z l).coeff p)) := by
  simpa only [limitingCoupledCoefficient_eq_polynomial] using
    coupledCoefficient_tendsto hr hn hmn z l p

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwiningSpin
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.nestedBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwining Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

namespace LadderMap
variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
variable {S : LadderSystem ι} {T : LadderSystem κ} {U : LadderSystem σ}

lemma weight (A : LadderMap S T) (x : ι → ℝ) :
    T.weight (A.toLinearMap x) = A.toLinearMap (S.weight x) := by
  rw [T.weight_eq, A.raise, A.lower, S.weight_eq, map_sub, A.lower, A.raise]

lemma casimir (A : LadderMap S T) (x : ι → ℝ) :
    T.casimir (A.toLinearMap x) = A.toLinearMap (S.casimir x) := by
  simp only [LadderSystem.casimir_apply, A.weight, A.lower, A.raise, map_add, map_smul]

lemma raw (A : LadderMap S T) (x : ι → ℝ) (l : ℕ) :
    T.raw (A.toLinearMap x) l = A.toLinearMap (S.raw x l) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [LadderSystem.raw_succ, LadderSystem.raw_succ, ih, A.lower]

lemma normalized (A : LadderMap S T) (x : ι → ℝ) (d l : ℕ) :
    T.normalized (A.toLinearMap x) d l = A.toLinearMap (S.normalized x d l) := by
  simp only [LadderSystem.normalized, map_smul, A.raw]

end LadderMap

theorem coupledTensor_expansion (n m : ℕ)
    (y : (Fin (n+1) × Fin (m+1)) → ℝ) :
    (∑ i : CoupledIndex n m,
      dotProduct (coupledTensor n m i.1.val i.2.val) y •
        coupledTensor n m i.1.val i.2.val) = y := by
  funext pq
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) => x pq)
    ((coupledBasis n m).sum_repr (WithLp.toLp 2 y))
  simpa only [OrthonormalBasis.repr_apply_apply, coupledBasis_apply, coupledFamily,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.smul_apply, WithLp.toLp_ofLp, Pi.smul_apply,
    smul_eq_mul, dotProduct, mul_comm] using h

lemma spinCasimir_injective :
    Function.Injective (fun d : ℕ => (d : ℝ)*(d+2)) := by
  intro d e h
  have hd : (0 : ℝ) ≤ d := by positivity
  have he : (0 : ℝ) ≤ e := by positivity
  have hs : 0 < (d : ℝ)+e+2 := by positivity
  have hh : ((d : ℝ)-e)*((d : ℝ)+e+2) = 0 := by nlinarith
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hs.ne')
  exact_mod_cast heq

theorem coupledHighest_eigenline {n m z : ℕ} (hz : z ≤ min n m)
    {y : (Fin (n+1) × Fin (m+1)) → ℝ}
    (hyH : (tensorSpin n m).weight y = ((n+m-2*z : ℕ) : ℝ) • y)
    (hyC : (tensorSpin n m).casimir y =
      (((n+m-2*z : ℕ) : ℝ)*((n+m-2*z : ℕ)+2)) • y) :
    y = dotProduct (highestTensor n m z) y • highestTensor n m z := by
  classical
  let iz : CoupledIndex n m := ⟨⟨z,by omega⟩,0⟩
  calc
    y = ∑ i : CoupledIndex n m,
        dotProduct (coupledTensor n m i.1.val i.2.val) y •
          coupledTensor n m i.1.val i.2.val := (coupledTensor_expansion n m y).symm
    _ = dotProduct (highestTensor n m z) y • highestTensor n m z := by
      apply Finset.sum_eq_single iz
      · intro i _ hne
        obtain ⟨w,k⟩ := i
        have hw : w.val ≤ min n m := Nat.le_of_lt_succ w.isLt
        have hk : k.val ≤ n+m-2*w.val := Nat.le_of_lt_succ k.isLt
        have horth : dotProduct (coupledTensor n m w.val k.val) y = 0 := by
          by_cases hwz : w.val=z
          · have hk0 : k.val ≠ 0 := by
              intro hk0
              apply hne
              apply Sigma.ext
              · exact Fin.ext hwz
              · apply (Fin.heq_ext_iff (by dsimp [iz]; omega)).mpr
                exact hk0
            apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).weight_adjoint
              (coupledTensor_weight hw hk) hyH
            simp only [hwz]
            intro hh
            apply hk0
            have : (k.val : ℝ) = 0 := by linarith
            exact_mod_cast this
          · apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).casimir_adjoint
              (coupledTensor_casimir hw hk) hyC
            intro hh
            have HD := spinCasimir_injective hh
            have := le_min_iff.mp hw
            have := le_min_iff.mp hz
            omega
        rw [horth, zero_smul]
      · simp

lemma LadderSystem.raw_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (l : ℕ) : S.raw (c • x) l = c • S.raw x l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [S.raw_succ, ih, map_smul, S.raw_succ]

lemma LadderSystem.normalized_smul {ι : Type*} [Fintype ι] (S : LadderSystem ι)
    (c : ℝ) (x : ι → ℝ) (d l : ℕ) :
    S.normalized (c • x) d l = c • S.normalized x d l := by
  simp only [LadderSystem.normalized, S.raw_smul, smul_comm c]

theorem tensorSpin_schur {n m z l : ℕ} (hz : z ≤ min n m) (hl : l ≤ n+m-2*z)
    (A : LadderMap (tensorSpin n m) (tensorSpin n m)) :
    A.toLinearMap (coupledTensor n m z l) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        coupledTensor n m z l := by
  have hh : A.toLinearMap (highestTensor n m z) =
      dotProduct (highestTensor n m z) (A.toLinearMap (highestTensor n m z)) •
        highestTensor n m z := by
    apply coupledHighest_eigenline hz
    · rw [A.weight, highestTensor_weight hz, map_smul]
    · rw [A.casimir]
      have hc := coupledTensor_casimir hz (by omega : 0 ≤ n+m-2*z)
      rw [coupledTensor_zero] at hc
      rw [hc, map_smul]
  rw [coupledTensor_eq_normalized hz hl, ← A.normalized]
  conv_lhs => rw [hh, LadderSystem.normalized_smul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalAveraging
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.combination_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

@[simp] lemma complexify_physicalPair (Q p : ℕ) :
    complexify (physicalPair Q p) = Occupation.localPair (Q+1) Q p := by
  rw [physicalPair, map_smul, complexify_combination]
  simp only [productFamily, map_mul, complexify_annihilation, Fintype.sum_prod_type,
    physicalPairTensor, Occupation.orderedPair_contraction]
  have he : (1/Real.sqrt 2 : ℝ) • ((Real.sqrt 2 : ℂ) • Occupation.localPair (Q+1) Q p) =
      ((1/Real.sqrt 2)*Real.sqrt 2 : ℝ) • Occupation.localPair (Q+1) Q p := by
    rw [mul_smul]; rfl
  rw [he, one_div_mul_cancel (by positivity : Real.sqrt 2 ≠ 0), one_smul]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_HighestRatios
attribute [-simp] _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest Ratios. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma highest_numerator_product {m z : ℕ} (hz : z ≤ m) (p : ℕ) :
    (∏ k ∈ Finset.range p, ((m : ℝ)-z+k+1)) =
      ((m-z+p).descFactorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih]
    rw [show m-z+(p+1) = (m-z+p)+1 by omega, Nat.succ_descFactorial_succ]
    push_cast
    rw [Nat.cast_sub hz]
    ring

lemma highest_denominator_product {n p : ℕ} (hp : p ≤ n) :
    (∏ k ∈ Finset.range p, ((n : ℝ)-k)) = (n.descFactorial p : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.cast_sub ((Finset.mem_range.mp hk).le.trans hp)]

theorem highestWeight_factorial {n m z p : ℕ} (hz : z ≤ min n m) (hp : p ≤ z) :
    highestWeight n m z p = (z.choose p : ℝ) *
      ((m-z+p).descFactorial p : ℝ) / (n.descFactorial p : ℝ) := by
  simp only [highestWeight, highestFactor, Finset.prod_div_distrib,
    highest_numerator_product (le_min_iff.mp hz).2 p,
    highest_denominator_product (hp.trans (le_min_iff.mp hz).1), mul_div_assoc]

lemma highestCoefficient_zero_ne {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z 0 ≠ 0 := by
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Real.sqrt_pos.mpr (highestNormalization_pos hz)).ne'

theorem highestCoefficient_ratio {n m z p : ℕ} (_hz : z ≤ min n m) (hp : p ≤ z) :
    highestCoefficient n m z p = highestCoefficient n m z 0 *
      ((-1 : ℝ)^p * Real.sqrt (highestWeight n m z p)) := by
  have he : (-1 : ℝ)^(z-p) = (-1 : ℝ)^z * (-1 : ℝ)^p := by
    have hzz : z=(z-p)+p := by omega
    conv_rhs => rw [hzz, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  simp only [highestCoefficient, highestWeight_zero, Real.sqrt_one, mul_one, Nat.sub_zero]
  rw [he]
  ring

lemma highestCoefficient_last {n m z : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z z = highestCoefficient n m z 0 *
      ((-1 : ℝ)^z * Real.sqrt ((m.descFactorial z : ℝ)/(n.descFactorial z : ℝ))) := by
  rw [highestCoefficient_ratio hz (le_refl z), highestWeight_factorial hz (le_refl z),
    Nat.sub_add_cancel (le_min_iff.mp hz).2, Nat.choose_self, Nat.cast_one, one_mul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairDecomposition
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Decomposition. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

lemma highestCoefficient_last_equal_spin {Q r : ℕ} (hr : r ≤ Q) :
    highestCoefficient Q Q r r = (-1 : ℝ)^r * highestCoefficient Q Q r 0 := by
  have hf : (Q.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hr).ne'
  rw [highestCoefficient_last (by simpa using hr), div_self hf, Real.sqrt_one, mul_one,
    mul_comm]

theorem coupledTensor_swap {Q r l : ℕ} (hr : r ≤ Q) (hl : l ≤ Q+Q-2*r)
    (i j : Fin (Q+1)) :
    coupledTensor Q Q r l (j,i) = (-1 : ℝ)^r * coupledTensor Q Q r l (i,j) := by
  have h0 := tensorSpin_schur (by simpa using hr : r ≤ min Q Q)
    (Nat.zero_le _) (tensorSwap Q)
  let r' : Fin (Q+1) := ⟨r, by omega⟩
  have hc := congrFun h0 (0,r')
  simp only [coupledTensor_zero, tensorSwap, highestTensor, LinearMap.coe_mk,
    AddHom.coe_mk, Fin.val_zero, r', zero_add, add_zero, ite_true, Pi.smul_apply,
    smul_eq_mul] at hc
  have hb : dotProduct (highestTensor Q Q r)
      ((tensorSwap Q).toLinearMap (highestTensor Q Q r)) = (-1 : ℝ)^r := by
    apply mul_right_cancel₀ (highestCoefficient_zero_ne (by simpa using hr : r ≤ min Q Q))
    exact hc.symm.trans (highestCoefficient_last_equal_spin hr)
  have h := congrFun (tensorSpin_schur (by simpa using hr : r ≤ min Q Q) hl
    (tensorSwap Q)) (i,j)
  rw [hb] at h
  exact h

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation Filter Topology

lemma affine_twice_spin_tendsto (r : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_mono (fun Q => show Q-r ≤ 2*Q-2*r by omega)
  exact tendsto_sub_atTop_nat r

lemma affine_twice_spin_ratio_tendsto (r : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ) / (2*Q-2 : ℕ)) atTop (𝓝 (1:ℝ)) := by
  have h := ((tendsto_const_nhds (x := (1:ℝ))).sub
    ((tendsto_const_nhds (x := ((2*r:ℕ):ℝ)-2)).div_atTop (affine_twice_spin_tendsto 1)))
  simp only [sub_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (max r 1+1)] with Q hQ
  have hr : 2*r ≤ 2*Q := by omega
  have h2 : 2 ≤ 2*Q := by omega
  have hd : ((2*Q-2 : ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-2 ≠ 0 by omega)
  simp only [Nat.cast_sub hr, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2]
  simp only [Nat.cast_sub h2, Nat.cast_mul, Nat.cast_ofNat] at hd
  calc
    _ = ((2*(Q:ℝ)-2) - (2*(r:ℝ)-2)) / (2*(Q:ℝ)-2) := by
      conv_rhs => rw [sub_div, div_self hd]
    _ = _ := by congr 1; ring

lemma equal_spin_ratio_tendsto :
    Tendsto (fun Q : ℕ => (Q:ℝ)/Q) atTop (𝓝 (1:ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  exact (div_self (Nat.cast_ne_zero.mpr (by omega))).symm

lemma balanced_coupling_limit {n m : ℕ → ℕ}
    (hn : Tendsto (fun Q => (n Q : ℝ)) atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ)/(n Q:ℝ)) atTop (𝓝 (1:ℝ)))
    {z T : ℕ} (hzT : z ≤ T) (p : ℕ) :
    Tendsto (fun Q => coupledCoefficient (n Q) (m Q) z (T-z) p) atTop
      (𝓝 (balancedCouplingCoefficient z T p)) := by
  have h := coupledCoefficient_tendsto_polynomial (by norm_num : (0:ℝ) ≤ 1) hn hr z (T-z) p
  simpa [balancedCouplingCoefficient, hzT, Nat.add_sub_of_le hzT,
    show (1:ℝ)+1=2 by norm_num] using h

theorem fourBodyCoefficient_tendsto {D T r : ℕ} (hrD : r ≤ D) (hDT : D ≤ T)
    (p j k : ℕ) :
    Tendsto (fun Q => fourBodyCoefficient Q D T r p j k) atTop
      (𝓝 (fourBodyCoefficientStar D T r p j k)) := by
  by_cases h : r ≤ j+k ∧ p+j+k=T
  · simp only [fourBodyCoefficient, fourBodyCoefficientStar, ite_eq_left h]
    have h₁ := balanced_coupling_limit tendsto_natCast_atTop_atTop
      equal_spin_ratio_tendsto h.1 j
    have h₂ := balanced_coupling_limit (affine_twice_spin_tendsto 1)
      (affine_twice_spin_ratio_tendsto r) (show D-r ≤ T-r by omega) p
    have he : T-r-(D-r)=T-D := by omega
    simpa only [he, mul_one] using (h₁.const_mul (Real.sqrt 2)).mul h₂
  · simp only [fourBodyCoefficient, fourBodyCoefficientStar, ite_eq_right h]
    exact tendsto_const_nhds

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma nestedTensor_flip (n Q r z l : ℕ) (hr : r ≤ Q) (_hl : l ≤ n+(2*Q-2*r)-2*z)
    (a : Fin (n+1)) (j k : Fin (Q+1)) :
    nestedTensor n Q Q r z l (a,(k,j)) = (-1:ℝ)^r * nestedTensor n Q Q r z l (a,(j,k)) := by
  unfold nestedTensor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coupledTensor_swap hr (Nat.le_of_lt_succ q.isLt)]
  ring

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma annihilation_anticommute' {n : ℕ} (j k : Fin n) :
    annihilation k * annihilation j = -(annihilation j * annihilation k) := by
  apply complexify_injective
  simpa only [map_mul, map_neg, complexify_annihilation] using
    Occupation.annihilation_anticommute k j

lemma physicalFour_flip (Q : ℕ) (a : Fin (2*Q-2+1)) (j k : Fin (Q+1)) :
    physicalFour Q (a,(k,j)) = -physicalFour Q (a,(j,k)) := by
  simp only [physicalFour, productFamily]
  rw [annihilation_anticommute' k j, neg_mul, smul_neg]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_LowNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low Nested. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma lowNested_coefficient {Q D T r : ℕ} (hrD : r ≤ D)
    (hDT : D ≤ T) (hT : T ≤ Q)
    (a : Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) :
    Real.sqrt 2 * nestedTensor (2*Q-2) Q Q r (D-r) (T-D) a =
      fourBodyCoefficient Q D T r a.1.val a.2.1.val a.2.2.val := by
  classical
  unfold nestedTensor fourBodyCoefficient
  by_cases hw : r ≤ a.2.1.val+a.2.2.val ∧ a.1.val+a.2.1.val+a.2.2.val=T
  · rw [ite_eq_left hw]
    let l : Fin (Q+Q-2*r+1) := ⟨a.2.1.val+a.2.2.val-r, by omega⟩
    rw [Finset.sum_eq_single l]
    · simp only [coupledTensor]
      rw [ite_eq_left (by dsimp [l]; omega), ite_eq_left (by dsimp [l]; omega)]
      dsimp [l]
      rw [show Q+Q=2*Q by omega]
      ring
    · intro k hk hkl
      have he : a.2.1.val+a.2.2.val ≠ r+k.val := by
        intro he
        apply hkl
        apply Fin.ext
        dsimp [l]
        omega
      simp only [coupledTensor, ite_eq_right he, mul_zero]
    · simp
  · rw [ite_eq_right hw]
    have he : (∑ k : Fin (Q+Q-2*r+1),
        coupledTensor (2*Q-2) (Q+Q-2*r) (D-r) (T-D) (a.1,k) *
          coupledTensor Q Q r k.val a.2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [coupledTensor]
      split_ifs with h₁ h₂ h₂ <;> try simp
      exfalso
      exact hw ⟨by omega, by omega⟩
    rw [he, mul_zero]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Positivity. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
lemma transpose_square_positive [DecidableEq ι] (B : Matrix ι ι ℝ) :
    (B.transpose * B).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self B

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma RowEntry.balance {t : Fin 8} (a : RowEntry t) :
    t.val+a.output.val = a.val.1.val+a.val.2.val := by
  dsimp [RowEntry.output]; have := a.property; omega

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExtendedPair
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.creationCombination_single _root_.OAI.LaughlinGap.Occupation.exteriorLift_single _root_.OAI.LaughlinGap.Occupation.normalizedReadout_apply _root_.OAI.LaughlinGap.Occupation.normalizedReadout_increasing _root_.OAI.LaughlinGap.Occupation.rawReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorExtract_toEuclideanLin _root_.OAI.LaughlinGap.Occupation.sectorReadout_apply _root_.OAI.LaughlinGap.Occupation.sectorReadout_inclusion _root_.OAI.LaughlinGap.RealOccupation.complexify_annihilation _root_.OAI.LaughlinGap.RealOccupation.complexify_physicalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extended Pair. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators ComplexOrder

lemma endCongr_transition {n m : ℕ} (h : n=m) (j : Fin n) (ε : Bool) :
    endCongr h (transition j ε) = transition (Fin.cast h j) ε := by subst m; rfl

lemma endCongr_adjoint {n m : ℕ} (h : n=m) (T : Module.End ℂ (Hilbert n)) :
    endCongr h T.adjoint = (endCongr h T).adjoint := by subst m; rfl

lemma endCongr_extendLocal {n m k : ℕ} (h : m=k) (T : Module.End ℂ (Hilbert n)) :
    endCongr (congrArg (n+·) h) (extendLocal (m := m) T) = extendLocal (m := k) T := by
  subst k
  rfl

@[simp] lemma extendTo_add_dim (n m : ℕ) (T : Module.End ℂ (Hilbert n)) :
    extendTo (Nat.le_add_right n m) T = extendLocal (m := m) T := by
  exact endCongr_extendLocal (Nat.add_sub_cancel_left n m) T

@[simp] lemma extendTo_annihilation {n m : ℕ} (h : n ≤ m) (j : Fin n) :
    extendTo h (annihilation j) = annihilation (Fin.castLE h j) := by
  simp only [extendTo,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,annihilation]
  change endCongr _ (extendLocal (transition j false)) = _
  rw [extendLocal_transition,endCongr_transition]
  rfl

@[simp] lemma extendTo_adjoint {n m : ℕ} (h : n ≤ m) (T : Module.End ℂ (Hilbert n)) :
    extendTo h T.adjoint = (extendTo h T).adjoint := by
  simp only [extendTo,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom]
  change endCongr _ (extendLocal T.adjoint) = (endCongr _ (extendLocal T)).adjoint
  rw [← extendLocal_adjoint,endCongr_adjoint]

lemma extendTo_matrixLift {n m : ℕ} (h : n ≤ m) {ι : Type*} [Fintype ι]
    (B : ι → Module.End ℂ (Hilbert n)) (C : Matrix ι ι ℂ) :
    extendTo h (matrixLift B C) = matrixLift (fun r => extendTo h (B r)) C := by
  simp only [matrixLift,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,map_mul,extendTo_adjoint]

lemma localPair_support {n Q p : ℕ} (i j : Fin n) (h : i.val+j.val ≠ p+1) :
    (sphericalExteriorPairCoefficient Q p i.val j.val : ℂ) = 0 := by
  simp [sphericalExteriorPairCoefficient,h]

lemma extendTo_localPair {n m Q p : ℕ} (h : n ≤ m) (hp : p+1 < n) :
    extendTo h (localPair n Q p) = localPair m Q p := by
  classical
  simp only [localPair,pairAnnihilator,map_sum,apply_ite,map_smul,map_mul,
    extendTo_annihilation,map_zero]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  apply Finset.sum_bij_ne_zero (fun a _ _ => (Fin.castLE h a.1,Fin.castLE h a.2))
  · simp
  · intro a ha ha0 b hb hb0 he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun x : Fin m × Fin m => x.1.val) he)
    · exact Fin.ext (congrArg (fun x : Fin m × Fin m => x.2.val) he)
  · intro b hb hb0
    have hw : b.1.val+b.2.val=p+1 := by
      by_contra hn
      exact hb0 (by simp [localPair_support b.1 b.2 hn])
    let a : Fin n × Fin n := (⟨b.1.val,by omega⟩,⟨b.2.val,by omega⟩)
    have he : (Fin.castLE h a.1,Fin.castLE h a.2)=b := by apply Prod.ext <;> rfl
    exact ⟨a,Finset.mem_univ _,by simpa [a] using hb0,he⟩
  · intro a ha ha0
    rfl

theorem local_four_family_transfer_to {n L : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : ι → Fin L) (j k : ι → Fin n)
    (s : ℕ → κ → ι → ℝ) (s₀ : κ → ι → ℝ)
    (C : ℕ → Matrix κ κ ℂ) (C₀ : Matrix κ κ ℂ)
    (hs : ∀ r b, Filter.Tendsto (fun Q => s Q r b) Filter.atTop (nhds (s₀ r b)))
    (hC : ∀ r t, Filter.Tendsto (fun Q => C Q r t) Filter.atTop (nhds (C₀ r t)))
    (hC₀ : C₀.IsHermitian)
    (hG : let B := fun r => ∑ b, (s₀ r b : ℂ) •
        (annihilation (k b) * annihilation (j b) * localPairStar n (p b).val)
      (createdGram B * C₀ * createdGram B).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Filter.Tendsto ρ Filter.atTop (nhds 0) ∧
      ∀ᶠ Q in Filter.atTop, ∀ m (h : n ≤ m) (x : Hilbert m),
        -(ρ Q) * (∑ a : Fin L, ‖extendTo h (localPair n Q a.val) x‖ ^ 2) ≤
          (inner ℂ x (extendTo h (matrixLift
            (fun r => ∑ b, (s Q r b : ℂ) •
              (annihilation (k b) * annihilation (j b) * localPair n Q (p b).val)) (C Q)) x)).re := by
  obtain ⟨ρ,hpos,hlim,hbound⟩ := local_four_family_transfer_of_gram p j k s s₀ C C₀ hs hC hC₀ hG
  refine ⟨ρ,hpos,hlim,?_⟩
  filter_upwards [hbound] with Q hQ
  intro m hm x
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa only [extendTo_add_dim] using hQ d x

end LaughlinGap.Occupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourHighest
attribute [-simp] _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Highest. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma sum_increasing_matrices {n : ℕ} {κ : Type*} (f : Fin n → Fin n → Matrix κ κ ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (2:ℝ) • (∑ a : Occupation.PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, f i j := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Occupation.sum_increasing_pairs (fun i j => f i j x y)
    (fun i j => congrFun (congrFun (hs i j) x) y)
    (fun i => congrFun (congrFun (hd i) x) y)

lemma annihilation_square_zero {n : ℕ} (i : Fin n) : annihilation i * annihilation i = 0 := by
  apply complexify_injective
  rw [map_mul, map_zero, complexify_annihilation]
  exact Occupation.transition_square i false

lemma fourAnnihilator_exterior {Q D T r : ℕ} (hQ : 2 ≤ Q)
    (hT : T ≤ Q) (hD : D ≤ T) (hr : r ≤ D) (ho : Odd r) :
    fourAnnihilator Q D T r =
      ∑ p : Fin (2*Q-2+1), ∑ a : Occupation.PairLabel (Q+1),
        fourBodyCoefficient Q D T r p.val a.val.1.val a.val.2.val •
          (annihilation a.val.2 * annihilation a.val.1 * physicalPair Q p.val) := by
  classical
  simp only [fourAnnihilator, combination, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  have hf (j k : Fin (Q+1)) :
      nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(k,j)) =
        -nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(j,k)) := by
    rw [nestedTensor_flip _ _ _ _ _ (by omega) (by omega), ho.neg_one_pow, neg_one_mul]
  let f := fun j k : Fin (Q+1) =>
    nestedTensor (2*Q-2) Q Q r (D-r) (T-D) (p,(j,k)) • physicalFour Q (p,(j,k))
  have hs (j k : Fin (Q+1)) : f j k = f k j := by
    dsimp [f]
    rw [hf, physicalFour_flip, neg_smul, smul_neg, neg_neg]
  have hd (j : Fin (Q+1)) : f j j = 0 := by
    simp [f, physicalFour, productFamily, annihilation_square_zero]
  rw [← sum_increasing_matrices f hs hd, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [f]
  rw [physicalFour, productFamily, productFamily, smul_smul, smul_smul,
    ← lowNested_coefficient hr hD hT (p,(a.val.1,a.val.2))]
  congr 1
  have hn := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  field_simp
  rw [hn]
  ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourAllowance
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val _root_.OAI.LaughlinGap.Spin.spinPairForms_physical_index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Allowance. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

lemma orbitalTripleFinite_injective {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    Function.Injective (orbitalTripleFinite hQ hD) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : FourCoordinates Q => x.1.val) he
  · apply Prod.ext
    · exact congrArg (fun x : FourCoordinates Q => x.2.val.1.val) he
    · exact congrArg (fun x : FourCoordinates Q => x.2.val.2.val) he

lemma sum_orbitalTriple {Q D : ℕ} {M : Type*} [AddCommMonoid M]
    (hQ : 2 ≤ Q) (hD : D ≤ Q) (f : FourCoordinates Q → M)
    (hf : ∀ a, a.1.val+a.2.val.1.val+a.2.val.2.val ≠ D → f a = 0) :
    ∑ b : OrbitalTriple D, f (orbitalTripleFinite hQ hD b) = ∑ a, f a := by
  classical
  apply Finset.sum_bij_ne_zero (fun b _ _ => orbitalTripleFinite hQ hD b)
  · simp
  · intros a _ _ b _ _ he
    exact orbitalTripleFinite_injective hQ hD he
  · intro a ha hfa
    have hw : a.1.val+a.2.val.1.val+a.2.val.2.val=D := by
      by_contra hn; exact hfa (hf a hn)
    let b : OrbitalTriple D := ⟨(a.1.val,a.2.val.1.val,a.2.val.2.val), hw,a.2.property⟩
    have hb : orbitalTripleFinite hQ hD b = a := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; rfl
    exact ⟨b,Finset.mem_univ _,by rwa [hb],hb⟩
  · simp

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma fourAnnihilator_high_local {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) (r : FourCopy D) :
    fourAnnihilator Q D D r.val.val =
      combination (localFourCoordinates hQ hD) (fourHighestRows Q D r) := by
  classical
  rw [fourAnnihilator_exterior hQ hD le_rfl (Nat.le_of_lt_succ r.val.isLt) r.property]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
  let f := fun a : FourCoordinates Q =>
    fourBodyCoefficient Q D D r.val.val a.1.val a.2.val.1.val a.2.val.2.val •
      (annihilation a.2.val.2 * annihilation a.2.val.1 * physicalPair Q a.1.val)
  change _ = ∑ b, f (orbitalTripleFinite hQ hD b)
  rw [sum_orbitalTriple hQ hD f]
  · exact (Fintype.sum_prod_type f).symm
  · intro a ha
    simp [f, fourBodyCoefficient, ha]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealSpinSquare
attribute [-simp] _root_.OAI.LaughlinGap.Occupation.extendTo_add_dim _root_.OAI.LaughlinGap.Occupation.extendTo_adjoint _root_.OAI.LaughlinGap.Occupation.extendTo_annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Spin Square. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Occupation

@[simp] lemma complexify_physicalTriple (Q : ℕ) (a : Fin (2*Q-2+1) × Fin (Q+1)) :
    complexify (physicalTriple Q a) = Occupation.annihilation a.2 * Occupation.localPair (Q+1) Q a.1.val := by
  simp [physicalTriple, productFamily]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourComparison
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma fourWeightCoefficient_tendsto {D r : ℕ} (hr : r ≤ D) (T p j k : ℕ) :
    Tendsto (fun Q => fourWeightCoefficient Q D T r p j k) atTop
      (𝓝 (fourWeightCoefficientStar D T r p j k)) := by
  by_cases h : D ≤ T
  · simp only [fourWeightCoefficient,fourWeightCoefficientStar,ite_eq_left h]
    exact fourBodyCoefficient_tendsto hr h p j k
  · simp only [fourWeightCoefficient,fourWeightCoefficientStar,ite_eq_right h]
    exact tendsto_const_nhds

lemma rowFourMatrix_symmetric (s : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ)
    (D : ℕ) (r : RowData) : (rowFourMatrix s D r).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext u v
  simp only [rowFourMatrix,Matrix.transpose_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : b.val.1.val+b.val.2.val+a.output.val = a.val.1.val+a.val.2.val+b.output.val := by
    have := a.balance; have := b.balance; omega
  rw [he]
  ring

lemma rowFourMatrix_tendsto (D : ℕ) (r : RowData) (u v : FourCopy D) :
    Tendsto (fun Q => rowFourMatrix (fourWeightCoefficient Q) D r u v) atTop
      (𝓝 (rowFourMatrix fourWeightCoefficientStar D r u v)) := by
  unfold rowFourMatrix
  apply Tendsto.neg
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  exact ((fourWeightCoefficient_tendsto (Nat.le_of_lt_succ u.val.isLt) _ _ _ _).const_mul _).mul
    (fourWeightCoefficient_tendsto (Nat.le_of_lt_succ v.val.isLt) _ _ _ _)

lemma fourCopyTarget_symmetric (D : ℕ) : (fourCopyTarget D).IsHermitian := by
  ext r s
  simp [fourCopyTarget,and_comm]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTransfer
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.complexify_physicalTriple _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Transfer. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma fourDimensionRatio_tendsto (D : ℕ) :
    Tendsto (fun Q => fourDimensionRatio Q D) atTop (𝓝 2) := by
  have ht : Tendsto (fun Q : ℕ => (4-(1+2*(D:ℝ))/Q)/(2-(1:ℝ)/Q))
      atTop (𝓝 (2:ℝ)) := by
    convert ((tendsto_const_nhds (x := (4:ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1+2*(D:ℝ)))).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))) (by norm_num : (2:ℝ)-0 ≠ 0) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Pi.div_def]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold fourDimensionRatio
  field_simp [hn]
  ring

variable {ι : Type*} [Fintype ι]

lemma fourComparison_symmetric (rows : ι → RowData) (ε : ℝ) (Q D : ℕ) :
    (fourComparison rows ε Q D).IsHermitian := by
  unfold fourComparison
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.sub
    · exact (fourCopyTarget_symmetric D).smul (by rfl)
    · apply Matrix.IsHermitian.ext
      intro u v
      simp only [Matrix.sum_apply,star_trivial]
      exact Finset.sum_congr rfl (fun a _ => (rowFourMatrix_symmetric _ _ _).apply u v)
  · exact Matrix.isHermitian_one.smul (by rfl)

lemma fourComparisonStar_symmetric (rows : ι → RowData) (ε : ℝ) (D : ℕ) :
    (fourComparisonStar rows ε D).IsHermitian := by
  unfold fourComparisonStar
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.sub
    · exact (fourCopyTarget_symmetric D).smul (by rfl)
    · apply Matrix.IsHermitian.ext
      intro u v
      simp only [Matrix.sum_apply,star_trivial]
      exact Finset.sum_congr rfl (fun a _ => (rowFourMatrix_symmetric _ _ _).apply u v)
  · exact Matrix.isHermitian_one.smul (by rfl)

lemma fourComparison_tendsto (rows : ι → RowData) (ε : ℝ) (D : ℕ)
    (u v : FourCopy D) : Tendsto (fun Q => fourComparison rows ε Q D u v) atTop
      (𝓝 (fourComparisonStar rows ε D u v)) := by
  simp only [fourComparison,fourComparisonStar,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  exact (((fourDimensionRatio_tendsto D).mul_const _).sub
    (tendsto_finsetSum Finset.univ (fun a _ => rowFourMatrix_tendsto D (rows a) u v))).add_const _

lemma fourHighestRows_tendsto (D : ℕ) (r : FourCopy D) (b : OrbitalTriple D) :
    Tendsto (fun Q => fourHighestRows Q D r b) atTop (𝓝 (fourHighestRowsStar D r b)) :=
  fourBodyCoefficient_tendsto (Nat.le_of_lt_succ r.val.isLt) le_rfl _ _ _

lemma complexify_four_highest {Q D : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (r : FourCopy D) :
    complexify (fourAnnihilator Q D D r.val.val) =
      Occupation.extendTo (show 25 ≤ Q+1 by omega)
        (∑ b : OrbitalTriple D, (fourHighestRows Q D r b : ℂ) •
          (Occupation.annihilation (localTripleK hD b) * Occupation.annihilation (localTripleJ hD b) *
            Occupation.localPair 25 Q (localTripleP hD b).val)) := by
  rw [fourAnnihilator_high_local (by omega) (by omega),complexify_combination]
  simp only [map_sum,map_smul,map_mul,Occupation.extendTo_annihilation]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Occupation.extendTo_localPair _ (by have := (localTripleP hD b).isLt; omega)]
  simp only [localFourCoordinates,orbitalTripleFinite,map_mul,complexify_annihilation,
    complexify_physicalPair,localTripleP,localTripleJ,localTripleK]
  rfl

lemma lift_symmetric {α β : Type*} [Fintype α] [Fintype β]
    (B : α → Matrix β β ℝ) {C : Matrix α α ℝ} (hC : C.IsHermitian) :
    (lift B C).IsHermitian := by
  classical
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [lift_transpose,(Matrix.conjTranspose_eq_transpose_of_trivial C).symm,hC.eq]

lemma posSemidef_of_complex_re {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : A.IsHermitian)
    (h : ∀ x : EuclideanSpace ℂ α, 0 ≤ (inner ℂ x (complexify A x)).re) : A.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hA,fun x => ?_⟩
  simpa [complexify,Matrix.toLpLin_apply,EuclideanSpace.inner_toLp_toLp,
    Matrix.mulVec,dotProduct,Complex.mul_re,Complex.add_re,mul_comm] using
      h (WithLp.toLp 2 (fun i => (x i : ℂ)))

lemma complexify_square_sum_inner {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (B : β → Matrix α α ℝ) (c : ℝ) (x : EuclideanSpace ℂ α) :
    (inner ℂ x (complexify (c • ∑ p, (B p).transpose * B p) x)).re =
      c * ∑ p, ‖complexify (B p) x‖^2 := by
  simp only [map_smul,map_sum,map_mul,complexify_transpose,LinearMap.smul_apply,
    LinearMap.sum_apply,Module.End.mul_apply,inner_smul_right_eq_smul,inner_sum,
    LinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

lemma complexify_four_local_lift {Q D : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (C : Matrix (FourCopy D) (FourCopy D) ℝ) :
    complexify (lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val) C) =
      Occupation.extendTo (show 25 ≤ Q+1 by omega)
        (matrixLift (fun r => ∑ b : OrbitalTriple D, (fourHighestRows Q D r b : ℂ) •
          (Occupation.annihilation (localTripleK hD b) * Occupation.annihilation (localTripleJ hD b) *
            Occupation.localPair 25 Q (localTripleP hD b).val)) (C.map (algebraMap ℝ ℂ))) := by
  rw [complexify_lift,Occupation.extendTo_matrixLift]
  simp only [complexify_four_highest hQ hD]

theorem four_local_transfer (rows : ι → RowData) (ε : ℝ) {D : ℕ} (hD : D ≤ 23)
    (hc : FourCertificate rows ε D hD) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ᶠ Q in atTop, ∀ _hQ : 24 ≤ Q,
        -(ρ Q) • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
          lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val) (fourComparison rows ε Q D) := by
  classical
  have hc₀ := (fourComparisonStar_symmetric rows ε D).map (algebraMap ℝ ℂ) (fun x => by simp)
  obtain ⟨ρ,hpos,hlim,hbound⟩ := Occupation.local_four_family_transfer_to
    (localTripleP hD) (localTripleJ hD) (localTripleK hD)
    (fun Q => fourHighestRows Q D) (fourHighestRowsStar D)
    (fun Q => (fourComparison rows ε Q D).map (algebraMap ℝ ℂ))
    ((fourComparisonStar rows ε D).map (algebraMap ℝ ℂ))
    (fourHighestRows_tendsto D)
    (fun r s => Complex.continuous_ofReal.continuousAt.tendsto.comp (fourComparison_tendsto rows ε D r s))
    hc₀ hc
  refine ⟨ρ,hpos,hlim,?_⟩
  filter_upwards [hbound] with Q bound
  intro hQ
  apply sub_nonneg.mp
  apply Matrix.PosSemidef.nonneg
  apply posSemidef_of_complex_re
  · exact (lift_symmetric _ (fourComparison_symmetric rows ε Q D)).sub
      ((Matrix.posSemidef_sum Finset.univ (fun p _ =>
        transpose_square_positive (physicalPair Q (p : Fin 24).val))).isHermitian.smul (by rfl))
  · intro x
    have hb := bound (Q+1) (by omega) x
    simp only [map_sub,LinearMap.sub_apply,inner_sub_right,Complex.sub_re]
    rw [complexify_four_local_lift hQ hD,complexify_square_sum_inner]
    simp only [complexify_physicalPair]
    apply sub_nonneg.mpr
    have hpair (p : Fin 24) := Occupation.extendTo_localPair (show 25 ≤ Q+1 by omega)
      (show p.val+1 < 25 by omega) (Q := Q)
    simpa only [hpair] using hb

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourBound
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Bound. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

theorem four_comparison_of_certificates_oai (rows : ι → RowData) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ∀ d : Fin 23, FourCertificate rows ε (d.val+1) (by omega)) :
    ∃ R : ℕ → ℝ, (∀ Q, 0 ≤ R Q) ∧ Tendsto R atTop (𝓝 0) ∧
      ∀ᶠ Q in atTop, ∀ hQ : 24 ≤ Q,
        ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
          (∑ r, rowFour (by omega) (rows r)) ≤
            fourTarget Q + (1222*ε+R Q) • physicalHamiltonian Q := by
  classical
  choose ρ hpos hlim hbound using (fun d : Fin 23 => four_local_transfer rows ε (by omega) (hc d))
  refine ⟨fun Q => 24*∑ d, ρ d Q,fun Q => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun d _ => hpos d Q)),?_,?_⟩
  · simpa using (tendsto_finsetSum Finset.univ (fun d _ => hlim d)).const_mul 24
  · filter_upwards [eventually_all.mpr hbound] with Q hQb
    intro hQ
    exact four_comparison_pointwise hQ rows ε hε (fun d => ρ d Q) (fun d => hQb d hQ)

end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LaughlinGap.RealOccupation.four_comparison_of_certificates_oai.{u_1} := @OAI.LaughlinGap.RealOccupation.four_comparison_of_certificates_oai.{u_1}
