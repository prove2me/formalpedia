-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventual_bounded_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T17:13:18.732607+00:00
-- url     : https://prove2.me/submissions/5fcf25db-9f89-4b73-90d2-4e3923162745
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_padded_raw_packet_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_zero_padded_raw_packet_mem_power

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

private theorem positive_rational_power_scale {ι : Type} [Fintype ι]
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) :
    ∃ R : ℚ, 0 < R ∧ ∃ e : ι → ℕ,
      (∀ i, 0 < e i) ∧ ∀ i, R = (e i : ℚ) * v i := by
  classical
  let a : ι → ℕ := fun i => (v i).num.natAbs
  have ha : ∀ i, 0 < a i := by
    intro i
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr (hv i)))
  have hnum : ∀ i, (a i : ℚ) = ((v i).num : ℚ) := by
    intro i
    have hi : (a i : ℤ) = (v i).num := by
      dsimp [a]
      exact Int.natAbs_of_nonneg (Rat.num_pos.mpr (hv i)).le
    exact_mod_cast hi
  refine ⟨(∏ i, a i : ℕ), ?_,
    fun i => (v i).den * ∏ j ∈ Finset.univ.erase i, a j, ?_, ?_⟩
  · exact_mod_cast Finset.prod_pos (fun i _ => ha i)
  · intro i
    exact Nat.mul_pos (v i).den_pos (Finset.prod_pos (fun j _ => ha j))
  · intro i
    have hprod := Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)
    have hden : ((v i).den : ℚ) ≠ 0 := by exact_mod_cast (v i).den_ne_zero
    rw [← hprod]
    push_cast
    have hmul : v i * ((v i).den : ℚ) = ((v i).num : ℚ) :=
      (eq_div_iff hden).mp (v i).num_div_den.symm
    rw [hnum, ← hmul]
    ring

private theorem fixed_row_positive {nu : ℝ} (d : FixedData nu) :
    ∀ i, 0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact d.v0_pos
  · change 0 < MatrixArithmetic.logWeights (finiteDenominators d) j / (d.base.theta : ℝ)
    have hw : MatrixArithmetic.logWeights (finiteDenominators d) j = d.x (j.val + 1) := by
      simp only [MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
    rw [hw]
    exact div_pos (lt_of_lt_of_le zero_lt_one (d.x_one_le _)) d.base.theta_pos

private theorem fixed_exact_scales {nu : ℝ} (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ,
      (∀ i, 0 < e i) ∧
      (∀ i, (R : ℝ) = (e i : ℝ) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
      (∀ i : Fin d.m, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤ (T i : ℝ) * (d.v0 : ℝ)) := by
  let v : Fin (d.m + 1) → ℚ := Fin.cases d.v0
    (fun i => (⌈Real.log (d.q i.val)⌉₊ : ℚ) / d.base.theta)
  have hvcast : ∀ i, (v i : ℝ) = InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [v, InterpolationMatrix.rowWeights, MatrixArithmetic.logWeights, finiteDenominators]
  have hv : ∀ i, 0 < v i := by
    intro i
    have hi := fixed_row_positive d i
    rw [← hvcast i] at hi
    exact_mod_cast hi
  obtain ⟨R, hR, e, he, hscale⟩ := positive_rational_power_scale v hv
  have ht : ∀ i : Fin d.m, ∃ t : ℕ,
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤ (t : ℝ) * (d.v0 : ℝ) := by
    intro i
    obtain ⟨t, ht⟩ := exists_nat_gt
      (InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ / (d.v0 : ℝ))
    exact ⟨t, ((div_lt_iff₀ d.v0_pos).mp ht).le⟩
  choose T hT using ht
  refine ⟨R, hR, T, e, he, ?_, hT⟩
  intro i
  rw [← hvcast i]
  exact_mod_cast hscale i

private theorem fixed_centers_injective {nu : ℝ} (d : FixedData nu) :
    Function.Injective (fun j : Fin d.K => fun i : Fin d.m => (j.val : ℂ) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i) := by
  let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
  have hp : (d.p i.val : ℂ) ≠ 0 := by exact_mod_cast (d.approximations i.val).2.1
  have hq : (d.q i.val : ℂ) ≠ 0 := by
    have h := (d.approximations i.val).1
    exact_mod_cast (show d.q i.val ≠ 0 by omega)
  have hr : MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  intro j k h
  have hjk := mul_right_cancel₀ hr (congrFun h i)
  apply Fin.ext
  exact_mod_cast hjk

theorem solution {nu : ℝ} (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ, ∃ N : ℕ,
      (∀ i, (R : ℝ) ≤ (e i : ℝ) *
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
      (∀ i : Fin d.m,
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
            (T i : ℝ) * (d.v0 : ℝ)) ∧
      ∀ n : ℕ, N ≤ n → ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
          P - Q.val ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            T e) ^ n := by
  obtain ⟨R, hR, T, e, he, hscale, hT⟩ := fixed_exact_scales d
  obtain ⟨N, hN⟩ := eventual_padded_raw_packet_surjective d R hR d.m
  refine ⟨R, hR, T, e, N, fun i => (hscale i).le, hT, ?_⟩
  intro n hn P
  obtain ⟨Q, hQ⟩ := hN n hn
    (rawPacketMap d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))
      (((n + d.m : ℕ) : ℝ) * (R : ℝ))
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) P)
  refine ⟨Q, ?_⟩
  apply zero_padded_raw_packet_mem_power d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) (R : ℝ)
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T e
    (by exact_mod_cast hR) (fixed_row_positive d) he hscale hT (fixed_centers_injective d) n
  funext rho
  have hcoeff := congrFun hQ rho
  change MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
    (formalJet (fun i => (rho.1.val : ℂ) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (P - Q.val)) = 0
  rw [map_sub, map_sub]
  exact sub_eq_zero.mpr hcoeff.symm
