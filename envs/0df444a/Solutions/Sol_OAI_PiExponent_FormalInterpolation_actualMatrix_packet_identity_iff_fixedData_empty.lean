-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.actualMatrix_packet_identity_iff_fixedData_empty
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:17:49.381412+00:00
-- url     : https://prove2.me/submissions/4f7be834-4bb6-4564-ad38-7329ce2a30fc

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

namespace MatrixPacketObstruction

private theorem simplex_mem {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (a : Fin n → ℕ) (H : ℝ) (ha : ∑ i, w i * (a i : ℝ) < H) :
    a ∈ strictWeightedSimplex w H := by
  classical
  simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter,
    Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨⟨?_, ha.le⟩, ha⟩
  intro i
  have hi : w i * (a i : ℝ) ≤ ∑ j, w j * (a j : ℝ) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _))
      (Finset.mem_univ i)
  have hd : (a i : ℝ) ≤ H / w i := (le_div_iff₀ (hw i)).2 (by nlinarith)
  exact Nat.lt_succ_of_le ((Nat.le_floor_iff (le_trans (Nat.cast_nonneg _) hd)).2 hd)

private theorem lift_coeff (m s : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin (m+1)) s)
      (FormalInterpolation.liftSeries m (PowerSeries.log ℂ)) =
        PowerSeries.coeff s (PowerSeries.log ℂ) := by
  have hc := MvPowerSeries.coeff_coeff_finSuccEquiv
    (p := FormalInterpolation.liftSeries m (PowerSeries.log ℂ))
    (k := s) (x := (0 : Fin m →₀ ℕ))
  have he : Finsupp.cons s (0 : Fin m →₀ ℕ) = Finsupp.single 0 s :=
    Finsupp.cons_eq_single_zero_iff.mpr ⟨rfl, rfl⟩
  rw [he] at hc
  rw [← hc]
  change MvPowerSeries.coeff 0 (PowerSeries.coeff s
    ((MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm
        (PowerSeries.map MvPowerSeries.C (PowerSeries.log ℂ))))) = _
  rw [AlgEquiv.apply_symm_apply, PowerSeries.coeff_map]
  simp only [MvPowerSeries.coeff_C, ite_true]

private theorem matrix_X_zero {m K : ℕ} (w0 v0 theta H : ℝ)
    (w : Fin m → ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m)
    (rho : InterpolationMatrix.Row K v0 theta w H)
    (hzero : rho.1.val = 0)
    (hexp : rho.2.val = fun k => if k = 0 then T i + 1 else 0) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
      (fun c => (MvPolynomial.X i.succ : MvPolynomial (Fin (m+1)) ℂ).coeff
        (InterpolationMatrix.exponentVector c.1)) rho = 0 := by
  classical
  rw [Matrix.mulVecLin_apply, Matrix.mulVec]
  apply Finset.sum_eq_zero
  intro c _
  dsimp only
  by_cases he : InterpolationMatrix.exponentVector c.val = Finsupp.single i.succ 1
  · have hhead : c.val 0 = 0 := by
      have hh := DFunLike.congr_fun he 0
      simpa [InterpolationMatrix.exponentVector] using hh
    have htail : (fun k : Fin m => c.val k.succ) = fun k => if k = i then 1 else 0 := by
      funext k
      have hh := DFunLike.congr_fun he k.succ
      simpa [InterpolationMatrix.exponentVector, Finsupp.single_apply, eq_comm] using hh
    have hentry : InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T rho c = 0 := by
      have hz : (Finsupp.equivFunOnFinite.symm (fun _ : Fin m => (0 : ℕ))) = 0 := by
        ext k
        rfl
      unfold InterpolationMatrix.truncatedLogMatrix InterpolationMatrix.matrix
        InterpolationMatrix.entry
      rw [htail, hhead, hzero, hexp]
      simp [InterpolationMatrix.monomialImage, InterpolationMatrix.exponentVector,
        InterpolationMatrix.truncatedLog, hz, PowerSeries.coeff_trunc]
    exact mul_eq_zero_of_left hentry _
  · have hz : (MvPolynomial.X i.succ : MvPolynomial (Fin (m+1)) ℂ).coeff
        (InterpolationMatrix.exponentVector c.val) = 0 := by
      simp [MvPolynomial.coeff_X, Ne.symm he]
    exact mul_eq_zero_of_right _ hz

theorem cutoff {nu : ℝ} (d : FixedData nu) :
    ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ) := by
  intro i
  have hw : 0 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    unfold MatrixArithmetic.logWeights
    positivity
  have hf : 1 / (d.base.theta : ℝ) ≤ d.F0 := by
    have ht := d.base.theta_pos
    have : 0 < 1 / (d.base.theta : ℝ) := by positivity
    have hh : 2 / (d.base.theta : ℝ) = 2 * (1 / (d.base.theta : ℝ)) := by ring
    linarith [d.F0_large]
  have hc := Nat.le_ceil (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i /
    (d.v0 : ℝ))
  have hb := (div_le_iff₀ d.v0_pos).mp hc
  dsimp [MatrixArithmetic.truncationOrders]
  calc
    _ = MatrixArithmetic.logWeights (finiteDenominators d) i * (1 / (d.base.theta : ℝ)) := by ring
    _ ≤ MatrixArithmetic.logWeights (finiteDenominators d) i * d.F0 := mul_le_mul_of_nonneg_left hf hw
    _ ≤ _ := by nlinarith [hb]

theorem counterexample {nu : ℝ} (d : FixedData nu) :
    ∃ (H : ℝ) (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) (rho : Row d H),
      (actualMatrix d H).mulVecLin
        (fun c : Column d H => P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho ≠
          FormalInterpolation.packetMap d H P rho := by
  classical
  let i : Fin d.m := ⟨0, d.m_pos⟩
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  let T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0
  let s := T i + 1
  let H : ℝ := max (w i) ((s : ℝ) * (d.v0 : ℝ)) + 1
  have hw : ∀ j, 0 < w j := by
    intro j
    have hq : (1 : ℝ) < (finiteDenominators d j : ℝ) := by
      exact_mod_cast (d.approximations j.val).1
    exact Nat.cast_pos.mpr (Nat.ceil_pos.mpr (Real.log_pos hq))
  let P : FormalInterpolation.WeightedPolynomial d.w0 w H :=
    ⟨MvPolynomial.X i.succ, by
      intro a ha
      rw [MvPolynomial.support_X] at ha
      simp only [Finset.mem_singleton] at ha
      subst a
      simp only [Finsupp.single_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      change w i ≤ H
      exact le_trans (le_max_left _ _) (by dsimp [H]; linarith)⟩
  let a : Fin (d.m+1) → ℕ := fun k => if k = 0 then s else 0
  have ha : a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H := by
    apply simplex_mem
    · intro k
      cases k using Fin.cases with
      | zero => exact d.v0_pos
      | succ j => exact div_pos (hw j) d.base.theta_pos
    · simp only [a, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      change (d.v0 : ℝ) * (s : ℝ) < H
      have := le_max_right (w i) ((s : ℝ) * (d.v0 : ℝ))
      dsimp [H]
      nlinarith
  let rho : Row d H := (⟨0, d.K_pos⟩, ⟨a, ha⟩)
  refine ⟨H, P, rho, ?_⟩
  have hl : (actualMatrix d H).mulVecLin
      (fun c : Column d H => P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho = 0 :=
    matrix_X_zero d.w0 d.v0 d.base.theta H w _ T i rho rfl rfl
  have he : InterpolationMatrix.exponentVector rho.2.val = Finsupp.single 0 s := by
    ext k
    simp [InterpolationMatrix.exponentVector, rho, a, Finsupp.single_apply, eq_comm]
  have hs : s ≠ 0 := Nat.succ_ne_zero _
  have hidx : Finsupp.single (0 : Fin (d.m+1)) s ≠ Finsupp.single i.succ 1 := by
    intro heq
    have := DFunLike.congr_fun heq 0
    simpa [hs] using this
  have hr : FormalInterpolation.packetMap d H P rho = PowerSeries.coeff s (PowerSeries.log ℂ) := by
    simp only [FormalInterpolation.packetMap, he]
    simp [P, FormalInterpolation.formalJet, rho, MvPowerSeries.coeff_X, hidx,
      lift_coeff]
  rw [hl, hr]
  symm
  simp [PowerSeries.coeff_log, hs]

end MatrixPacketObstruction

theorem solution :
    (∀ {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)), ∀ ρ : Row d (H : ℝ),
      (actualMatrix d (H : ℝ)).mulVecLin
        (fun c : Column d (H : ℝ) => P.val.coeff (InterpolationMatrix.exponentVector c.1)) ρ =
          FormalInterpolation.packetMap d (H : ℝ) P ρ) ↔
    (∀ nu : ℝ, IsEmpty (FixedData nu)) := by
  constructor
  · intro h nu
    refine ⟨fun d => ?_⟩
    obtain ⟨H, P, rho, hne⟩ := MatrixPacketObstruction.counterexample d
    exact hne (h d H P (MatrixPacketObstruction.cutoff d) rho)
  · intro h nu d
    exact ((h nu).false d).elim
