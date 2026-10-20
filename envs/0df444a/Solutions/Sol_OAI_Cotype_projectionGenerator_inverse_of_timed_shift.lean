-- Prove2me | solution 1 for OAI.Cotype.projectionGenerator_inverse_of_timed_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:09:13.066075+00:00
-- url     : https://prove2.me/submissions/aae5714f-12eb-4711-9308-5be30ffe7661

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent

open OAI OAI.Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
theorem h50c_deg_cons {m : ℕ} (b : Bool) (η : Cube m) :
    projectionDegree (Fin.cons b η : Cube (m+1)) = (if b then 1 else 0) + projectionDegree η := by
  classical
  simp only [projectionDegree, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem h50c_pat_cons {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (P : Fin (m+1) → Y →L[ℝ] Y) (b : Bool) (η : Cube m) :
    projectionPattern P (Fin.cons b η : Cube (m+1)) =
      (if b then 1 - P 0 else P 0) * projectionPattern (fun i => P i.succ) η := by
  simp only [projectionPattern, projectionProduct, Fin.cons_zero, Fin.cons_succ]

theorem h50c_spec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (z : ℂ) : ∀ (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
    complexProjectionProduct (fun i => complexDualLift (P i) + z • (1 - complexDualLift (P i))) =
      ∑ ε : Cube m, (z^(projectionDegree ε)) • complexDualLift (projectionPattern P ε) := by
  intro m
  induction m with
  | zero =>
    intro P
    simp [complexProjectionProduct, projectionDegree, projectionPattern, projectionProduct]
  | succ m ih =>
    intro P
    rw [complexProjectionProduct, ih (fun i => P i.succ)]
    rw [← (projectionChoiceCons Bool m).sum_comp]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, projectionChoiceCons, Equiv.coe_fn_mk,
      h50c_deg_cons, h50c_pat_cons]
    simp only [if_true, if_false, Bool.false_eq_true, zero_add, complexDualLift_mul, complexDualLift_sub,
      complexDualLift_one, add_mul, Finset.mul_sum, mul_smul_comm, smul_mul_assoc, pow_add, pow_one,
      mul_comm z, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    simp only [smul_add, Finset.sum_add_distrib]; exact add_comm _ _

theorem h50c_pgi {N : ℕ} {b q : ℝ}
    (hb : 0 ≤ b) (hq : q < 1)
    {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]
    (H : R) (hH : ‖H‖ ≤ b) (hHN : ‖H^N‖ ≤ q) :
    ∃ U : Rˣ, (U : R) = 1-H ∧ ‖(↑U⁻¹ : R)‖ ≤ powerGapInverseBound N b q := by
  have hHN1 : ‖H^N‖ < 1 := lt_of_le_of_lt hHN hq
  let V : Rˣ := Units.oneSub (H^N) hHN1
  let S : R := ∑ k ∈ Finset.range N, H^k
  have hSl : S * (1 - H) = 1 - H^N := by
    simp only [S]; rw [Finset.sum_mul]
    simp only [mul_sub, mul_one, ← pow_succ]
    rw [Finset.sum_range_sub' (fun k => H^k)]; simp
  have hSr : (1 - H) * S = 1 - H^N := by
    simp only [S]; rw [Finset.mul_sum]
    simp only [sub_mul, one_mul, ← pow_succ']
    rw [Finset.sum_range_sub' (fun k => H^k)]; simp
  have hV : (V : R) = 1 - H^N := rfl
  have hHc : Commute (H^N) H := (Commute.refl H).pow_left N
  have hcomm : Commute (V : R) (1 - H) := by
    rw [hV]; exact (Commute.one_left (1-H)).sub_left ((Commute.one_right (H^N)).sub_right hHc)
  have hci : Commute ((V⁻¹ : Rˣ) : R) (1 - H) := hcomm.units_inv_left
  refine ⟨⟨1 - H, ((V⁻¹ : Rˣ) : R) * S, ?_, ?_⟩, rfl, ?_⟩
  · rw [← mul_assoc, ← hci.eq, mul_assoc, hSr, ← hV, Units.inv_mul]
  · rw [mul_assoc, hSl, ← hV, Units.inv_mul]
  · show ‖((V⁻¹ : Rˣ) : R) * S‖ ≤ _
    have h1 : ‖((V⁻¹ : Rˣ) : R)‖ ≤ (1 - q)⁻¹ := by
      have hb := tsum_geometric_le_of_norm_lt_one (H^N) hHN1
      have : ((V⁻¹ : Rˣ) : R) = ∑' n, (H^N)^n := rfl
      rw [this]
      have : (1 - ‖H^N‖)⁻¹ ≤ (1 - q)⁻¹ := by
        apply inv_anti₀ (by linarith) (by linarith)
      simp only [norm_one, sub_self, zero_add] at hb
      linarith
    have h2 : ‖S‖ ≤ ∑ k ∈ Finset.range N, b^k := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      exact (norm_pow_le H k).trans (pow_le_pow_left₀ (norm_nonneg _) hH k)
    have hq0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg (H^N)])
    rw [powerGapInverseBound, div_eq_mul_inv, mul_comm (∑ k ∈ Finset.range N, b^k)]
    exact (norm_mul_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) hq0)

theorem h50c_csi {N : ℕ} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    (T : A) (hT : ‖T‖ ≤ 1) (hTN : ‖(1-T)^N‖ ≤ C)
    (β : ℂ) (hβ : ρ ≤ ‖β‖) :
    ∃ U : Aˣ, (U : A) = (β-1) • (1 : A) + T ∧
      ‖(↑U⁻¹ : A)‖ ≤ powerGapInverseBound N (2/ρ) (C/ρ^N) / ‖β‖ := by
  have hβ0 : (β : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; linarith
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  set H : A := β⁻¹ • (1 - T) with hHdef
  have h1T : ‖1 - T‖ ≤ 2 := by
    calc ‖1 - T‖ ≤ ‖(1:A)‖ + ‖T‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hH : ‖H‖ ≤ 2/ρ := by
    rw [hHdef, norm_smul, norm_inv]
    calc ‖β‖⁻¹ * ‖1 - T‖ ≤ ρ⁻¹ * 2 := mul_le_mul (inv_anti₀ hρ hβ) h1T (norm_nonneg _) (inv_nonneg.2 hρ.le)
      _ = 2/ρ := by ring
  have hHN : ‖H^N‖ ≤ C/ρ^N := by
    rw [hHdef, smul_pow, norm_smul, norm_pow, norm_inv, inv_pow]
    have hρN : 0 < ρ^N := pow_pos hρ N
    calc (‖β‖^N)⁻¹ * ‖(1 - T)^N‖ ≤ (ρ^N)⁻¹ * C :=
          mul_le_mul (inv_anti₀ hρN (pow_le_pow_left₀ hρ.le hβ N)) hTN (norm_nonneg _) (inv_nonneg.2 hρN.le)
      _ = C/ρ^N := by ring
  have hq : C/ρ^N < 1 := by rw [div_lt_one (pow_pos hρ N)]; exact hgap
  obtain ⟨V, hV, hVb⟩ := h50c_pgi (by positivity) hq H hH hHN
  have hrel : β • (1 - H) = (β-1) • (1 : A) + T := by
    rw [hHdef, smul_sub, smul_smul, mul_inv_cancel₀ hβ0, one_smul, sub_smul, one_smul]; abel
  refine ⟨⟨β • (V : A), β⁻¹ • ((V⁻¹ : Aˣ) : A), ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hβ0, Units.mul_inv, one_smul]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hβ0, Units.inv_mul, one_smul]
  · show β • (V : A) = _
    rw [hV, hrel]
  · show ‖β⁻¹ • ((V⁻¹ : Aˣ) : A)‖ ≤ _
    rw [norm_smul, norm_inv, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hVb (inv_nonneg.2 hβpos.le)


theorem h50c_expshift {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (s : ℝ) :
    NormedSpace.exp (s • (z • 1 - projectionGenerator P)) =
      Complex.exp (z * (s : ℂ)) • complexProjectionTime P (s : ℂ) := by
  let Φ := complexProjectionSpectralHom P hp hc
  have hΦc : Continuous Φ := (Φ.toLinearMap).continuous_of_finiteDimensional
  have hG : s • (z • 1 - projectionGenerator P) =
      Φ ((s : ℂ) • fun ε : Cube m => z - (projectionDegree ε : ℂ)) := by
    have e : ∀ X : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y), (s:ℂ) • X = s • X :=
      fun X => ContinuousLinearMap.ext fun x => Complex.coe_smul s (X x)
    rw [map_smul, e]
    congr 1
    show _ = complexSpectralEval P _
    have : (fun ε : Cube m => z - (projectionDegree ε : ℂ)) = (fun _ => z) - fun ε => (projectionDegree ε : ℂ) := rfl
    rw [this]
    have h2 : complexSpectralEval P ((fun _ => z) - fun ε : Cube m => (projectionDegree ε : ℂ)) =
        Φ (fun _ => z) - Φ (fun ε : Cube m => (projectionDegree ε : ℂ)) := map_sub Φ _ _
    rw [h2]
    show _ = complexSpectralEval P (fun _ => z) - complexSpectralEval P _
    rw [complexSpectralEval_const]; rfl
  rw [hG, ← NormedSpace.map_exp Φ hΦc]
  have hf : NormedSpace.exp ((s : ℂ) • fun ε : Cube m => z - (projectionDegree ε : ℂ)) =
      Complex.exp (z * (s : ℂ)) • fun ε : Cube m => Complex.exp (-(s : ℂ)) ^ projectionDegree ε := by
    rw [Pi.exp_def]
    funext ε
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Complex.exp_eq_exp_ℂ, ← Complex.exp_nat_mul, ← Complex.exp_add]
    ring_nf
  rw [hf, map_smul]
  congr 1
  show complexSpectralEval P _ = complexProjectionPolynomial P (Complex.exp (-(s:ℂ)))
  rw [complexProjectionPolynomial, h50c_spec]; rfl


theorem h50c_poly_real {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (r : ℝ) : ∀ (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
    complexProjectionPolynomial P (r : ℂ) = complexDualLift (projectionSemigroup P r) := by
  have e : ∀ X : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y), (r:ℂ) • X = r • X :=
    fun X => ContinuousLinearMap.ext fun x => Complex.coe_smul r (X x)
  intro m
  induction m with
  | zero => intro P; show (1 : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = complexDualLift 1; simp
  | succ m ih =>
    intro P
    have := ih (fun i => P i.succ)
    simp only [complexProjectionPolynomial] at this ⊢
    rw [complexProjectionProduct, this]
    show _ = complexDualLift ((P 0 + r • (1 - P 0)) * projectionSemigroup (fun i => P i.succ) r)
    rw [complexDualLift_mul, complexDualLift_add, complexDualLift_smul, complexDualLift_sub,
      complexDualLift_one, e]

theorem h50c_factor_norm {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (Q : Y →L[ℝ] Y)
    (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ‖Q + r • (1 - Q)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  have : (Q + r • (1 - Q)) y = r • y + (1 - r) • Q y := by
    simp [sub_smul, smul_sub]; abel
  rw [this, one_mul]
  calc ‖r • y + (1 - r) • Q y‖ ≤ ‖r • y‖ + ‖(1 - r) • Q y‖ := norm_add_le _ _
    _ = r * ‖y‖ + (1 - r) * ‖Q y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hr0, Real.norm_of_nonneg (by linarith)]
    _ ≤ r * ‖y‖ + (1 - r) * ‖y‖ := by
        have := mul_le_mul_of_nonneg_left (hQ y) (show (0:ℝ) ≤ 1 - r by linarith); linarith
    _ = ‖y‖ := by ring

theorem h50c_semigroup_norm {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ (m : ℕ) (P : Fin m → Y →L[ℝ] Y), (∀ i y, ‖P i y‖ ≤ ‖y‖) → ‖projectionSemigroup P r‖ ≤ 1 := by
  intro m
  induction m with
  | zero => intro P _; exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => by
      show ‖(1 : Y →L[ℝ] Y) y‖ ≤ 1 * ‖y‖; simp)
  | succ m ih =>
    intro P hP
    show ‖(P 0 + r • (1 - P 0)) * projectionSemigroup (fun i => P i.succ) r‖ ≤ 1
    calc _ ≤ ‖P 0 + r • (1 - P 0)‖ * ‖projectionSemigroup (fun i => P i.succ) r‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (h50c_factor_norm _ (hP 0) hr0 hr1) (ih _ (fun i => hP i.succ))
            (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem h50c_time_eq {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (s : ℝ) :
    complexProjectionTime P (s : ℂ) = complexDualLift (projectionSemigroup P (Real.exp (-s))) := by
  rw [complexProjectionTime, ← h50c_poly_real]
  congr 1
  rw [Complex.ofReal_exp, Complex.ofReal_neg]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem solution
    [Nontrivial (ComplexDualSpace Y)]
    {N : ℕ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖)
    (hpower : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
      ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖)
    (z : ℂ) {t D : ℝ} (ht : 0 ≤ t)
    (hshift : ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖)
    (hD : ∀ s ∈ Set.Icc 0 t, Real.exp (z.re * (s-t)) ≤ D) :
    ∃ W : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)ˣ,
      (W : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = z • 1 - projectionGenerator P ∧
      ‖(↑W⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)‖ ≤
        D*t * (powerGapInverseBound N (2/ρ) (C/ρ^N) /
          ‖1-Complex.exp (-(z*(t : ℂ)))‖) := by
  set L : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y := z • 1 - projectionGenerator P with hL
  set T := complexProjectionTime P (t : ℂ) with hTdef
  have hTn : ∀ s : ℝ, 0 ≤ s → ‖complexProjectionTime P (s : ℂ)‖ ≤ 1 := by
    intro s hs
    rw [h50c_time_eq]
    refine (complexDualLift_norm_le _).trans (h50c_semigroup_norm (Real.exp_pos _).le ?_ m P hP)
    rw [Real.exp_le_one_iff]; linarith
  have hTN : ‖(1 - T)^N‖ ≤ C := by
    rw [hTdef, h50c_time_eq, ← complexDualLift_one, ← complexDualLift_sub, ← complexDualLift_pow]
    refine (complexDualLift_norm_le _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_
    exact hpower _ (Real.exp_pos _).le (by rw [Real.exp_le_one_iff]; linarith) y
  set β : ℂ := 1 - Complex.exp (-(z*(t : ℂ))) with hβ
  obtain ⟨U, hU, hUb⟩ := h50c_csi hC hρ hgap T (hTn t ht) hTN β hshift
  -- the integral
  set I : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y := ∫ s in (0:ℝ)..t, NormedSpace.exp (s • L) with hI
  have hcont : Continuous fun s : ℝ => NormedSpace.exp (s • L) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_const L s).continuousAt
  have h0 : NormedSpace.exp ((0:ℝ) • L) = 1 := by
    have : ((0:ℝ) • L) = 0 := ContinuousLinearMap.ext fun x => by
      rw [ContinuousLinearMap.smul_apply, zero_smul, ContinuousLinearMap.zero_apply]
    rw [this]; exact NormedSpace.exp_zero
  have hsm1 : ∀ (c : ℂ) (A B : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y), (c • A) * B = c • (A * B) :=
    fun c A B => ContinuousLinearMap.ext fun x => rfl
  have hsm2 : ∀ (c : ℂ) (A B : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y), A * (c • B) = c • (A * B) :=
    fun c A B => ContinuousLinearMap.ext fun x => A.map_smul c (B x)
  have hIL : I * L = NormedSpace.exp (t • L) - 1 := by
    have h1 : ∫ s in (0:ℝ)..t, NormedSpace.exp (s • L) * L = NormedSpace.exp (t • L) - NormedSpace.exp ((0:ℝ) • L) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_exp_smul_const L s)
        ((hcont.mul continuous_const).intervalIntegrable _ _)
    rw [h0] at h1
    rw [← h1, hI]
    exact ((ContinuousLinearMap.compL ℂ (ComplexDualSpace Y) (ComplexDualSpace Y) (ComplexDualSpace Y)).flip L).intervalIntegral_comp_comm
      (hcont.intervalIntegrable _ _) |>.symm
  have hLI : L * I = NormedSpace.exp (t • L) - 1 := by
    have h1 : ∫ s in (0:ℝ)..t, L * NormedSpace.exp (s • L) = NormedSpace.exp (t • L) - NormedSpace.exp ((0:ℝ) • L) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_exp_smul_const' L s)
        ((continuous_const.mul hcont).intervalIntegrable _ _)
    rw [h0] at h1
    rw [← h1, hI]
    exact ((ContinuousLinearMap.compL ℂ (ComplexDualSpace Y) (ComplexDualSpace Y) (ComplexDualSpace Y)) L).intervalIntegral_comp_comm
      (hcont.intervalIntegrable _ _) |>.symm
  set Q := Complex.exp (-(z*(t:ℂ))) • I with hQ
  have hexpt : NormedSpace.exp (t • L) = Complex.exp (z * (t : ℂ)) • T := h50c_expshift P hp hc z t
  have hkey : ∀ X : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y, X = NormedSpace.exp (t • L) - 1 → Complex.exp (-(z*(t:ℂ))) • X = (U : _) := by
    intro X hX
    have hmul : Complex.exp (-(z*(t:ℂ))) * Complex.exp (z*(t:ℂ)) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    rw [hX, hexpt, hU, smul_sub, smul_smul, hmul, one_smul, hβ, sub_sub_cancel_left, neg_smul]
    abel
  have hQL : Q * L = U := by rw [hQ, hsm1, hIL]; exact hkey _ rfl
  have hLQ : L * Q = U := by rw [hQ, hsm2, hLI]; exact hkey _ rfl
  have hinv_eq : (↑U⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) * Q = Q * ↑U⁻¹ := by
    calc (↑U⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) * Q
        = ↑U⁻¹ * Q * (L * (Q * ↑U⁻¹)) := by rw [← mul_assoc L, hLQ, Units.mul_inv, mul_one]
      _ = (↑U⁻¹ * (Q * L)) * (Q * ↑U⁻¹) := by noncomm_ring
      _ = Q * ↑U⁻¹ := by rw [hQL, Units.inv_mul, one_mul]
  refine ⟨⟨L, Q * ↑U⁻¹, ?_, ?_⟩, rfl, ?_⟩
  · rw [← mul_assoc, hLQ, Units.mul_inv]
  · rw [← hinv_eq, mul_assoc, hQL, Units.inv_mul]
  · show ‖Q * ↑U⁻¹‖ ≤ _
    have hQb : ‖Q‖ ≤ D * t := by
      rw [hQ, hI, ← intervalIntegral.integral_smul]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := D)
        (f := fun s : ℝ => Complex.exp (-(z*(t:ℂ))) • NormedSpace.exp (s • L)) ?_
      · rwa [sub_zero, abs_of_nonneg ht] at this
      intro s hs
      rw [Set.uIoc_of_le ht] at hs
      rw [h50c_expshift P hp hc z s, smul_smul, norm_smul, ← Complex.exp_add]
      rw [Complex.norm_exp]
      have hre : (-(z * (t:ℂ)) + z * (s:ℂ)).re = z.re * (s - t) := by
        simp [Complex.mul_re]; ring
      rw [hre]
      have hDs := hD s ⟨hs.1.le, hs.2⟩
      calc Real.exp (z.re * (s - t)) * ‖complexProjectionTime P (s:ℂ)‖ ≤ D * 1 :=
            mul_le_mul hDs (hTn s hs.1.le) (norm_nonneg _) (le_trans (Real.exp_pos _).le hDs)
        _ = D := mul_one D
    have hD0 : 0 ≤ D := le_trans (Real.exp_pos _).le (hD t ⟨ht, le_rfl⟩)
    calc ‖Q * ↑U⁻¹‖ ≤ ‖Q‖ * ‖(↑U⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)‖ := norm_mul_le _ _
      _ ≤ (D * t) * (powerGapInverseBound N (2/ρ) (C/ρ^N) / ‖β‖) :=
          mul_le_mul hQb hUb (norm_nonneg _) (by positivity)

