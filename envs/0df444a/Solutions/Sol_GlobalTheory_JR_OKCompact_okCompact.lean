-- Prove2me | solution 1 for GlobalTheory.JR.OKCompact.okCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:08.378367+00:00
-- url     : https://prove2.me/submissions/42467d9a-aac7-4b93-b2ae-f0e9f0826288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK
import Theorems.Thm_GlobalTheory_JR_OKCompact_coeff_charpoly_lmul_smul
import Theorems.Thm_GlobalTheory_JR_OKCompact_continuous_coeff_lmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact
namespace GlobalTheory.JR.OKCompact
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by
  intro F E _ _ _ _ hU A
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank F A.K = n := ⟨_, rfl⟩
  let e : A.K ≃ₗ[F] (Fin n → F) := (Module.finBasisOfFinrankEq F A.K hn).equivFun
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let P : ℕ → A.K → F := fun k z => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff k
  have hPc : ∀ k, Continuous (P k) := fun k => continuous_coeff_lmul k
  have hcl : IsClosed A.OK := by
    have : A.OK = ⋂ k, {z | ‖P k z‖ ≤ 1} := by ext z; simp [Et.OK, P]
    rw [this]
    exact isClosed_iInter fun k => isClosed_le (continuous_norm.comp (hPc k)) continuous_const
  have hzero : ∀ z : A.K, (∀ k < n, P k z = 0) → z = 0 := by
    intro z hz
    have hp : LinearMap.charpoly (Algebra.lmul F A.K z) = Polynomial.X ^ n := by
      ext k
      rw [Polynomial.coeff_X_pow]
      rcases lt_trichotomy k n with hk | hk | hk
      · rw [if_neg hk.ne]; exact hz k hk
      · rw [if_pos hk]
        have := (LinearMap.charpoly_monic (Algebra.lmul F A.K z)).coeff_natDegree
        rwa [LinearMap.charpoly_natDegree, hn, ← hk] at this
      · rw [if_neg hk.ne']
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [LinearMap.charpoly_natDegree, hn]; exact hk
    have hCH := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
    rw [hp, map_pow, Polynomial.aeval_X, ← map_pow] at hCH
    have h1 := LinearMap.congr_fun hCH 1
    have h2 : z ^ n = 0 := by simpa using h1
    exact IsReduced.eq_zero z ⟨n, h2⟩
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm F
  let T : Set (Fin n → F) := {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ ‖a‖}
  have hT : IsCompact T := (isCompact_closedBall (0 : Fin n → F) ‖a‖).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun v hv => mem_closedBall_zero_iff.2 hv.2)
  let h : (Fin n → F) → ℝ := fun v => ∑ k ∈ Finset.range n, ‖P k (e.symm v)‖
  have hc : Continuous h := continuous_finset_sum _ fun k _ => continuous_norm.comp ((hPc k).comp hes)
  have hpos : ∀ v ∈ T, 0 < h v := by
    intro v hv
    by_contra hle
    push_neg at hle
    have hsum : h v = 0 := le_antisymm hle (Finset.sum_nonneg fun k _ => norm_nonneg _)
    have h0 : ∀ k < n, P k (e.symm v) = 0 := by
      intro k hk
      exact norm_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => norm_nonneg (P k (e.symm v))).1 hsum k
        (Finset.mem_range.2 hk))
    have hv0 : v = 0 := by simpa using congrArg e (hzero _ h0)
    have := hv.1
    rw [hv0, norm_zero] at this
    linarith
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ v ∈ T, m ≤ h v := by
    rcases T.eq_empty_or_nonempty with hTe | hTn
    · exact ⟨1, one_pos, fun v hv => by rw [hTe] at hv; exact hv.elim⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hT.exists_isMinOn hTn hc.continuousOn
      exact ⟨h v₀, hpos v₀ hv₀, fun v hv => hmin hv⟩
  have hsub : A.OK ⊆ e.symm '' Metric.closedBall 0 (‖a‖ * max 1 (n / m)) := by
    intro z hz
    refine ⟨e z, ?_, e.symm_apply_apply z⟩
    rw [mem_closedBall_zero_iff]
    have hR : ‖a‖ ≤ ‖a‖ * max 1 (n / m) := le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)
    by_cases hv : e z = 0
    · rw [hv, norm_zero]; linarith
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell ha (by linarith : (0 : ℝ) < ‖a‖) hv
    have hwT : d • e z ∈ T := ⟨by rwa [div_self (by linarith : ‖a‖ ≠ 0)] at hd2, hd1.le⟩
    have hvw : e z = d⁻¹ • (d • e z) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have hnv : ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := by rw [← norm_smul, ← hvw]
    have hsc : ∀ k, P k (e.symm (e z)) = P k (e.symm (d • e z)) * d⁻¹ ^ (n - k) := by
      intro k
      conv_lhs => rw [hvw, map_smul]
      have := coeff_charpoly_lmul_smul (F := F) (e.symm (d • e z)) (inv_ne_zero hd0) k
      rw [hn] at this
      exact this
    have hhv : h (e z) ≤ n := by
      calc h (e z) ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
              show ‖P k (e.symm (e z))‖ ≤ 1
              rw [e.symm_apply_apply]; exact hz k
        _ = n := by simp
    by_cases hc1 : ‖d⁻¹‖ ≤ 1
    · calc ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := hnv
        _ ≤ 1 * ‖a‖ := mul_le_mul hc1 hwT.2 (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact hR
    · push_neg at hc1
      have hlow : ‖d⁻¹‖ * m ≤ h (e z) := by
        calc ‖d⁻¹‖ * m ≤ ‖d⁻¹‖ * h (d • e z) := mul_le_mul_of_nonneg_left (hm _ hwT) (norm_nonneg _)
          _ = ∑ k ∈ Finset.range n, ‖d⁻¹‖ * ‖P k (e.symm (d • e z))‖ := Finset.mul_sum _ _ _
          _ ≤ ∑ k ∈ Finset.range n, ‖P k (e.symm (e z))‖ := Finset.sum_le_sum fun k hk => by
              rw [hsc k, norm_mul, norm_pow, mul_comm]
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              have hk' : 1 ≤ n - k := by have := Finset.mem_range.1 hk; omega
              calc ‖d⁻¹‖ = ‖d⁻¹‖ ^ 1 := (pow_one _).symm
                _ ≤ ‖d⁻¹‖ ^ (n - k) := pow_le_pow_right₀ hc1.le hk'
      have hcm : ‖d⁻¹‖ ≤ n / m := by rw [le_div_iff₀ hm0]; linarith
      calc ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := hnv
        _ ≤ (n / m) * ‖a‖ := mul_le_mul hcm hwT.2 (norm_nonneg _) (by positivity)
        _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  exact ((isCompact_closedBall 0 _).image hes).of_isClosed_subset hcl hsub
end GlobalTheory.JR.OKCompact
