-- Prove2me | solution 1 for LSAPR.identity_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:50:36.98355+00:00
-- url     : https://prove2.me/submissions/a53cdb99-24ea-41c2-9288-2825aeb3c2d2

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

open LSAPR in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (π : Measure Z)
    (A : Z → Mat d) (b : Z → Vec d) (θstar : Vec d)
    (hsol : matApply (Abar π A) θstar = bbar π b)
    (α : ℝ) (hα : 0 < α) (θ0 : Vec d) (Zpath : ℕ → Z) (n0 n : ℕ) (hn : n0 < n) :
    matApply (Abar π A) (prAvg α A b θ0 Zpath n0 n - θstar) =
        (α * ((n : ℝ) - n0))⁻¹ • (lsaIter α A b θ0 Zpath n0 - lsaIter α A b θ0 Zpath n)
          - ((n : ℝ) - n0)⁻¹ • ∑ t ∈ Finset.Ico n0 n,
              eNoise π A b (lsaIter α A b θ0 Zpath t) (Zpath (t + 1)) ∧
      ∀ (θ : Vec d) (z : Z), eNoise π A b θ z =
        epsNoise π A b θstar z + matApply (Atilde π A z) (θ - θstar) := by
  have hsub : ∀ (M M' : Mat d) (v : Vec d), matApply (M - M') v = matApply M v - matApply M' v := by
    intro M M' v
    unfold matApply
    rw [map_sub, LinearMap.sub_apply]
  have hlin : ∀ (M : Mat d) (v w : Vec d), matApply M (v - w) = matApply M v - matApply M w := by
    intro M v w
    unfold matApply
    rw [map_sub]
  refine ⟨?_, fun θ z => ?_⟩
  · unfold prAvg
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = lsaIter α A b θ0 Zpath := ⟨_, rfl⟩
    rw [← hθ]
    obtain ⟨L, hL⟩ : ∃ L, L = Matrix.toEuclideanLin (Abar π A) := ⟨_, rfl⟩
    have hLapp : ∀ v, matApply (Abar π A) v = L v := by intro v; subst hL; rfl
    have key : ∀ (v : Vec d) (z : Z), matApply (A z) v - b z
        = L (v - θstar) + eNoise π A b v z := by
      intro v z
      unfold eNoise Atilde btilde
      rw [hsub, map_sub, ← hLapp, ← hLapp, hsol]
      abel
    have hstep : ∀ k, θ k - θ (k + 1) = α • (L (θ k - θstar) + eNoise π A b (θ k) (Zpath (k + 1))) := by
      intro k
      have hrec : θ (k + 1) = θ k - α • (matApply (A (Zpath (k + 1))) (θ k) - b (Zpath (k + 1))) := by
        subst hθ; rfl
      rw [hrec, key, sub_sub_cancel]
    have htel : ∀ m : ℕ, ∑ k ∈ Finset.Ico n0 (n0 + m), (θ k - θ (k + 1)) = θ n0 - θ (n0 + m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show n0 + (m + 1) = n0 + m + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
        abel
    obtain ⟨m, rfl⟩ : ∃ m, n = n0 + m := ⟨n - n0, by omega⟩
    have hN : ((n0 + m : ℕ) : ℝ) - n0 = (m : ℝ) := by push_cast; ring
    have hm : (m : ℝ) ≠ 0 := by
      have : 0 < m := by omega
      exact_mod_cast this.ne'
    have hdiff : θ n0 - θ (n0 + m) = α • (∑ k ∈ Finset.Ico n0 (n0 + m), L (θ k - θstar)
        + ∑ k ∈ Finset.Ico n0 (n0 + m), eNoise π A b (θ k) (Zpath (k + 1))) := by
      rw [← htel, Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.smul_sum,
        Finset.sum_add_distrib]
    have hsumL : ∑ k ∈ Finset.Ico n0 (n0 + m), L (θ k - θstar)
        = L (∑ k ∈ Finset.Ico n0 (n0 + m), θ k) - (m : ℝ) • L θstar := by
      rw [Finset.sum_congr rfl (fun k _ => map_sub L (θ k) θstar), Finset.sum_sub_distrib,
        map_sum, Finset.sum_const, Nat.card_Ico, show n0 + m - n0 = m by omega, Nat.cast_smul_eq_nsmul]
    rw [hdiff, hsumL, hN, hLapp, map_sub, map_smul, smul_smul,
      show (α * (m : ℝ))⁻¹ * α = (m : ℝ)⁻¹ by field_simp, smul_add, smul_sub, smul_smul,
      inv_mul_cancel₀ hm, one_smul]
    abel
  · unfold eNoise epsNoise
    rw [hlin]
    abel
