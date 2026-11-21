-- Prove2me | solution 1 for MasulloGRH.hilbert_quotient_biorthogonal_section
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:51:04.72764+00:00
-- url     : https://prove2.me/submissions/e4df1ead-75e1-4350-a6b3-7de274622da3

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter Topology
open scoped InnerProductSpace
noncomputable section

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (K F : Submodule 𝕜 E) [IsClosed (K : Set E)]
    (hd : K ≤ (K ⊓ F).topologicalClosure) (x : ℕ → E ⧸ K) (f : ℕ → StrongDual 𝕜 (E ⧸ K))
    (hbi : ∀ n m, f n (x m) = if n=m then 1 else 0)
    (hx : ∀ n, ∃ y ∈ F, K.mkQ y = x n) (ε : ℝ) (hε : 0 < ε) :
    let J : (E ⧸ K) →L[𝕜] E := Kᗮ.subtypeL.comp K.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
    ∃ T : (E ⧸ K) →L[𝕜] E, (∀ y, K.mkQ (T y) = y) ∧ (∀ n, T (x n) ∈ F) ∧ ‖T-J‖ < ε := by
  classical
  dsimp only
  let J : (E ⧸ K) →L[𝕜] E := Kᗮ.subtypeL.comp K.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
  have hJ (y : E ⧸ K) : K.mkQ (J y) = y := by
    let z := K.quotientEquivOrthogonal y
    change Submodule.Quotient.mk z.val = y
    rw [←K.quotientEquivOrthogonal_symm_eq_mk z.val z.property]
    exact K.quotientEquivOrthogonal.symm_apply_apply y
  let w := fun n : ℕ => (ε/4)*(1/2:ℝ)^n
  have hw (n : ℕ) : 0 < w n := by dsimp [w]; positivity
  have hs : HasSum w ((ε/4)*2) := hasSum_geometric_two.mul_left (ε/4)
  have hl (n : ℕ) : ∃ z : K, J (x n) + z.val ∈ F ∧ ‖z‖ < w n/(‖f n‖+1) := by
    obtain ⟨y,hy,hyq⟩ := hx n
    have hker : J (x n)-y ∈ K := by
      apply (Submodule.Quotient.mk_eq_zero K).mp
      change K.mkQ (J (x n)-y) = 0
      rw [map_sub,hJ,hyq,sub_self]
    have hc : J (x n)-y ∈ closure ((K ⊓ F : Submodule 𝕜 E) : Set E) := hd hker
    obtain ⟨t,ht,htd⟩ := Metric.mem_closure_iff.mp hc (w n/(‖f n‖+1)) (div_pos (hw _) (by positivity))
    have hdif : y + t - J (x n) = t - (J (x n)-y) := by abel
    refine ⟨⟨y+t-J (x n),hdif ▸ K.sub_mem ht.1 hker⟩,?_,?_⟩
    · change J (x n) + (y + t - J (x n)) ∈ F
      simpa [add_sub_cancel] using (show (y+t) ∈ F from F.add_mem hy ht.2)
    · change ‖y+t-J (x n)‖ < _
      rwa [hdif,←dist_eq_norm,dist_comm]
  choose z hF hz using hl
  let A := fun n => (f n).smulRight (z n)
  have hb (n : ℕ) : ‖A n‖ ≤ w n := by
    rw [show ‖A n‖ = ‖f n‖*‖z n‖ from (f n).norm_smulRight_apply _]
    have hh := (lt_div_iff₀ (by positivity : 0<‖f n‖+1)).mp (hz n)
    nlinarith [norm_nonneg (z n)]
  have hnorm : Summable (fun n => ‖A n‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs.summable
  let B := ∑' n, A n
  have hsmall : ‖B‖ < ε := calc
    ‖B‖ ≤ ∑' n, ‖A n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, w n := hnorm.tsum_le_tsum hb hs.summable
    _ = _ := hs.tsum_eq
    _ < ε := by linarith
  have hBx (m : ℕ) : B (x m) = z m := by
    have hh := (ContinuousLinearMap.apply 𝕜 K (x m)).hasSum hnorm.of_norm.hasSum
    change HasSum (fun n => A n (x m)) (B (x m)) at hh
    rw [←hh.tsum_eq,tsum_eq_single m]
    · simp [A,hbi]
    · intro n hn; simp [A,hbi,hn]
  refine ⟨J + K.subtypeL.comp B,?_,?_,?_⟩
  · intro y
    change K.mkQ (J y + (B y).val) = y
    rw [map_add,hJ,show K.mkQ (B y).val = 0 from (Submodule.Quotient.mk_eq_zero K).mpr (B y).property,add_zero]
  · intro n
    change J (x n) + (B (x n)).val ∈ F
    rw [hBx]; exact hF n
  · change ‖J + K.subtypeL.comp B - J‖ < ε
    rw [add_sub_cancel_left]
    calc ‖K.subtypeL.comp B‖ ≤ ‖K.subtypeL‖ * ‖B‖ := K.subtypeL.opNorm_comp_le _
         _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right K.norm_subtypeL_le (norm_nonneg _)
         _ < ε := by simpa using hsmall
