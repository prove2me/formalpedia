-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_tail_multiplicative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:36:11.045113+00:00
-- url     : https://prove2.me/submissions/3f77babf-813f-47ef-9f56-937c3ebf2945
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_bounds
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_semigroup
import Theorems.Thm_Kyprianou_Ch08_StageB_exp_of_semigroup_bounded
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_bounded_on_Icc
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
noncomputable def S3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (q a h : ℝ) : ℝ := ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω}, Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) : ∀ a h : ℝ, 0 < a → 0 < h → (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω}, Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P) = Real.exp (-a * (-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  intro a h ha hh
  have hB : ∀ h, 0 < h → 0 < S3 P D ψ q 1 h ∧ S3 P D ψ q 1 h ≤ 1 := Kyprianou.Ch08.StageB.actual_height_tail_bounds P D ψ W hψ hW q hq
  have hSg : ∀ a1 a2 h, 0 < a1 → 0 < a2 → 0 < h → S3 P D ψ q (a1 + a2) h = S3 P D ψ q a1 h * S3 P D ψ q a2 h := Kyprianou.Ch08.StageB.actual_height_semigroup P D ψ W hψ hW q hq
  have hD0 : ∀ t : WithTop ℝ≥0, 0 ≤ discountedAt q t := by intro t; induction t using WithTop.recTopCoe with | top => simp [discountedAt] | coe s => simp [discountedAt, Real.exp_nonneg]
  have hnn : ∀ b, 0 ≤ S3 P D ψ q b h := fun b => integral_nonneg_of_ae (Eventually.of_forall fun ω => mul_nonneg (le_of_lt (Real.exp_pos _)) (hD0 _))
  have hpow : ∀ n : ℕ, S3 P D ψ q ((n + 1 : ℕ) : ℝ) h = (S3 P D ψ q 1 h) ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k IH =>
      have kp : (0:ℝ) < (((k+1:ℕ)):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
      have hc : ((((k+1+1:ℕ))):ℝ) = ((((k+1:ℕ)):ℝ) + 1) := by push_cast; ring
      rw [hc, hSg _ _ h kp zero_lt_one hh, IH]
      exact (pow_succ _ _).symm
  have hpos : ∀ b, 0 < b → 0 < S3 P D ψ q b h := by intro b hb; obtain ⟨n, hn⟩ := exists_nat_gt b; have hR : (0:ℝ) < (n:ℝ) := lt_trans hb hn; have hN : 0 < n := Nat.cast_pos.mp hR; obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n-1, by omega⟩; have hSn : S3 P D ψ q (((k+1:ℕ)):ℝ) h = (S3 P D ψ q 1 h)^(k+1) := hpow k; have h1 : 0 < S3 P D ψ q 1 h := (hB h hh).1; have hSP : 0 < S3 P D ψ q (((k+1:ℕ)):ℝ) h := hSn.symm ▸ pow_pos h1 (k+1); have hs : (0:ℝ) < ((((k+1:ℕ))):ℝ) - b := sub_pos.mpr hn; have hsp := hSg b (((((k+1:ℕ))):ℝ)-b) h hb hs hh; have hadd : b + (((((k+1:ℕ))):ℝ) - b) = ((((k+1:ℕ))):ℝ) := add_sub_cancel b ((((k+1:ℕ))):ℝ); rw [hadd] at hsp; have hprod : 0 < S3 P D ψ q b h * S3 P D ψ q (((((k+1:ℕ))):ℝ)-b) h := hsp ▸ hSP; have hne : S3 P D ψ q b h ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hprod)).1; exact lt_of_le_of_ne' (hnn b) hne
  have hbdd : ∃ B, ∀ x, 1 ≤ x → x ≤ 2 → S3 P D ψ q x h ≤ B := Kyprianou.Ch08.StageB.actual_height_bounded_on_Icc P D ψ W hψ hW q hq h hh
  have hs : ∀ x y, 0 < x → 0 < y → (fun a => S3 P D ψ q a h) (x+y) = (fun a => S3 P D ψ q a h) x * (fun a => S3 P D ψ q a h) y := fun x y hx hy => hSg x y h hx hy hh
  have hp2 : ∀ x, 0 < x → 0 < (fun a => S3 P D ψ q a h) x := fun x hx => hpos x hx
  have hb2 : ∃ B, ∀ x, 1 ≤ x → x ≤ 2 → (fun a => S3 P D ψ q a h) x ≤ B := hbdd
  exact Kyprianou.Ch08.StageB.exp_of_semigroup_bounded (fun a => S3 P D ψ q a h) hs hp2 hb2 a ha
