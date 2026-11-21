-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_coefficient_when_positive_zero_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:11:52.31234+00:00
-- url     : https://prove2.me/submissions/f102e320-1099-4aad-a978-7970f3407957

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem scaleRoot_nonneg_root
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) : 0 ≤ Phi ψ q ∧ ψ (Phi ψ q) = q :=
  (hW q hq).1.2.1

private theorem scaleRoot_pos
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hzero : ψ 0 = 0) (q : ℝ) (hq : 0 < q) : 0 < Phi ψ q := by
  obtain ⟨hn, he⟩ := scaleRoot_nonneg_root ψ W hW q hq.le
  by_contra! h
  rw [le_antisymm h hn, hzero] at he
  exact hq.ne' he.symm

private theorem exponent_secants_mono
    (ψ : ℝ → ℝ) (hconv : ConvexOn ℝ (Ici 0) ψ) (hzero : ψ 0 = 0) :
    MonotoneOn (fun x : ℝ => ψ x / x) (Ioi 0) := by
  intro x hx y hy hxy
  simpa only [hzero, sub_zero] using hconv.secant_mono (a := (0 : ℝ)) (by simp)
    (mem_Ici.mpr (le_of_lt hx)) (mem_Ici.mpr (le_of_lt hy)) (ne_of_gt hx) (ne_of_gt hy) hxy

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hconv : ConvexOn ℝ (Ici 0) ψ) (hzero : ψ 0 = 0) (hφ0 : 0 < Phi ψ 0) :
    (∀ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds d)) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      Tendsto (fun q : ℝ => q / Phi ψ q)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) := by
  let N := nhdsWithin (0 : ℝ) (Ioi 0)
  haveI : N.NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hqev : ∀ᶠ q in N, 0 < q := self_mem_nhdsWithin
  have hsec := exponent_secants_mono ψ hconv hzero
  have hφq (q : ℝ) (hq : 0 < q) : 0 < Phi ψ q := scaleRoot_pos ψ W hW hzero q hq
  have hΨφ0 : ψ (Phi ψ 0) = 0 := (scaleRoot_nonneg_root ψ W hW 0 le_rfl).2
  have hφlt (q : ℝ) (hq : 0 < q) : Phi ψ 0 < Phi ψ q := by
    by_contra! hle
    have hm := hsec (hφq q hq) hφ0 hle
    change ψ (Phi ψ q) / Phi ψ q ≤ ψ (Phi ψ 0) / Phi ψ 0 at hm
    rw [(scaleRoot_nonneg_root ψ W hW q hq.le).2, hΨφ0, zero_div] at hm
    exact (div_pos hq (hφq q hq)).not_ge hm
  have htend : Tendsto (fun q => q / Phi ψ q) N (nhds 0) := by
    have hId : Tendsto (fun q : ℝ => q) N (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (hqev.mono fun q hq => div_nonneg hq.le (hφq q hq).le)
      (hqev.mono fun q hq => div_le_div_of_nonneg_left hq.le hφ0 (hφlt q hq).le) ?_
    simpa only [zero_div] using hId.div_const (Phi ψ 0)
  have hno (d : ℝ) (hd : HasPositiveFiniteRightPsiSlope ψ d) : False := by
    have hsmall : ∀ᶠ q in N, q < Phi ψ 0 :=
      (show ∀ᶠ q in nhds (0 : ℝ), q < Phi ψ 0 from Iio_mem_nhds hφ0).filter_mono nhdsWithin_le_nhds
    have hnonpos : ∀ᶠ q in N, (ψ q - ψ 0) / q ≤ 0 := by
      filter_upwards [hqev, hsmall] with q hq hqsmall
      simpa only [hzero, sub_zero, hΨφ0, zero_div] using hsec hq hφ0 hqsmall.le
    exact hd.1.not_ge (le_of_tendsto hd.2 hnonpos)
  exact ⟨fun d hd => (hno d hd).elim, fun _ => htend⟩
