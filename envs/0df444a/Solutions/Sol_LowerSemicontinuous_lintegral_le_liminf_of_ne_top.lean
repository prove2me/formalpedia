-- Prove2me | solution 1 for LowerSemicontinuous.lintegral_le_liminf_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:08:05.851638+00:00
-- url     : https://prove2.me/submissions/6186d9c6-7663-4598-a96b-710d9f962889

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc

set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]
namespace LowerSemicontinuous
theorem _root_.solution
    {μ : Measure W} {μs : ℕ → Measure W} {f : W → ℝ≥0∞}
    (hf : LowerSemicontinuous f) (hf_ne : ∀ x, f x ≠ ∞)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := by
  have g_nn : ∀ x, (0 : ℝ) ≤ (f x).toReal := fun x => ENNReal.toReal_nonneg
  have g_mble : Measurable fun x => (f x).toReal := hf.measurable.ennreal_toReal
  -- superlevel sets of `x ↦ (f x).toReal` are open
  have levels_open : ∀ t : ℝ, IsOpen {a : W | t < (f a).toReal} := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · have huniv : {a : W | t < (f a).toReal} = univ :=
        eq_univ_of_forall fun a => lt_of_lt_of_le ht (g_nn a)
      rw [huniv]
      exact isOpen_univ
    · have hpre : {a : W | t < (f a).toReal} = f ⁻¹' Ioi (ENNReal.ofReal t) := by
        ext a
        simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
        exact (ENNReal.ofReal_lt_iff_lt_toReal ht (hf_ne a)).symm
      rw [hpre]
      exact hf.isOpen_preimage _
  -- layer-cake formula for each measure
  have key : ∀ ν : Measure W,
      ∫⁻ x, f x ∂ν = ∫⁻ t in Ioi (0 : ℝ), ν {a : W | t < (f a).toReal} := fun ν =>
    (lintegral_congr fun x => (ENNReal.ofReal_toReal (hf_ne x)).symm).trans
      (lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall g_nn) g_mble.aemeasurable)
  calc ∫⁻ x, f x ∂μ
      = ∫⁻ t in Ioi (0 : ℝ), μ {a : W | t < (f a).toReal} := key μ
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), atTop.liminf fun i => μs i {a : W | t < (f a).toReal} :=
        lintegral_mono fun t => h_opens _ (levels_open t)
    _ ≤ atTop.liminf fun i => ∫⁻ t in Ioi (0 : ℝ), μs i {a : W | t < (f a).toReal} :=
        lintegral_liminf_le fun i => Antitone.measurable fun s t hst =>
          measure_mono fun ω hω => lt_of_le_of_lt hst hω
    _ = atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) :=
        liminf_congr (Eventually.of_forall fun i => (key (μs i)).symm)
end LowerSemicontinuous
