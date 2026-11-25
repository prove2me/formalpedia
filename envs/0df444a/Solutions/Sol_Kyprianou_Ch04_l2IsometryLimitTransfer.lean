-- Prove2me | solution 1 for Kyprianou.Ch04.l2IsometryLimitTransfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:50:20.235381+00:00
-- url     : https://prove2.me/submissions/0b9261c9-af00-40df-894b-649ed7fe08f8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_l2CauchyLimitIdentification
import Theorems.Thm_Kyprianou_Ch04_lpNormSqIntegral
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
universe u v

/-- Isometric approximations preserve second moments at a limit in measure. -/
theorem solution
    {A : Type u} {Ω : Type v} [MeasurableSpace A] [MeasurableSpace Ω]
    (μ : Measure A) (P : Measure Ω)
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hY : TendstoInMeasure P X atTop Y)
    (hDist : ∀ n m, dist ((hX n).toLp (X n)) ((hX m).toLp (X m)) =
      dist ((hf n).toLp (f n)) ((hf m).toLp (f m)))
    (hNorm : ∀ n, ‖(hX n).toLp (X n)‖ = ‖(hf n).toLp (f n)‖) :
    MemLp Y 2 P ∧ (∫ ω, (Y ω) ^ 2 ∂P) = ∫ a, (g a) ^ 2 ∂μ := by
  have hc : CauchySeq (fun n => (hX n).toLp (X n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hfg.cauchySeq ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rw [hDist]
    exact hN n hn m hm
  obtain ⟨h, ht⟩ := Kyprianou.Ch04.l2CauchyLimitIdentification P X Y hX hc hY
  have hn : ‖h.toLp Y‖ = ‖hg.toLp g‖ := by
    apply tendsto_nhds_unique ht.norm
    exact hfg.norm.congr' (Eventually.of_forall fun n => (hNorm n).symm)
  refine ⟨h, ?_⟩
  rw [← Kyprianou.Ch04.lpNormSqIntegral P Y h,
    ← Kyprianou.Ch04.lpNormSqIntegral μ g hg, hn]
