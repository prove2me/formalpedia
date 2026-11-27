-- Prove2me | solution 1 for Kyprianou.Ch04.physicalKernelDifferenceIdentityAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:15.764746+00:00
-- url     : https://prove2.me/submissions/b5e39502-556b-4d1f-8cdb-92926a95b39d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_predictablePhysicalKernelSectionV1
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Compensated physical integration is linear for two bounded predictable kernels on a common finite mark band, simultaneously at every time. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal inferInstance)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ) (hB : MeasurableSet B)
    (hfin : ν B < ⊤)
    (g h : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (hh : Measurable[F.predictable.prod inferInstance] h)
    (K : ℝ) (hC : ∀ p, ‖g p‖ ≤ K ∧ ‖h p‖ ≤ K)
    (hs : ∀ p, p.2 ∉ B → g p = 0 ∧ h p = 0) :
    let J := fun (k : (NNReal × Ω) × ℝ → ℝ) (t : NNReal) (w : Ω) =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    ∀ᵐ w ∂P, ∀ t, J (fun p => g p-h p) t w = J g t w-J h t w := by
  intro J
  let D (t : NNReal) := Icc (0 : ℝ) (t : ℝ) ×ˢ B
  have hLam (t : NNReal) := Kyprianou.Ch04.closedTimeBandIntensityFinite ν t B hfin
  have hN (t : NNReal) : ∀ᵐ w ∂P, N.N w (D t) < ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod hB) (hLam t)] with w hw
    obtain ⟨m,hm⟩ := hw
    rw [hm]
    exact ENNReal.natCast_lt_top m
  filter_upwards [ae_all_iff.mpr (fun m : ℕ => hN m)] with w hw
  intro t
  obtain ⟨m,hm⟩ := exists_nat_ge t
  have hNt : N.N w (D t) < ⊤ := (measure_mono (fun z hz =>
    show z ∈ D m from ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast hm)⟩,hz.2⟩)).trans_lt (hw m)
  have hInt (R : Measure (ℝ × ℝ)) (hR : R (D t) < ⊤) :
      IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,w),z.2))
        (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) R ∧
      IntegrableOn (fun z : ℝ × ℝ => h ((z.1.toNNReal,w),z.2))
        (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) R :=
    ⟨(Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 R t B hB hR _
      (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F g hg w) K
      (fun z => (hC _).1) (fun z hz => (hs _ hz).1)).1,
     (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 R t B hB hR _
      (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F h hh w) K
      (fun z => (hC _).2) (fun z hz => (hs _ hz).2)).1⟩
  have h1 := hInt (N.N w) hNt
  have h2 := hInt (referenceIntensity ν) (hLam t).lt_top
  dsimp only [J]
  rw [integral_sub h1.1 h1.2,integral_sub h2.1 h2.2]
  ring
