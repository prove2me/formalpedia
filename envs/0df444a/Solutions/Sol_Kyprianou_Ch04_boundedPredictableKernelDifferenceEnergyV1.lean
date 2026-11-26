-- Prove2me | solution 1 for Kyprianou.Ch04.boundedPredictableKernelDifferenceEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:34:30.989343+00:00
-- url     : https://prove2.me/submissions/644a5b77-1e0e-4deb-8d13-9aa18619cc48

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalIsometryV1
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_predictablePhysicalKernelSectionV1
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityClosedWindowProductV1
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two bounded predictable kernels on a common finite band have exact
terminal difference energy in the positive-time intensity product. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun ω => N.N ω D))
    (T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g h : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (hh : Measurable[F.predictable.prod inferInstance] h)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C ∧ ‖h p‖ ≤ C)
    (hs : ∀ p, p.2 ∉ B → g p = 0 ∧ h p = 0) :
    let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    let q := fun (ω : Ω) (z : ℝ × ℝ) => ((z.1.toNNReal,ω),z.2)
    let J := fun (k : (NNReal × Ω) × ℝ → ℝ) ω =>
      (∫ z in U, k (q ω z) ∂(N.N ω)) - ∫ z in U, k (q ω z) ∂referenceIntensity ν
    (∫ ω, (J g ω - J h ω)^2 ∂P) = ∫ ω, ∫ s in Ioc (0 : ℝ) (T : ℝ),
      ∫ x, (g ((s.toNNReal,ω),x) - h ((s.toNNReal,ω),x))^2 ∂ν ∂volume ∂P := by
  let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
  let q := fun (ω : Ω) (z : ℝ × ℝ) => ((z.1.toNNReal,ω),z.2)
  let J := fun (k : (NNReal × Ω) × ℝ → ℝ) ω =>
    (∫ z in U, k (q ω z) ∂(N.N ω)) - ∫ z in U, k (q ω z) ∂referenceIntensity ν
  let k := fun p => g p - h p
  have hk : Measurable[F.predictable.prod inferInstance] k := hg.sub hh
  have hkb (p) : ‖k p‖ ≤ 2*C :=
    (norm_sub_le _ _).trans (by linarith [(hC p).1,(hC p).2])
  have hks (p) (hp : p.2 ∉ B) : k p = 0 := by simp [k,(hs p hp).1,(hs p hp).2]
  have hi := Kyprianou.Ch04.boundedSupportedPredictablePhysicalIsometryV1 P ν F N
    hFuture hPast T B hB hfin k hk (2*C) hkb hks
  have hIntensity := Kyprianou.Ch04.closedTimeBandIntensityFinite ν T B hfin
  have hN : ∀ᵐ ω ∂P, N.N ω (Icc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod hB) hIntensity] with ω hω
    obtain ⟨n,hn⟩ := hω
    rw [hn]
    exact ENNReal.natCast_lt_top n
  have hInt (R : Measure (ℝ × ℝ)) (hR : R (Icc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤)
      (ω : Ω) : IntegrableOn (fun z => g (q ω z)) U R ∧
        IntegrableOn (fun z => h (q ω z)) U R := by
    exact ⟨(Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 R T B hB hR _
      (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F g hg ω) C
      (fun z => (hC (q ω z)).1) (fun z hz => (hs (q ω z) hz).1)).1,
      (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 R T B hB hR _
      (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F h hh ω) C
      (fun z => (hC (q ω z)).2) (fun z hz => (hs (q ω z) hz).2)).1⟩
  have hJ : ∀ᵐ ω ∂P, J g ω - J h ω = J k ω := by
    filter_upwards [hN] with ω hω
    have h1 := hInt (N.N ω) hω ω
    have h2 := hInt (referenceIntensity ν) hIntensity.lt_top ω
    dsimp only [J,k]
    rw [integral_sub h1.1 h1.2,integral_sub h2.1 h2.2]
    ring
  have hE (ω : Ω) : (∫ z in U, (k (q ω z))^2 ∂referenceIntensity ν) =
      ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ x, (k ((s.toNNReal,ω),x))^2 ∂ν ∂volume := by
    have hs := (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1
      (referenceIntensity ν) T B hB hIntensity.lt_top _
      (Kyprianou.Ch04.predictablePhysicalKernelSectionV1 F k hk ω)
      (2*C) (fun z => hkb (q ω z)) (fun z hz => hks (q ω z) hz)).2
    have hprod := Kyprianou.Ch04.referenceIntensityClosedWindowProductV1 ν T
      (univ : Set ℝ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at hprod
    rw [show U = Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ) from rfl, hprod]
    rw [IntegrableOn,hprod] at hs
    rw [integral_prod _ hs,integral_Icc_eq_integral_Ioc]
  change (∫ ω, (J g ω - J h ω)^2 ∂P) = _
  calc
    _ = ∫ ω, (J k ω)^2 ∂P := integral_congr_ae (hJ.mono fun ω hω => congrArg (·^2) hω)
    _ = ∫ ω, ∫ z in U, (k (q ω z))^2 ∂referenceIntensity ν ∂P := hi.2
    _ = _ := integral_congr_ae (Eventually.of_forall hE)
