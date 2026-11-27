-- Prove2me | solution 1 for Kyprianou.Ch04.nestedGridStepKernelEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:13:46.080476+00:00
-- url     : https://prove2.me/submissions/b64c6c5c-3038-447a-a261-b4275a2fe59a

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_boundedPredictableMarkMaskV1
import Theorems.Thm_Kyprianou_Ch04_physicalKernelReferenceSquareProductV1
import Theorems.Thm_Kyprianou_Ch04_gridMarkedKernelBudgetV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Predictability, boundedness, support and terminal energy for the nested cutoff step kernels. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (F : Filtration NNReal inferInstance) (a b K : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (W V : NNReal × Ω → ℝ)
    (hW : Measurable[F.predictable] W) (hV : Measurable[F.predictable] V)
    (hWb : ∀ p, |W p| ≤ K) (hVb : ∀ p, |V p| ≤ K)
    (S : Ω → ℝ) (hS : Integrable S P) (hSnn : ∀ᵐ w ∂P, 0 ≤ S w)
    (hDiff : ∀ᵐ w ∂P, ∀ t : NNReal, |W (t,w)-V (t,w)| ≤ K * Real.sqrt (S w))
    (hEnergy : (∫ w, S w ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    let A : Set ℝ := {z | a < |z| ∧ |z| < 1}
    let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
    let g := fun p : (NNReal × Ω) × ℝ => A.indicator (fun z => z * W p.1) p.2
    let h := fun p : (NNReal × Ω) × ℝ => B.indicator (fun z => z * V p.1) p.2
    let k := fun p => g p-h p
    Measurable[F.predictable.prod inferInstance] g ∧
    Measurable[F.predictable.prod inferInstance] h ∧
    (∀ p, ‖g p‖ ≤ K ∧ ‖h p‖ ≤ K) ∧
    (∀ p, p.2 ∉ A → g p = 0 ∧ h p = 0) ∧
    (∫ w, ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      (k ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity ν ∂P) ≤
      (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  intro A B g h k
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hfin : ν A < ⊤ := (measure_mono (show A ⊆ {z | a ≤ |z|}
    from fun z hz => hz.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top ha)
  have hg := Kyprianou.Ch04.boundedPredictableMarkMaskV1 F A hA
    (fun z hz => hz.2.le) W hW K hK hWb
  have hh := Kyprianou.Ch04.boundedPredictableMarkMaskV1 F B hB
    (fun z hz => hz.2.le) V hV K hK hVb
  have hs (p : (NNReal × Ω) × ℝ) (hp : p.2 ∉ A) : g p = 0 ∧ h p = 0 :=
    ⟨hg.2.2 p hp,hh.2.2 p (fun hbp => hp ⟨hab.trans hbp.1,hbp.2⟩)⟩
  refine ⟨hg.1,hh.1,fun p => ⟨hg.2.1 p,hh.2.1 p⟩,hs,?_⟩
  have hk : Measurable[F.predictable.prod inferInstance] k := hg.1.sub hh.1
  have hkb (p) : ‖k p‖ ≤ 2*K :=
    (norm_sub_le _ _).trans (by linarith [hg.2.1 p,hh.2.1 p])
  have hks (p) (hp : p.2 ∉ A) : k p = 0 := by
    change g p - h p = 0
    rw [(hs p hp).1,(hs p hp).2,sub_zero]
  have he (w : Ω) := Kyprianou.Ch04.physicalKernelReferenceSquareProductV1 ν F A hA hfin
    k hk (2*K) hkb hks T w
  simp_rw [he]
  have heq (w : Ω) (s z : ℝ) : k ((s.toNNReal,w),z) =
      z * ((if a < |z| ∧ |z| < 1 then W (s.toNNReal,w) else 0) -
        (if b < |z| ∧ |z| < 1 then V (s.toNNReal,w) else 0)) := by
    simp only [k,g,h,A,B,Set.indicator_apply,Set.mem_setOf_eq]
    rw [mul_sub]
    simp only [mul_ite,mul_zero]
  simp_rw [heq]
  apply Kyprianou.Ch04.gridMarkedKernelBudgetV1 P ν hν a b K ha hab hb hK T
    (fun s w => W (s.toNNReal,w)) (fun s w => V (s.toNNReal,w)) S hS hSnn _ hEnergy
  filter_upwards [hDiff] with w hw
  exact fun s _ => ⟨hWb _,hw _⟩
