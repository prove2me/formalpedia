-- Prove2me | solution 1 for Kyprianou.Ch04.nestedPhysicalStepGridIdentityRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:00:57.848638+00:00
-- url     : https://prove2.me/submissions/da197902-d863-492a-81c2-8b742fda80af

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_physicalStepGridIdentityV1
import Theorems.Thm_Kyprianou_Ch04_physicalKernelDifferenceIdentityAEV1
import Theorems.Thm_Kyprianou_Ch04_compensatedBandPathRightV1
import Theorems.Thm_Kyprianou_Ch04_clippedGridRightContinuousV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The nested physical step-grid difference equals the difference kernel integral almost surely at every time, and is right continuous. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ) (H L : ℕ → Ω → ℝ)
    (hH : ∀ k ∈ Finset.range n, Measurable[F (u k)] (H k))
    (hL : ∀ k ∈ Finset.range n, Measurable[F (u k)] (L k))
    (hHb : ∀ k ∈ Finset.range n, ∀ w, |H k w| ≤ K)
    (hLb : ∀ k ∈ Finset.range n, ∀ w, |L k w| ≤ K)
    (Y Z : NNReal → Ω → ℝ)
    (hY : ∀ t w, Y t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | a < |x| ∧ |x| < 1},x ∂ν))
    (hZ : ∀ t w, Z t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | b < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | b < |x| ∧ |x| < 1},x ∂ν)) :
    let A : Set ℝ := {x | a < |x| ∧ |x| < 1}
    let B : Set ℝ := {x | b < |x| ∧ |x| < 1}
    let W := fun (p : NNReal × Ω) => ∑ k ∈ Finset.range n,
      (Ioc (u k) (u (k+1))).indicator (fun _ => H k p.2) p.1
    let V := fun (p : NNReal × Ω) => ∑ k ∈ Finset.range n,
      (Ioc (u k) (u (k+1))).indicator (fun _ => L k p.2) p.1
    let g := fun p : (NNReal × Ω) × ℝ => A.indicator (fun x => x * W p.1) p.2
    let h := fun p : (NNReal × Ω) × ℝ => B.indicator (fun x => x * V p.1) p.2
    let k := fun p => g p-h p
    let J := fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    let G := fun (U : NNReal → Ω → ℝ) (Q : ℕ → Ω → ℝ) (t : NNReal) w =>
      ∑ i ∈ Finset.range n, Q i w * (U (min t (u (i+1))) w-U (min t (u i)) w)
    Measurable[F.predictable.prod inferInstance] g →
    Measurable[F.predictable.prod inferInstance] h →
    (∀ p, ‖g p‖ ≤ K ∧ ‖h p‖ ≤ K) →
    (∀ p, p.2 ∉ A → g p = 0 ∧ h p = 0) →
    (∀ᵐ w ∂P, ∀ t, J t w = G Y H t w-G Z L t w) ∧
    (∀ᵐ w ∂P, ∀ t, Tendsto (fun s => J s w) (𝓝[>] t) (𝓝 (J t w))) := by
  intro A B W V g h k J G hg hh hC hs
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hAfin : ν A < ⊤ := (measure_mono (show A ⊆ {z | a ≤ |z|}
    from fun z hz => hz.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top ha)
  have hBfin : ν B < ⊤ := (measure_mono (show B ⊆ A from
    fun z hz => ⟨hab.trans hz.1,hz.2⟩)).trans_lt hAfin
  have hId1 := Kyprianou.Ch04.physicalStepGridIdentityV1 P ν N A hA hAfin
    (fun z hz => hz.2.le) u hu n H Y hY
  have hId2 := Kyprianou.Ch04.physicalStepGridIdentityV1 P ν N B hB hBfin
    (fun z hz => hz.2.le) u hu n L Z hZ
  have hlin := Kyprianou.Ch04.physicalKernelDifferenceIdentityAEV1 P ν F N A hA hAfin
    g h hg hh K hC hs
  have hJ : ∀ᵐ w ∂P, ∀ t, J t w = G Y H t w-G Z L t w := by
    filter_upwards [hId1,hId2,hlin] with w h1 h2 hl
    intro t
    exact (hl t).trans (congrArg₂ (· - ·) (h1 t) (h2 t))
  refine ⟨hJ,?_⟩
  have hy := Kyprianou.Ch04.compensatedBandPathRightV1 P ν N A hA hAfin hz Y hY
  have hz' := Kyprianou.Ch04.compensatedBandPathRightV1 P ν N B hB hBfin hz Z hZ
  filter_upwards [hJ,hy,hz'] with w hw hyw hzw
  have hfun : (fun s => J s w) = fun s => G Y H s w-G Z L s w := funext hw
  intro t
  rw [hfun,hw t]
  exact (Kyprianou.Ch04.clippedGridRightContinuousV1 (fun s => Y s w) hyw u n
    (fun i => H i w) t).sub
    (Kyprianou.Ch04.clippedGridRightContinuousV1 (fun s => Z s w) hzw u n (fun i => L i w) t)
