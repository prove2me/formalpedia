-- Prove2me | solution 1 for Kyprianou.Ch04.physicalStepGridPairMaximalBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:03:57.417069+00:00
-- url     : https://prove2.me/submissions/a7901142-fc1a-4a24-bbce-65c0e873bb3f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_gridStepWeightMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_gridStepUniformWeightBoundV1
import Theorems.Thm_Kyprianou_Ch04_gridStepDifferenceWeightBoundV1
import Theorems.Thm_Kyprianou_Ch04_nestedGridStepKernelEnergyV1
import Theorems.Thm_Kyprianou_Ch04_nestedPhysicalStepGridIdentityRightV1
import Theorems.Thm_Kyprianou_Ch04_physicalKernelMaximalProbabilityV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The nested physical step-grid error obeys a mesh-independent maximal probability bound from the predictable kernel energy estimate. -/
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
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | b < |x| ∧ |x| < 1},x ∂ν))
    (X : NNReal → Ω → ℝ) (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (t : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (t : ℝ) ×ˢ univ → Measurable[F t] (fun w => N.N w D))
    (T : NNReal) (hT : 0 < T) (S : Ω → ℝ) (hS : Integrable S P)
    (hSnn : ∀ᵐ w ∂P, 0 ≤ S w)
    (hDiff : ∀ᵐ w ∂P, ∀ i ∈ Finset.range n, |H i w-L i w| ≤ K * Real.sqrt (S w))
    (hEnergy : (∫ w, S w ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
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
    ∀ δ : ℝ, 0 < δ →
      P {w | ∃ t ≤ T, δ ≤ |G Y H t w-G Z L t w|} ≤
      ENNReal.ofReal (4 * ((K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal)) /
        ENNReal.ofReal ((δ/2)^2) := by
  intro A B W V g h k J G δ hδ
  have hW := Kyprianou.Ch04.gridStepWeightMeasurableV1 F u n H hH
  have hV := Kyprianou.Ch04.gridStepWeightMeasurableV1 F u n L hL
  have hWb (p : NNReal × Ω) : |W p| ≤ K :=
    Kyprianou.Ch04.gridStepUniformWeightBoundV1 u hu n H K hK hHb p.1 p.2
  have hVb (p : NNReal × Ω) : |V p| ≤ K :=
    Kyprianou.Ch04.gridStepUniformWeightBoundV1 u hu n L K hK hLb p.1 p.2
  have hD : ∀ᵐ w ∂P, ∀ t, |W (t,w)-V (t,w)| ≤ K*Real.sqrt (S w) := by
    filter_upwards [hDiff] with w hw
    exact Kyprianou.Ch04.gridStepDifferenceWeightBoundV1 u hu n
      (fun i => H i w) (fun i => L i w) _ (by positivity) hw
  obtain ⟨hg,hh,hC,hs,hE⟩ := Kyprianou.Ch04.nestedGridStepKernelEnergyV1 P ν hν F
    a b K ha hab hb hK T W V hW hV hWb hVb S hS hSnn hD hEnergy
  obtain ⟨hId,hr⟩ := Kyprianou.Ch04.nestedPhysicalStepGridIdentityRightV1
    P ν hν F N hz a b K ha hab hb hK u hu n H L hH hL hHb hLb Y Z hY hZ hg hh hC hs
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hfin : ν A < ⊤ := (measure_mono (show A ⊆ {z | a ≤ |z|}
    from fun z hz => hz.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top ha)
  have hk : Measurable[F.predictable.prod inferInstance] k := hg.sub hh
  have hkb (p) : ‖k p‖ ≤ 2*K :=
    (norm_sub_le _ _).trans (by linarith [(hC p).1,(hC p).2])
  have hks (p) (hp : p.2 ∉ A) : k p = 0 := by
    change g p - h p = 0
    have hg0 : g p = 0 := (hs p hp).1
    have hh0 : h p = 0 := (hs p hp).2
    exact sub_eq_zero.mpr (hg0.trans hh0.symm)
  have hmax := Kyprianou.Ch04.physicalKernelMaximalProbabilityV1 P ν X F hF N
    hFuture hPast A hA hfin k hk (2*K) (by positivity) hkb hks T hT _ hE hr
      (δ/2) (by positivity)
  refine le_trans (measure_mono_ae ?_) hmax
  filter_upwards [hId] with w hw
  rintro ⟨t,ht,hd⟩
  exact ⟨t,ht,by rw [hw t]; linarith⟩
