-- Prove2me | solution 1 for Kyprianou.Ch04.physicalFiniteVariationGridEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:41:07.470536+00:00
-- url     : https://prove2.me/submissions/8ccae293-7378-4a50-afdf-95e1d59039eb

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_physicalLargeGridWeightErrorV1
import Theorems.Thm_Kyprianou_Ch04_normalisedWeightStateBoundV1
import Theorems.Thm_Kyprianou_Ch04_physicalAbsoluteLedgerMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_gridUniformWeightedEnvelopeProbabilityV1
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A common physical finite-variation state has uniform grid convergence
under compact convergence of the states defining its normalised weights. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (T : NNReal) (b K : ℝ) (hK : 0 ≤ K)
    (X L V : NNReal → Ω → ℝ) (Y U : ℕ → NNReal → Ω → ℝ)
    (g : ℝ → ℝ → ℝ)
    (hLip : ∀ s : NNReal, ∀ x y : ℝ, |g s x-g s y| ≤ K * |x-y|)
    (hV : ∀ t w, V t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hAtoms : ∀ᵐ w ∂P, ∃ S : Finset NNReal,
      (∀ r ∈ S, 0 < r ∧ r ≤ T ∧ 1/2 < |X r w-L r w|) ∧
      (N.N w).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
        ∑ r ∈ S, Measure.dirac ((r : ℝ),X r w-L r w))
    (hX : ∀ᵐ w ∂P, ∀ t, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hY : ∀ᵐ w ∂P, ∀ m t, 0 < t →
      Tendsto (fun s => Y m s w) (nhdsWithin t (Iio t)) (nhds (U m t w)))
    (D : ℕ → Ω → ℝ≥0∞) (hD : ∀ m, Measurable (D m))
    (hb : ∀ᵐ w ∂P, ∀ m t, t ≤ T → ENNReal.ofReal |Y m t w-X t w| ≤ D m w)
    (hc : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d) :
    let G := fun (H : NNReal → Ω → ℝ) (n : ℕ) (t : NNReal) w =>
      ∑ k ∈ Finset.range n, H (T * (k : NNReal) / (n : NNReal)) w *
        (V (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
          V (min t (T * (k : NNReal) / (n : NNReal))) w)
    let H := fun (s : NNReal) w => if s = 0 then 0 else g (s : ℝ) (L s w)
    let Hc := fun m (s : NNReal) w => if s = 0 then 0 else g (s : ℝ) (U m s w)
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, (P {w | ∃ t ≤ T, δ ≤ |G (Hc m) n t w-G H n t w|}).toReal ≤ η := by
  intro G H Hc
  let B := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}
  let C (w : Ω) := K * (|b| * (T : ℝ) + ∫ z in B, |z.2| ∂(N.N w))
  have hC : Measurable C := measurable_const.mul (measurable_const.add
    (Kyprianou.Ch04.physicalAbsoluteLedgerMeasurableV1 P ν N B
      (measurableSet_Icc.prod (measurableSet_lt measurable_const measurable_id.abs))))
  apply Kyprianou.Ch04.gridUniformWeightedEnvelopeProbabilityV1 P
    (fun m n t w => G (Hc m) n t w-G H n t w) T C D hC hD _ hc
  filter_upwards [hAtoms,hX,hY,hb] with w hw hXw hYw hbw
  obtain ⟨S,hS,hR⟩ := hw
  refine ⟨mul_nonneg hK (add_nonneg (by positivity) (integral_nonneg fun z => abs_nonneg z.2)),?_⟩
  intro m hm n t ht
  have hstate (s : NNReal) (hs : s ≤ T) : |Y m s w-X s w| ≤ (D m w).toReal := by
    have hh := ENNReal.toReal_mono hm (hbw m s hs)
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at hh
  have hW := Kyprianou.Ch04.normalisedWeightStateBoundV1
    (fun s => Y m s w) (fun s => X s w) (fun s => U m s w) (fun s => L s w)
    T g K (D m w).toReal hK ENNReal.toReal_nonneg (hYw m) hXw hstate hLip
  let u (k : ℕ) : NNReal := T * (k : NNReal) / (n : NNReal)
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  have hweight (k : ℕ) (hk : k ∈ Finset.range n) : |Hc m (u k) w-H (u k) w| ≤
      K * (D m w).toReal := by
    apply hW
    have hn : 0 < (n : NNReal) := by exact_mod_cast Nat.zero_lt_of_lt (Finset.mem_range.mp hk)
    dsimp [u]
    rw [div_le_iff₀ hn]
    gcongr
    exact_mod_cast (Finset.mem_range.mp hk).le
  have hh := Kyprianou.Ch04.physicalLargeGridWeightErrorV1 (N.N w) T S
    (fun r => X r w-L r w) (fun s => V s w) (fun s => Hc m s w) (fun s => H s w)
    b (K * (D m w).toReal) (mul_nonneg hK ENNReal.toReal_nonneg)
    u hu n hS hR (fun s _ => hV s w) hweight t ht
  exact hh.trans_eq (by dsimp [C,B]; ring)
