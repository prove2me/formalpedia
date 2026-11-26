-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_trueMartingale_productGrid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:06:05.695424+00:00
-- url     : https://prove2.me/submissions/4a633b2b-65eb-4fdd-9165-b25c0b3260b4

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_adapted
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_esscher_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_integrable
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_ledger
import Theorems.Thm_Kyprianou_Ch04_kw47_martingale_from_grid_event_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_integrable_envelope
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_uniform_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_past_event_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer the centred predictable product grids to the actual
Kella--Whitt martingale by integrable domination. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha) :
    let supX : NNReal → Ω → Real := fun t w =>
      sSup ((fun s : NNReal => L.X s w) '' Set.Iic t)
    let M : NNReal → Ω → Real := fun t w =>
      L.ψ alpha * (∫ s in Set.Icc (0:Real) (t:Real),
        Real.exp (-alpha*(supX s.toNNReal w-L.X s.toNNReal w)) ∂volume) +
      1-Real.exp (-alpha*(supX t w-L.X t w))-alpha*supX t w
    Martingale M F P := by
  dsimp only
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L]
  letI : IsProbabilityMeasure P := L.isProbability
  let U := runningSup L
  let Z : NNReal → Ω → Real := fun t w => Real.exp (-alpha*(U t w-L.X t w))
  let J : NNReal → Ω → Real := fun t w => ∫ s in Icc (0:Real) (t:Real),
    Z s.toNNReal w ∂volume
  let M : NNReal → Ω → Real := fun t w =>
    L.ψ alpha * J t w + 1 - Z t w - alpha*U t w
  let E : NNReal → Ω → Real := fun t w =>
    Real.exp (alpha*L.X t w-L.ψ alpha*(t:Real))
  let H : NNReal → Ω → Real := fun t w =>
    Real.exp (-alpha*U t w+L.ψ alpha*(t:Real))
  let u : NNReal → NNReal → Nat → Nat → NNReal := fun a b n i =>
    a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  let Q : NNReal → NNReal → Nat → Ω → Real := fun a b n w =>
    ∑ i ∈ Finset.range (n+1), H (u a b n i) w *
      (E (u a b n (i+1)) w-E (u a b n i) w)
  let B : NNReal → NNReal → Ω → Real := fun _ b w =>
    4*Real.exp (alpha * U b w + |L.ψ alpha| * (b:Real))*
      Real.exp (|L.ψ alpha| * (b:Real))
  have hAdapt : StronglyAdapted F M :=
    Kyprianou.Ch04.kw47_actual_adapted L alpha hAlpha
  have hInt (t : NNReal) : Integrable (M t) P :=
    Kyprianou.Ch04.kw47_actual_integrable P F L alpha hAlpha t
  have hB (a b : NNReal) : Integrable (B a b) P :=
    Kyprianou.Ch04.kw47_esscher_grid_gain_integrable_envelope L alpha hAlpha b
  have hLedger (a b : NNReal) (hab : a ≤ b) (n : Nat) :
      Integrable (Q a b n) P ∧ (∀ᵐ w ∂P, ‖Q a b n w‖ ≤ B a b w) ∧
      (∀ A : Set Ω, MeasurableSet[F a] A → (∫ w in A, Q a b n w ∂P) = 0) := by
    obtain ⟨hu,h0,_,hT,_,_⟩ := Kyprianou.Ch04.kw47_capped_uniform_grid a b hab
    exact Kyprianou.Ch04.kw47_esscher_grid_ledger P F L alpha hAlpha
      b (u a b n) (hu n) (hT n) (n+1) a (le_of_eq (h0 n).symm)
  exact Kyprianou.Ch04.kw47_martingale_from_grid_event_limit P F M hAdapt hInt Q B
    (fun a b hab n => (hLedger a b hab n).1)
    (fun a b _ => hB a b)
    (fun a b hab n => (hLedger a b hab n).2.1)
    (fun a b hab => Eventually.of_forall fun w =>
      Kyprianou.Ch04.kw47_capped_esscher_grid_limit L alpha hAlpha a b hab w)
    (fun a b hab n => (hLedger a b hab n).2.2)
