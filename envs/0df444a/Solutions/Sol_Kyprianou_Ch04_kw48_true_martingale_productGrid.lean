-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_true_martingale_productGrid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:44:57.362949+00:00
-- url     : https://prove2.me/submissions/ed845f0b-d187-446e-875c-91749825fd07

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_M_adapted_integrable
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_event_ledger
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_gain_uniform_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_capped_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_envelope_integrable
import Theorems.Thm_Kyprianou_Ch04_kw48_martingale_from_grid_event_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex reflected two-parameter process is a true martingale
by dominated transfer of centred predictable product grids. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I*(theta:Complex)*(L.X t w:Complex)) ∂P) =
      Complex.exp (-((t:Real):Complex)*Psi theta))
    (alpha beta : Real) : Martingale (M L Psi alpha beta) F P := by
  letI : IsProbabilityMeasure P := L.isProbability
  let u : NNReal → NNReal → Nat → Nat → NNReal := fun a b n i =>
    a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  let q : NNReal → NNReal → Nat → Ω → Complex := fun a b n =>
    Q L Psi alpha beta (u a b n) (n+1)
  let B : NNReal → NNReal → Ω → Real := fun _ b w =>
    2*envelope L Psi alpha beta b w
  have hM := Kyprianou.Ch04.kw48_M_adapted_integrable P F L Psi alpha beta
  have hLedger (a b : NNReal) (hab : a ≤ b) (n : Nat) :
      Integrable (q a b n) P ∧ ∀ A : Set Ω, MeasurableSet[F a] A →
        (∫ w in A, q a b n w ∂P) = 0 := by
    obtain ⟨hu,h0,_,_,_,_⟩ := Kyprianou.Ch04.kw47_capped_uniform_grid a b hab
    exact Kyprianou.Ch04.kw48_grid_event_ledger L Psi hPsi alpha beta
      (u a b n) (n+1) (hu n) a (le_of_eq (h0 n).symm)
  apply Kyprianou.Ch04.kw48_martingale_from_grid_event_limit P F
    (M L Psi alpha beta) hM.1 hM.2 q B
  · intro a b hab n
    exact (hLedger a b hab n).1
  · intro a b hab
    exact (Kyprianou.Ch04.kw48_envelope_integrable P F L Psi alpha beta b).const_mul 2
  · intro a b hab n
    obtain ⟨hu,_,_,hT,_,_⟩ := Kyprianou.Ch04.kw47_capped_uniform_grid a b hab
    exact Eventually.of_forall fun w =>
      Kyprianou.Ch04.kw48_grid_gain_uniform_bound L Psi alpha beta b
        (u a b n) (n+1) (hu n) (hT n) w
  · intro a b hab
    exact Eventually.of_forall fun w =>
      Kyprianou.Ch04.kw48_capped_grid_pathwise_limit L Psi alpha beta a b hab w
  · intro a b hab n
    exact (hLedger a b hab n).2
