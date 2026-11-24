-- Prove2me | solution 1 for Kyprianou.Ch04.commonNullEventCutoffAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:41:11.564022+00:00
-- url     : https://prove2.me/submissions/cba1ce6b-03f3-4ed8-9790-30241d96ace9

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Classical

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : (∀ᵐ omega ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (r : Real) (Set.Iio (r : Real)))
        (nhds (phi (r : Real) x omega))))
    (u : NNReal) (A : Set Omega) (hA : MeasurableSet[F u] A) :
    IsAdmissiblePoissonKernel P F (fun (s x : Real) (omega : Omega) => if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0) ∧
    (∀ᵐ omega ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0)
        (nhdsWithin (r : Real) (Set.Iio (r : Real)))
        (nhds (if (u : Real) < (r : Real) ∧ omega ∈ A then phi (r : Real) x omega else 0))) := by
  classical
  let psi : Real → Real → Omega → Real :=
    fun s x omega => if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0
  change IsAdmissiblePoissonKernel P F psi ∧ _
  have hAm : MeasurableSet A := F.le u A hA
  have hleft : ∀ᵐ omega ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => psi s x omega)
        (nhdsWithin (r : Real) (Set.Iio (r : Real)))
        (nhds (psi (r : Real) x omega)) := by
    filter_upwards [hCommon] with omega homega
    intro x r hr
    by_cases h : (u : Real) < (r : Real) ∧ omega ∈ A
    · have hev : ∀ᶠ s : Real in nhdsWithin (r : Real) (Set.Iio (r : Real)),
          (u : Real) < s := nhdsWithin_le_nhds (Ioi_mem_nhds h.1)
      have hEq : (fun s : Real => phi s x omega) =ᶠ[
          nhdsWithin (r : Real) (Set.Iio (r : Real))] (fun s => psi s x omega) := by
        filter_upwards [hev] with s hs
        simp [psi, hs, h.2]
      simpa [psi, h] using (homega x r hr).congr' hEq
    · have hev : ∀ᶠ s : Real in nhdsWithin (r : Real) (Set.Iio (r : Real)),
          s < (r : Real) := eventually_mem_nhdsWithin
      have hEq : (fun _ : Real => (0 : Real)) =ᶠ[
          nhdsWithin (r : Real) (Set.Iio (r : Real))] (fun s => psi s x omega) := by
        filter_upwards [hev] with s hs
        have hs' : ¬ ((u : Real) < s ∧ omega ∈ A) :=
          fun hh => h ⟨lt_trans hh.1 hs, hh.2⟩
        simp [psi, hs']
      have hzero : psi (r : Real) x omega = 0 := by
        exact if_neg h
      rw [hzero]
      exact tendsto_const_nhds.congr' hEq
  refine ⟨?_, hleft⟩
  rcases hPhi with ⟨hn, hm, ha, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x omega
    dsimp [psi]
    split_ifs
    · exact hn s x omega
    · exact le_rfl
  · change Measurable (fun z : (Real × Real) × Omega =>
        if (u : Real) < z.1.1 ∧ z.2 ∈ A then phi z.1.1 z.1.2 z.2 else 0)
    exact Measurable.ite
      ((measurableSet_Ioi.preimage (measurable_fst.comp measurable_fst)).inter
        (hAm.preimage measurable_snd)) hm measurable_const
  · intro r
    by_cases hur : u < r
    · have hAr : MeasurableSet[F r] A := F.mono hur.le A hA
      have hUr : (u : Real) < (r : Real) := hur
      simp only [psi, hUr, true_and]
      exact Measurable.ite (hAr.preimage measurable_fst) (ha r) measurable_const
    · have hUr : ¬ (u : Real) < (r : Real) := hur
      simp only [psi, hUr, false_and, if_false]
      exact measurable_const
  · exact fun x => hleft.mono fun omega hw => hw x
