-- Prove2me | solution 1 for Kyprianou.Ch04.markedExpectedIntegralExhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:56:34.869808+00:00
-- url     : https://prove2.me/submissions/47f607b0-8b91-4b7f-8c65-89d29e24923f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (Real × Real))
    (hR : ∀ S : Set (Real × Real), MeasurableSet S →
      Measurable (fun w => R w S))
    (t : NNReal) (B : Nat → Set Real) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (hFin : ∀ n, ∀ᵐ w ∂P, R w (Set.Icc (0 : Real) (t : Real) ×ˢ B n) ≠ ⊤)
    (f : ((NNReal × Omega) × Real) → ENNReal) (hf : Measurable[F.predictable.prod inferInstance] f) :
    (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P) =
    ⨆ n, (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ (B n),
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P) := by
  let U : Nat → Set (Real × Real) := fun n =>
    Set.Icc (0 : Real) (t : Real) ×ˢ B n
  let G : Nat → Omega → ENNReal := fun n w =>
    ∫⁻ z in U n, f ((z.1.toNNReal, w), z.2) ∂(R w)
  have hG : ∀ n, AEMeasurable (G n) P := by
    intro n
    obtain ⟨M, hM⟩ := finiteMarkedClockMeasure P F R hR t (B n) (hB n) (hFin n)
    exact (hM f hf).1
  have hUmono : Monotone U := fun i j hij _ hz => ⟨hz.1, hmono hij hz.2⟩
  have hUcover : (⋃ n, U n) = Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact ⟨hn.1, Set.mem_univ _⟩
    · intro hz
      have hx : z.2 ∈ ⋃ n, B n := by rw [hcover]; exact Set.mem_univ _
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n, hz.1, hn⟩
  have hdir : Directed (· ⊆ ·) U :=
    fun i j => ⟨max i j, hUmono (le_max_left _ _), hUmono (le_max_right _ _)⟩
  have he : (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      f ((z.1.toNNReal, w), z.2) ∂(R w)) = fun w => ⨆ n, G n w := by
    funext w
    rw [← hUcover]
    exact setLIntegral_iUnion_of_directed _ hdir
  rw [he]
  exact lintegral_iSup' hG
    (Filter.Eventually.of_forall (fun w i j hij => lintegral_mono_set (hUmono hij)))
