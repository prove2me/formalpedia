-- Prove2me | solution 1 for Kyprianou.Ch04.markedFullClockAEMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:31:42.318723+00:00
-- url     : https://prove2.me/submissions/c35ba377-5410-4fd7-8501-5e2fccc5a582

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A full nonnegative predictable random integral is a.e. measurable by finite-band exhaustion. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (ℝ × ℝ))
    (hR : ∀ S : Set (ℝ × ℝ), MeasurableSet S → Measurable (fun w => R w S))
    (t : NNReal) (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (hFin : ∀ n, ∀ᵐ w ∂P, R w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n) ≠ ⊤)
    (f : ((NNReal × Omega) × ℝ) → ENNReal)
    (hf : Measurable[F.predictable.prod inferInstance] f) :
    AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      f ((z.1.toNNReal,w),z.2) ∂(R w)) P := by
  let U : ℕ → Set (ℝ × ℝ) := fun n => Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n
  let G : ℕ → Omega → ENNReal := fun n w =>
    ∫⁻ z in U n, f ((z.1.toNNReal,w),z.2) ∂(R w)
  have hG (n : ℕ) : AEMeasurable (G n) P := by
    obtain ⟨M,hM⟩ := Kyprianou.Ch04.finiteMarkedClockMeasure P F R hR t (B n) (hB n) (hFin n)
    exact (hM f hf).1
  have hu : Monotone U := fun i j hij _ hz => ⟨hz.1,hmono hij hz.2⟩
  have hcov : (⋃ n, U n) = Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hz
      exact ⟨hn.1,Set.mem_univ _⟩
    · intro hz
      have hm : z.2 ∈ ⋃ n, B n := by rw [hcover]; exact Set.mem_univ _
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hm
      exact Set.mem_iUnion.mpr ⟨n,hz.1,hn⟩
  have hd : Directed (· ⊆ ·) U := fun i j =>
    ⟨max i j,hu (le_max_left _ _),hu (le_max_right _ _)⟩
  have he : (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      f ((z.1.toNNReal,w),z.2) ∂(R w)) = fun w => ⨆ n, G n w := by
    funext w
    rw [← hcov]
    exact setLIntegral_iUnion_of_directed _ hd
  rw [he]
  exact AEMeasurable.iSup hG
