-- Prove2me | solution 1 for Kyprianou.Ch01.shiftedDriverRealisesPopulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:12:07.800052+00:00
-- url     : https://prove2.me/submissions/ff687145-3570-4d0f-b193-ad64b53f7d24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_branchingCountDeterminedBySequenceLaw

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (hFullProductLaw : HasLaw
      (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q)
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    Q {ω | (compoundPoissonToBranching
        (integerCompoundPoisson z
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)) s ω).toNat = m} =
      K z s m := by
  rw [hRealisation]
  let μ : (ℕ ⊕ ℕ) → Measure ℝ :=
    Sum.elim (fun _ : ℕ => expMeasure rate) (fun _ : ℕ => jumpLaw)
  let σ : ℕ ⊕ ℕ → ℕ ⊕ ℕ := Sum.map Nat.succ Nat.succ
  have hExp : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
    (hdriver.law_interarrival 0).isProbabilityMeasure_iff.mp inferInstance
  have hμ : ∀ i : ℕ ⊕ ℕ, IsProbabilityMeasure (μ i) := by
    rintro (n | n)
    · simpa [μ] using hExp
    · simpa [μ] using (inferInstance : IsProbabilityMeasure jumpLaw)
  have hShiftPi : (Measure.infinitePi μ).map (fun x i => x (σ i)) = Measure.infinitePi μ := by
    have hσinj : Function.Injective σ :=
      Sum.map_injective.mpr ⟨Nat.succ_injective, Nat.succ_injective⟩
    have hσμ : ∀ i, μ (σ i) = μ i := by rintro (_ | _) <;> rfl
    classical
    apply Measure.eq_infinitePi (hμ := hμ)
    intro s t ht
    have hm : Measurable (fun x : (ℕ ⊕ ℕ) → ℝ => fun i => x (σ i)) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
    rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
    let box : (ℕ ⊕ ℕ) → Set ℝ := fun j =>
      ⋃ (i : ℕ ⊕ ℕ) (_ : i ∈ s) (_ : σ i = j), t i
    have hpre :
        (fun x i => x (σ i)) ⁻¹' (s : Set (ℕ ⊕ ℕ)).pi t =
          Set.pi (Finset.image σ s : Set (ℕ ⊕ ℕ)) box := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, box, Set.mem_iUnion]
      constructor
      · intro hx j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact ⟨i, hi, rfl, hx i hi⟩
      · intro hx i hi
        obtain ⟨i', hi', hσ, hx'⟩ := hx (σ i) (Finset.mem_image_of_mem σ hi)
        obtain rfl := hσinj hσ
        exact hx'
    rw [hpre]
    have hset : ∀ i ∈ s, box (σ i) = t i := by
      intro i hi
      ext r
      simp only [box, Set.mem_iUnion]
      constructor
      · rintro ⟨i', hi', hσ, hr⟩
        obtain rfl := hσinj hσ
        exact hr
      · intro hr
        exact ⟨i, hi, rfl, hr⟩
    have hbox : ∀ j ∈ Finset.image σ s, MeasurableSet (box j) := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      simpa [hset i hi] using ht i
    rw [Measure.infinitePi_pi (μ := μ) (s := Finset.image σ s) (t := box) hbox]
    have hOn : Set.InjOn σ (s : Set (ℕ ⊕ ℕ)) := fun _ _ _ _ h => hσinj h
    rw [Finset.prod_image hOn]
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [hset i hi, hσμ]
  let unpack : ((ℕ ⊕ ℕ) → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun x => (fun n => x (Sum.inl n), fun n => x (Sum.inr n))
  have hUnpack : Measurable unpack :=
    Measurable.prod
      (measurable_pi_lambda _ (fun n => measurable_pi_apply (Sum.inl n)))
      (measurable_pi_lambda _ (fun n => measurable_pi_apply (Sum.inr n)))
  let ν : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := (Measure.infinitePi μ).map unpack
  have hU : HasLaw unpack ν (Measure.infinitePi μ) := ⟨hUnpack.aemeasurable, rfl⟩
  have hOrig : HasLaw (fun w => (fun n => arrival n w, fun n => marks n w)) ν Q := by
    have hcomp := hU.comp hFullProductLaw
    have hEq : (fun w => (fun n => arrival n w, fun n => marks n w)) =
        unpack ∘ (fun w (i : ℕ ⊕ ℕ) => Sum.elim arrival marks i w) := by
      funext w
      rfl
    simpa [hEq] using hcomp
  have hShift : HasLaw
      (fun w => (fun n => arrival (n + 1) w, fun n => marks (n + 1) w)) ν Q := by
    let pre : ((ℕ ⊕ ℕ) → ℝ) → ((ℕ ⊕ ℕ) → ℝ) := fun x i => x (σ i)
    have hPre : Measurable pre :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
    have hP : HasLaw pre ((Measure.infinitePi μ).map pre) (Measure.infinitePi μ) :=
      ⟨hPre.aemeasurable, rfl⟩
    have hPreLaw : HasLaw (pre ∘ fun w i => Sum.elim arrival marks i w)
        (Measure.infinitePi μ) Q := by
      have hcomp := hP.comp hFullProductLaw
      rw [hShiftPi] at hcomp
      exact hcomp
    have hcomp := hU.comp hPreLaw
    have hEq : (fun w => (fun n => arrival (n + 1) w, fun n => marks (n + 1) w)) =
        unpack ∘ pre ∘ (fun w i => Sum.elim arrival marks i w) := by
      funext w
      ext n
      · rfl
      · rfl
    simpa [hEq, Function.comp] using hcomp
  exact branchingCountDeterminedBySequenceLaw Q rate arrival marks jumpLaw hNoExplosion
    hTailDriver ν hOrig hShift z s m
