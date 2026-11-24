-- Prove2me | solution 1 for Kyprianou.Ch03.finiteCylinderOfOrderedGridLawsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:24:28.604674+00:00
-- url     : https://prove2.me/submissions/28c0a193-4b48-4847-9881-9bea44fb98ef

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_finiteOrderedGridCoversV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (t : NNReal) (F G : NNReal → Omega → Real)
    (hF : ∀ s, AEMeasurable (F s) P)
    (hG : ∀ s, AEMeasurable (G s) P)
    (hLaw : ∀ (n : Nat) (q : Fin (n + 1) → NNReal),
      Monotone q → q 0 = 0 → (∀ i, q i ≤ t) →
      P.map (fun ω : Omega => fun i => F (q i) ω) =
      P.map (fun ω : Omega => fun i => G (q i) ω))
    (J : Finset {s : NNReal // s ≤ t})
    (B : {s : NNReal // s ≤ t} → Set Real)
    (hB : ∀ i ∈ J, MeasurableSet (B i)) :
    P ((fun ω : Omega => fun s : {s : NNReal // s ≤ t} => F s ω) ⁻¹'
      Set.pi (J : Set {s : NNReal // s ≤ t}) B) =
    P ((fun ω : Omega => fun s : {s : NNReal // s ≤ t} => G s ω) ⁻¹'
      Set.pi (J : Set {s : NNReal // s ≤ t}) B) := by
  classical
  obtain ⟨n, q, hq, h0, hqt, hcover⟩ := Kyprianou.Ch03.finiteOrderedGridCoversV1 t J
  let k (j : J) := (hcover j.val j.property).choose
  have hk (j : J) : q (k j) = (j.val : NNReal) :=
    (hcover j.val j.property).choose_spec
  let C : Set (Fin (n + 1) → ℝ) := {v | ∀ j : J, v (k j) ∈ B j.val}
  have hCeq : C = ⋂ j : J, (fun v : Fin (n + 1) → ℝ => v (k j)) ⁻¹' B j.val := by
    ext v
    simp [C]
  have hC : MeasurableSet C := by
    rw [hCeq]
    exact MeasurableSet.iInter fun j => measurable_pi_apply (k j) (hB j.val j.property)
  have hmF : AEMeasurable (fun ω : Omega => fun i => F (q i) ω) P :=
    aemeasurable_pi_iff.mpr fun i => hF _
  have hmG : AEMeasurable (fun ω : Omega => fun i => G (q i) ω) P :=
    aemeasurable_pi_iff.mpr fun i => hG _
  have he := congrArg (fun m : Measure (Fin (n + 1) → ℝ) => m C) (hLaw n q hq h0 hqt)
  rw [Measure.map_apply_of_aemeasurable hmF hC,
    Measure.map_apply_of_aemeasurable hmG hC] at he
  have hpre (H : NNReal → Omega → ℝ) :
      (fun ω : Omega => fun s : {s : NNReal // s ≤ t} => H s ω) ⁻¹'
        Set.pi (J : Set _) B =
      (fun ω : Omega => fun i => H (q i) ω) ⁻¹' C := by
    apply Set.ext
    intro ω
    change (∀ s ∈ (J : Set _), H s ω ∈ B s) ↔ ∀ j : J, H (q (k j)) ω ∈ B j.val
    simp only [hk]
    exact ⟨fun h j => h j.val j.property, fun h s hs => h ⟨s, hs⟩⟩
  rw [hpre F, hpre G]
  exact he
