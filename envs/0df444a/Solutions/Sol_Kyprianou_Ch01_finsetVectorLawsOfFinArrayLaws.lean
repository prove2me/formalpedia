-- Prove2me | solution 1 for Kyprianou.Ch01.finsetVectorLawsOfFinArrayLaws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:19:25.97485+00:00
-- url     : https://prove2.me/submissions/ca3df8a0-339c-417b-ab95-5a8022811442

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Data.Fintype.EquivFin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Encode an arbitrary finite coordinate set using Fin n for path laws. -/
theorem solution
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (F : Ω → (ι → ℤ)) (G : Ω' → (ι → ℤ))
    (hF : Measurable F) (hG : Measurable G)
    (hJoint : ∀ n : ℕ, ∀ times : Fin n → ι,
      P.map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i))) :
    ∀ J : Finset ι,
      P.map (fun ω => fun j : J => F ω j) =
        Q.map (fun ω => fun j : J => G ω j) := by
  classical
  intro J
  let e : J ≃ Fin J.card := J.equivFin
  let proj : (Fin J.card → ℤ) → (J → ℤ) :=
    fun v j => v (e j)
  have hProj : Measurable proj := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (e j)
  have hLeft : Measurable (fun ω : Ω =>
      fun i : Fin J.card => F ω (e.symm i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (e.symm i : ι)).comp hF
  have hRight : Measurable (fun ω : Ω' =>
      fun i : Fin J.card => G ω (e.symm i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (e.symm i : ι)).comp hG
  calc
    P.map (fun ω => fun j : J => F ω j) =
        (P.map (fun ω => fun i : Fin J.card => F ω (e.symm i))).map proj := by
          rw [Measure.map_map hProj hLeft]
          congr 1
          funext ω j
          simp [proj]
    _ = (Q.map (fun ω => fun i : Fin J.card => G ω (e.symm i))).map proj := by
          rw [hJoint J.card (fun i => (e.symm i : ι))]
    _ = Q.map (fun ω => fun j : J => G ω j) := by
          rw [Measure.map_map hProj hRight]
          congr 1
          funext ω j
          simp [proj]
