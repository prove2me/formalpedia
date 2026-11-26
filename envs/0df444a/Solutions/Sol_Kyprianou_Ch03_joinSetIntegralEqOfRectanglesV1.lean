-- Prove2me | solution 1 for Kyprianou.Ch03.joinSetIntegralEqOfRectanglesV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:32:40.916923+00:00
-- url     : https://prove2.me/submissions/8a1d0a0f-d16a-4b46-8d85-011b39b5f12b

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem _root_.solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (m h : MeasurableSpace Omega)
    (hjoin : m ⊔ h ≤ mΩ)
    (f z : Omega → ℝ) (hf : Integrable f P) (hz : Integrable z P)
    (hrect : ∀ C D : Set Omega, MeasurableSet[m] C → MeasurableSet[h] D →
      (∫ x in C ∩ D, z x ∂P) = ∫ x in C ∩ D, f x ∂P) :
    ∀ S : Set Omega, MeasurableSet[m ⊔ h] S →
      (∫ x in S, z x ∂P) = ∫ x in S, f x ∂P := by
  intro S hS
  have hzf : ∀ C D : Set Omega, MeasurableSet[m] C → MeasurableSet[h] D → ∫ x in C ∩ D, (z x - f x) ∂P = 0 := by
    intro C D hC hD
    rw [integral_sub hz.integrableOn hf.integrableOn, hrect C D hC hD, sub_self]
  suffices H : ∫ x in S, (z x - f x) ∂P = 0 by
    rw [integral_sub hz.integrableOn hf.integrableOn] at H; linarith
  set R : Set (Set Omega) := {T | ∃ C D : Set Omega, MeasurableSet[m] C ∧ MeasurableSet[h] D ∧ T = C ∩ D} with hR
  have hgen : (m ⊔ h) = MeasurableSpace.generateFrom R := by
    apply le_antisymm
    · refine sup_le (fun C hC => ?_) (fun D hD => ?_)
      · exact MeasurableSpace.measurableSet_generateFrom ⟨C, Set.univ, hC, MeasurableSet.univ, (Set.inter_univ C).symm⟩
      · exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, D, MeasurableSet.univ, hD, (Set.univ_inter D).symm⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro T ⟨C, D, hC, hD, rfl⟩
      exact MeasurableSet.inter ((le_sup_left : m ≤ m ⊔ h) _ hC) ((le_sup_right : h ≤ m ⊔ h) _ hD)
  have hpi : IsPiSystem R := by
    rintro _ ⟨C, D, hC, hD, rfl⟩ _ ⟨C', D', hC', hD', rfl⟩ _
    exact ⟨C ∩ C', D ∩ D', hC.inter hC', hD.inter hD', Set.inter_inter_inter_comm C D C' D'⟩
  have hint : Integrable (fun x => z x - f x) P := hz.sub hf
  have htot : ∫ x, (z x - f x) ∂P = 0 := by
    have := hzf Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    rwa [Set.inter_univ, setIntegral_univ] at this
  refine MeasurableSpace.induction_on_inter (m := m ⊔ h) (C := fun T _ => ∫ x in T, (z x - f x) ∂P = 0) hgen hpi ?_ ?_ ?_ ?_ S hS
  · simp
  · rintro T ⟨C, D, hC, hD, rfl⟩
    exact hzf C D hC hD
  · intro T hT ih
    have := integral_add_compl (hjoin _ hT) hint
    rw [ih, zero_add, htot] at this
    exact this
  · intro g hd hg ih
    rw [integral_iUnion (fun i => hjoin _ (hg i)) hd hint.integrableOn]
    simp [ih]

