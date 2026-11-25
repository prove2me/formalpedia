-- Prove2me | solution 1 for Kyprianou.Ch04.predictableMarkedWindowMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:07:20.305407+00:00
-- url     : https://prove2.me/submissions/13b1667b-8e2a-4ab2-8e78-957ec76bc4ac

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (a : NNReal) (D : Set NNReal)
    (hD : ∀ A : Set Omega, MeasurableSet[F a] A →
      MeasurableSet[F.predictable] (D ×ˢ A))
    (g : Omega × Real → ENNReal)
    (hg : Measurable[(F a).prod inferInstance] g) :
    Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real =>
        @ite ENNReal (z.1.1 ∈ D) (Classical.propDecidable _) (g (z.1.2, z.2)) 0) := by
  classical
  letI : MeasurableSpace ((NNReal × Omega) × Real) := F.predictable.prod inferInstance
  let S : Set ((NNReal × Omega) × Real) := {z | z.1.1 ∈ D}
  have hSe : S = (D ×ˢ (Set.univ : Set Omega)) ×ˢ (Set.univ : Set Real) := by
    ext z
    change (z.1.1 ∈ D) ↔ ((z.1.1 ∈ D ∧ z.1.2 ∈ (Set.univ : Set Omega)) ∧
      z.2 ∈ (Set.univ : Set Real))
    simp
  have hS : MeasurableSet S := by
    rw [hSe]
    exact (hD Set.univ MeasurableSet.univ).prod MeasurableSet.univ
  have hω : @Measurable S Omega inferInstance (F a) (fun z => z.val.1.2) := by
    intro A hA
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨(D ×ˢ A) ×ˢ (Set.univ : Set Real), (hD A hA).prod MeasurableSet.univ, ?_⟩
    ext z
    have hz : z.val.1.1 ∈ D := by exact z.property
    simp [hz]
  have hx : Measurable (fun z : S => z.val.2) := measurable_snd.comp measurable_subtype_coe
  have hpair : @Measurable S (Omega × Real) inferInstance
      ((F a).prod inferInstance) (fun z => (z.val.1.2, z.val.2)) := hω.prodMk hx
  apply measurable_of_restrict_of_restrict_compl hS
  · have he : S.domRestrict (fun z => if z.1.1 ∈ D then g (z.1.2, z.2) else 0) =
        fun z : S => g (z.val.1.2, z.val.2) := by
      funext z
      exact if_pos z.property
    rw [he]
    exact hg.comp hpair
  · have he : Sᶜ.domRestrict (fun z => if z.1.1 ∈ D then g (z.1.2, z.2) else 0) =
        fun _ : (Sᶜ : Set ((NNReal × Omega) × Real)) => (0 : ENNReal) := by
      funext z
      exact if_neg z.property
    rw [he]
    exact measurable_const
