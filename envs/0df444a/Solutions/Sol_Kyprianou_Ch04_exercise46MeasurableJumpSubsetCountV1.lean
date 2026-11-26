-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MeasurableJumpSubsetCountV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:48:48.01388+00:00
-- url     : https://prove2.me/submissions/147bb104-3b1f-4b41-bd39-0df97aef55ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (S : Set (Omega × NNReal)) (hS : MeasurableSet S)
    (hJ : ∀ w t, (w,t) ∈ S → 0 < t ∧
      L.X t w - Function.leftLim (fun u : NNReal => L.X u w) t ≠ 0) :
    Measurable (fun w : Omega => (({t : NNReal | (w,t) ∈ S}).encard : ENNReal)) := by
  obtain ⟨K, hK, hKeq⟩ := avram_wave5_02a_actual_source_intrinsic_sfinite_kernel L
  letI := hK
  let T : Set (Omega × (NNReal × Real)) := {z | (z.1,z.2.1) ∈ S}
  have hT : MeasurableSet T := hS.preimage
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hm := Kernel.measurable_kernel_prodMk_left (κ := K) hT
  have he (w : Omega) : K w (Prod.mk w ⁻¹' T) =
      (({t : NNReal | (w,t) ∈ S}).encard : ENNReal) := by
    rw [hKeq w]
    have hmap : Measurable (fun u : NNReal =>
        (u, L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)) :=
      measurable_id.prodMk ((avram_wave4_04a_actual_levy_jumpmark_joint_measurable L).comp
        (measurable_id.prodMk measurable_const))
    have hsec : MeasurableSet (Prod.mk w ⁻¹' T) := hT.preimage measurable_prodMk_left
    rw [Measure.map_apply hmap hsec, Measure.restrict_apply (hsec.preimage hmap)]
    have hs : MeasurableSet {t : NNReal | (w,t) ∈ S} :=
      hS.preimage measurable_prodMk_left
    rw [show _ ∩ _ = {t : NNReal | (w,t) ∈ S} by
      ext t
      exact ⟨fun ht => ht.1, fun ht => ⟨ht, hJ w t ht⟩⟩]
    exact Measure.count_apply hs
  simpa only [he] using hm
