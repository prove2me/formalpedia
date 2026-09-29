-- Prove2me | solution 1 for JordanCurve.circle_embedding_is_schoenflies_jordan
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T13:16:46.982896+00:00
-- url     : https://prove2.me/submissions/7de5b35d-6b7d-4c5d-bf37-5ed569e995ab

import Definitions.Def_Schoenflies_Jordan
import Theorems.Thm_JordanCurve_euclidean_unit_circle_loop

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    Schoenflies.IsJordanCurve (Set.range γ) := by
  obtain ⟨e, hec, heclose, heinj, herange⟩ :=
    JordanCurve.euclidean_unit_circle_loop
  refine ⟨fun t => γ (e t), ⟨hγ.comp_continuousOn hec,
    congrArg γ heclose, ?_⟩, ?_⟩
  · intro s hs t ht hst
    exact heinj hs ht (hinj hst)
  · change (fun t => γ (e t)) '' Set.Icc (0 : ℝ) 1 = Set.range γ
    rw [← Set.image_image, herange, Set.image_univ]
