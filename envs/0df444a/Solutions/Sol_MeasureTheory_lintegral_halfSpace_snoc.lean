-- Prove2me | solution 1 for MeasureTheory.lintegral_halfSpace_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:51:15.137077+00:00
-- url     : https://prove2.me/submissions/4541df24-3a20-4440-82b2-b4ffc73c0fbb

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Set HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem solution {m : ℕ} (F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞)
    (hF : AEMeasurable F (volume.restrict (upperHalfSpace m))) :
    (∫⁻ x, F x ∂volume.restrict (upperHalfSpace m)) =
      ∫⁻ x' : EuclideanSpace ℝ (Fin m), ∫⁻ t in Ioi (0 : ℝ),
        F (WithLp.toLp 2 (Fin.snoc (fun i => x' i) t)) := by
  let e : EuclideanSpace ℝ (Fin (m + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin m) :=
    ((MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m))).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.toLp 2 (Fin m → ℝ)))
  have he : MeasurePreserving e volume (volume.prod volume) :=
    ((PiLp.volume_preserving_ofLp (Fin (m + 1))).trans
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m))).trans
        ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m)))
  have hval (t : ℝ) (x' : EuclideanSpace ℝ (Fin m)) :
      e.symm (t, x') = WithLp.toLp 2 (Fin.snoc (fun i => x' i) t) := by
    change WithLp.toLp 2 ((Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ)
      (Fin.last m)) (t, WithLp.ofLp x')) = _
    simp [Fin.insertNthEquiv, Fin.insertNth_last']
  have hpre : e.symm ⁻¹' upperHalfSpace m = Ioi (0 : ℝ) ×ˢ univ := by
    ext p
    simp [hval, upperHalfSpace]
  rw [← he.symm.setLIntegral_comp_preimage_emb e.symm.measurableEmbedding F,
    hpre]
  have hm : AEMeasurable (F ∘ e.symm)
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m))))) := by
    apply hF.comp_quasiMeasurePreserving
    apply he.symm.quasiMeasurePreserving.restrict
    intro p hp
    exact congrArg (fun s => p ∈ s) hpre ▸ hp
  rw [setLIntegral_prod_symm (fun p => F (e.symm p)) hm]
  simp only [Measure.restrict_univ, hval]
