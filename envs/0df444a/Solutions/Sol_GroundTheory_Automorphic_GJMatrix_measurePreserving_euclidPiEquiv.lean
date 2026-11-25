-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.measurePreserving_euclidPiEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:24.128805+00:00
-- url     : https://prove2.me/submissions/0d28eb85-14e5-426d-8bef-a6e963755805

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_curry_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution :
    MeasurePreserving (euclidPiEquiv K (ι := ι))
      (Measure.pi fun _ : ι ↦ (volume : Measure (euclidean.mixedSpace K))) volume := by
  set b := stdOrthonormalBasis ℝ (euclidean.mixedSpace K)
  have h1 : MeasurePreserving
      (fun (u : ι → euclidean.mixedSpace K) (i : ι) ↦ WithLp.ofLp (b.repr (u i)))
      (Measure.pi fun _ : ι ↦ (volume : Measure (euclidean.mixedSpace K)))
      (Measure.pi fun _ : ι ↦
        (volume : Measure (Fin (finrank ℝ (euclidean.mixedSpace K)) → ℝ))) :=
    measurePreserving_pi _ _ fun _ ↦ (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have h2 := measurePreserving_curry_symm (α := ι) (κ := Fin (finrank ℝ (euclidean.mixedSpace K)))
    (volume : Measure ℝ)
  have h3 := PiLp.volume_preserving_toLp (ι × Fin (finrank ℝ (euclidean.mixedSpace K)))
  have h : ⇑(euclidPiEquiv K (ι := ι)) =
      WithLp.toLp 2 ∘ (MeasurableEquiv.curry ι (Fin (finrank ℝ (euclidean.mixedSpace K))) ℝ).symm ∘
        fun (u : ι → euclidean.mixedSpace K) (i : ι) ↦ WithLp.ofLp (b.repr (u i)) := rfl
  rw [h]
  exact h3.comp (h2.comp h1)
end GroundTheory.Automorphic.GJMatrix
