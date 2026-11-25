-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.det_mem_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:13.039196+00:00
-- url     : https://prove2.me/submissions/59af3852-dd6d-4c54-9d2b-0bbf7a6afa69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (hM : ∀ i j, M i j ∈ 𝒪[F]) :
    M.det ∈ 𝒪[F] := by
  let N : Matrix (Fin m) (Fin m) 𝒪[F] := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have : M = N.map (𝒪[F]).subtype := by
    ext i j
    rfl
  have h := RingHom.map_det (𝒪[F]).subtype N
  rw [RingHom.mapMatrix_apply] at h
  rw [this, ← h]
  exact (N.det).2
end GroundTheory.Automorphic.Spherical
