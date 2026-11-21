-- Prove2me | solution 1 for NewtonianLipschitz.cartesianPositiveSafeHalfspace_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:59.828269+00:00
-- url     : https://prove2.me/submissions/6b0611b9-6162-4a52-a7e6-6a791904e133

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (i : Fin 3) (d : ℝ) :
    Convex ℝ {z : Vec3 | d ≤ z i} := by
  change Convex ℝ
    ((LinearMap.proj i : Vec3 →ₗ[ℝ] ℝ) ⁻¹' Set.Ici d)
  exact (convex_Ici d).linear_preimage
    (LinearMap.proj i : Vec3 →ₗ[ℝ] ℝ)
end NewtonianLipschitz
