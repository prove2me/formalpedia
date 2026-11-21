-- Prove2me | solution 1 for NewtonianLipschitz.cartesianNegativeSafeHalfspace_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:56:33.265341+00:00
-- url     : https://prove2.me/submissions/f52d6fc3-5b1a-4a21-b688-22fd9df5a830

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (i : Fin 3) (d : ℝ) :
    Convex ℝ {z : Vec3 | z i ≤ -d} := by
  change Convex ℝ
    ((LinearMap.proj i : Vec3 →ₗ[ℝ] ℝ) ⁻¹' Set.Iic (-d))
  exact (convex_Iic (-d)).linear_preimage
    (LinearMap.proj i : Vec3 →ₗ[ℝ] ℝ)
end NewtonianLipschitz
