-- Prove2me | solution 1 for GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:01.642799+00:00
-- url     : https://prove2.me/submissions/3373ed1c-7b59-46b5-be64-c2911e7e198f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionIsometryPrimitiveRootBijectiveModN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsIsometry
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.TorsIsometry
namespace _root_.GlobalTheory.TorsIsometry
theorem _root_.solution {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (hB : Function.Bijective B) (n : ℕ) (d : M) (hd : ∀ b, (n : ℤ) ∣ B d b) : ∃ f : M, d = n • f := by
  let φ : M →ₗ[ℤ] ℤ :=
    { toFun := fun b => B d b / n
      map_add' := fun x y => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hd x)
      map_smul' := fun c x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hd x) }
  obtain ⟨f, hf⟩ := hB.2 φ
  refine ⟨f, hB.1 ?_⟩
  ext b
  simp only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hd b)).symm
end _root_.GlobalTheory.TorsIsometry
end GlobalTheory.TorsIsometry
