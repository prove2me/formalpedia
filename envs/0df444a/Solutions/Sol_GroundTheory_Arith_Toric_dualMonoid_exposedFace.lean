-- Prove2me | solution 1 for GroundTheory.Arith.Toric.dualMonoid_exposedFace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:36.001881+00:00
-- url     : https://prove2.me/submissions/7bcd3981-1d7f-4513-b2dd-9d397bb597e7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_anti
import Theorems.Thm_GroundTheory_Arith_Toric_exists_add_smul_mem_dual
import Theorems.Thm_GroundTheory_Arith_Toric_mem_dualMonoid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]
omit [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) {u : Dual ℤ N} (hu : u ∈ dualMonoid σ) :
    dualMonoid (exposedFace σ (toRealDual N u)) = dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [← Finset.coe_image] at hu ⊢
  apply le_antisymm
  · intro m hm
    obtain ⟨p, -, hp⟩ := exists_add_smul_mem_dual (S.image (toRealSpan N))
      (u := toRealDual N u) (w := toRealDual N m) (mem_dualMonoid.1 hu) (mem_dualMonoid.1 hm)
    have hk : p ≤ ((⌈p⌉₊ : ℕ) : ℝ) := Nat.le_ceil p
    rw [AddSubmonoid.mem_sup]
    refine ⟨m + ⌈p⌉₊ • u, mem_dualMonoid.2 fun x hx => ?_, ⌈p⌉₊ • (-u),
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_singleton _)) _,
      by rw [smul_neg, add_neg_cancel_right]⟩
    have := hp _ hk x hx
    rw [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact this
  · refine sup_le (dualMonoid_anti fun x hx => (mem_exposedFace.1 hx).1) ?_
    rw [AddSubmonoid.closure_le, Set.singleton_subset_iff]
    exact mem_dualMonoid.2 fun x hx => by simp [(mem_exposedFace.1 hx).2]
end GroundTheory.Arith.Toric
