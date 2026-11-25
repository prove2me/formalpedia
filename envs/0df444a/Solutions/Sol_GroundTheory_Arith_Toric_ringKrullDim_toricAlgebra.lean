-- Prove2me | solution 1 for GroundTheory.Arith.Toric.ringKrullDim_toricAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:29.957371+00:00
-- url     : https://prove2.me/submissions/f34baff0-4483-48a5-b525-022c0dd05f74

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_eq_of_isIntegral
import Theorems.Thm_GroundTheory_Arith_Toric_trdeg_semigroupAlgebra_eq_top
import Theorems.Thm_GroundTheory_Arith_Toric_trdeg_semigroupAlgebra_top
import Theorems.Thm_GroundTheory_Arith_Toric_bot_isFaceOf_iff
import Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_exposedFace
import Theorems.Thm_GroundTheory_Arith_Toric_exists_mem_dualMonoid_eq_exposedFace
import Theorems.Thm_GroundTheory_Arith_Toric_finiteType_toricAlgebra
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
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hs : (σ : ConvexCone ℝ (ℝ ⊗[ℤ] N)).Salient) :
    ringKrullDim (toricAlgebra k σ) = Module.finrank ℤ N := by
  have hfin := finiteType_toricAlgebra (k := k) hσ
  obtain ⟨u, hu, hτu⟩ := exists_mem_dualMonoid_eq_exposedFace hσ (bot_isFaceOf_iff.2 hs)
  have hbot : dualMonoid (⊥ : PointedCone ℝ (ℝ ⊗[ℤ] N)) = ⊤ :=
    eq_top_iff.2 fun m _ => mem_dualMonoid.2 fun x hx => by
      rw [(Submodule.mem_bot _).1 hx, map_zero]
  have hT : ∀ m : Dual ℤ N, ∃ j : ℕ, m + j • u ∈ dualMonoid σ := by
    intro m
    have hm : m ∈ dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by
      rw [← dualMonoid_exposedFace hσ hu, ← hτu, hbot]
      exact AddSubmonoid.mem_top m
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubmonoid.mem_sup.1 hm
    obtain ⟨j, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hz
    exact ⟨j, by rwa [add_assoc, smul_neg, neg_add_cancel, add_zero]⟩
  have hrank : Module.finrank ℤ (Dual ℤ N) = Module.finrank ℤ N :=
    (Module.finBasis ℤ N).toDualEquiv.finrank_eq.symm
  have htr : trdeg k (toricAlgebra k σ) = Module.finrank ℤ N := by
    rw [trdeg_semigroupAlgebra_eq_top hu hT, trdeg_semigroupAlgebra_top, hrank]
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg k (toricAlgebra k σ)
  let := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (toricAlgebra k σ) := ⟨fun x => hgint x⟩
  have hdim : ringKrullDim (toricAlgebra k σ) = s := by
    rw [ringKrullDim_eq_of_isIntegral hginj, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
  have : IsScalarTower k (MvPolynomial (Fin s) k) (toricAlgebra k σ) :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (toricAlgebra k σ) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hginj
  have h0 : trdeg (MvPolynomial (Fin s) k) (toricAlgebra k σ) = 0 := trdeg_eq_zero
  have hsum := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := toricAlgebra k σ)
  rw [h0, add_zero, MvPolynomial.trdeg_of_isDomain, htr, Cardinal.mk_fin,
    Cardinal.lift_natCast] at hsum
  have hsn : s = Module.finrank ℤ N := by exact_mod_cast hsum
  rw [hdim, hsn]
end GroundTheory.Arith.Toric
