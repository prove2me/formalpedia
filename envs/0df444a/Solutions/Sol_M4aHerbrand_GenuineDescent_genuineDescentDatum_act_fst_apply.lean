-- Prove2me | solution 1 for M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7c09b12a-6595-5300-9e72-758496a2423a

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_algebraMap_completion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply

set_option autoImplicit false

namespace P2mS26CL

open NumberField NumberField.InfinitePlaceTransport
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem comap_smul_algebraMap (σ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
  rw [InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp]
  congr 1
  exact RingHom.ext fun x => σ.symm.commutes x

theorem transport_algebraMap (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (l : L) :
    transport σ h (algebraMap L w.Completion l) = algebraMap L w'.Completion (σ l) := by
  change transport σ h (((WithAbs.toAbs w.1 l) : WithAbs w.1) : w.Completion) = (((WithAbs.toAbs w'.1 (σ l)) : WithAbs w'.1) : w'.Completion)
  rw [transport_coe]
  rfl

variable [NumberField K] [NumberField L]

theorem conorm_apply_of_comap_eq (a : InfiniteAdeleRing K) (w' : InfinitePlace L) (v : InfinitePlace K)
    (hv : w'.comap (algebraMap K L) = v) :
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm a w' =
      (letI := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq hv; algebraMap v.Completion w'.Completion (a v)) := by
  subst hv
  letI := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq (rfl : w'.comap (algebraMap K L) = w'.comap (algebraMap K L))
  show M4aHerbrand.ArchSemilocal.psiFactor (w'.comap (algebraMap K L)) w' ((a (w'.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
  rw [M4aHerbrand.ArchSemilocal.psiFactor_tmul, map_one, mul_one]

end P2mS26CL

open P2mS26CL in
theorem solution (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers L) L)
    {w w' : NumberField.InfinitePlace L} (h : σ • w = w') :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 w'
      = NumberField.InfinitePlaceTransport.transport σ h (x.1 w) := by
  letI : Algebra (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) :=
    (M4aHerbrand.Bridge.genuineβ K L).toAlgebra

  have hact : ∀ y, (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ y
      = M4aHerbrand.Bridge.genuineTensorEquiv K L
          ((Algebra.TensorProduct.congr AlgEquiv.refl σ) ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm y)) :=
    fun y => rfl
  obtain ⟨z, rfl⟩ := (M4aHerbrand.Bridge.genuineTensorEquiv K L).surjective x
  rw [hact, AlgEquiv.symm_apply_apply]
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    show (0 : w'.Completion) = NumberField.InfinitePlaceTransport.transport σ h 0
    rw [map_zero]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add]
    show ((M4aHerbrand.Bridge.genuineTensorEquiv K L) ((Algebra.TensorProduct.congr AlgEquiv.refl σ) z₁)).1 w'
        + ((M4aHerbrand.Bridge.genuineTensorEquiv K L) ((Algebra.TensorProduct.congr AlgEquiv.refl σ) z₂)).1 w'
      = NumberField.InfinitePlaceTransport.transport σ h
        (((M4aHerbrand.Bridge.genuineTensorEquiv K L) z₁).1 w + ((M4aHerbrand.Bridge.genuineTensorEquiv K L) z₂).1 w)
    rw [h₁, h₂, map_add]
  | tmul a l =>

    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]

    have hte : ∀ m : L, M4aHerbrand.Bridge.genuineTensorEquiv K L (a ⊗ₜ[K] m)
        = M4aHerbrand.Bridge.genuineβ K L a * algebraMap L (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) m := by
      intro m
      rw [← M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one K L a, ← M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul K L m, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    simp only [AlgEquiv.coe_algHom, AlgEquiv.coe_refl, id_eq]
    rw [hte, hte]
    show (M4aHerbrand.Bridge.genuineβ K L a).1 w' * (algebraMap L (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) (σ l)).1 w'
      = NumberField.InfinitePlaceTransport.transport σ h
        ((M4aHerbrand.Bridge.genuineβ K L a).1 w * (algebraMap L (NumberField.AdeleRing (NumberField.RingOfIntegers L) L) l).1 w)
    rw [M4aHerbrand.Bridge.genuineβ_fst, map_mul]
    congr 1
    ·
      have hu : w'.comap (algebraMap K L) = w.comap (algebraMap K L) := by
        rw [← h]; exact comap_smul_algebraMap σ w
      letI i₁ := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq (rfl : w.comap (algebraMap K L) = w.comap (algebraMap K L))
      letI i₂ := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq hu
      rw [conorm_apply_of_comap_eq a.1 w' (w.comap (algebraMap K L)) hu, conorm_apply_of_comap_eq a.1 w (w.comap (algebraMap K L)) rfl]
      exact (NumberField.InfinitePlaceTransport.transport_algebraMap_completion K L σ (w.comap (algebraMap K L)) h _).symm
    ·
      exact (transport_algebraMap σ h l).symm

end S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
end P2MW
export P2MW.S_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply (solution)
