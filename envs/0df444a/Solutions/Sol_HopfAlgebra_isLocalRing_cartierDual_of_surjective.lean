-- Prove2me | solution 1 for HopfAlgebra.isLocalRing_cartierDual_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b83b4064-e40f-563b-8ed5-6fcc31ff864c

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isLocalRing_cartierDual_of_surjective

set_option autoImplicit false

namespace UnipotentSubgroup

variable {k : Type*} [Field k]
  {A : Type*} [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
  {B : Type*} [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]

lemma nontrivial_of_bialgebra (K : Type*) [Field K] (C : Type*) [CommRing C] [Bialgebra K C] :
    Nontrivial C :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := K)
    (by simpa using congrArg (Coalgebra.counit (R := K) (A := C)) h)⟩⟩

theorem isLocalRing_of_surjective (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hA : IsLocalRing (CartierDual k A)) : IsLocalRing (CartierDual k B) := by
  haveI := hA
  haveI : Nontrivial B := nontrivial_of_bialgebra k B
  haveI : Nontrivial (CartierDual k B) := ⟨⟨0, 1, fun h => by
    have h1 := congrArg (fun χ : CartierDual k B => χ 1) h
    simp only [CartierDual.one_apply, Bialgebra.counit_one] at h1
    exact zero_ne_one h1⟩⟩
  let ι : CartierDual k B →ₐ[k] CartierDual k A := CartierDual.mapAlgHom π
  have hι : Function.Injective ι := by
    intro φ ψ h
    apply CartierDual.ext
    intro b
    obtain ⟨a, rfl⟩ := hπ b
    have := congrArg (fun χ : CartierDual k A => χ a) h
    simpa [ι, CartierDual.mapAlgHom_apply] using this

  have key : ∀ φ : CartierDual k B,
      ¬ IsUnit φ ↔ ι φ ∈ IsLocalRing.maximalIdeal (CartierDual k A) := by
    intro φ
    constructor
    · intro hφ
      by_contra hmem
      have hu : IsUnit (ι φ) := by
        by_contra hnu
        exact hmem ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu))

      have hinj : Function.Injective (LinearMap.mulLeft k φ) := by
        intro x y hxy
        have h1 : φ * x = φ * y := hxy
        have h2 : ι φ * ι x = ι φ * ι y := by rw [← map_mul, ← map_mul, h1]
        exact hι (hu.mul_left_cancel h2)
      have hsurj : Function.Surjective (LinearMap.mulLeft k φ) :=
        LinearMap.surjective_of_injective hinj
      obtain ⟨x, hx⟩ := hsurj 1
      exact hφ (isUnit_iff_exists_inv.2 ⟨x, hx⟩)
    · intro hmem hu
      exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem) (hu.map ι)
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, key] at ha hb ⊢
  rw [map_add]
  exact Ideal.add_mem _ ha hb

end UnipotentSubgroup

universe u v w

theorem solution
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (B : Type w) [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π) (hA : IsLocalRing (CartierDual k A)) :
    IsLocalRing (CartierDual k B) :=
  UnipotentSubgroup.isLocalRing_of_surjective π hπ hA

end S_HopfAlgebra_isLocalRing_cartierDual_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_isLocalRing_cartierDual_of_surjective (solution)
