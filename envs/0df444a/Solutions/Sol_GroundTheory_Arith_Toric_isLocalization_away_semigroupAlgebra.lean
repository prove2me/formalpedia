-- Prove2me | solution 1 for GroundTheory.Arith.Toric.isLocalization_away_semigroupAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:33.389036+00:00
-- url     : https://prove2.me/submissions/41f221ff-831a-47d4-81d6-458b5df45c04

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {S T : AddSubmonoid G} (h : S ≤ T) {u : G}
    (hu : u ∈ S) (hu' : -u ∈ T) (hT : ∀ m ∈ T, ∃ j : ℕ, m + j • u ∈ S) :
    letI := semigroupAlgebraAlgebra (k := k) h
    IsLocalization.Away (⟨single u 1, single_mem_semigroupAlgebra hu 1⟩ : semigroupAlgebra k S)
      (semigroupAlgebra k T) := by
  let := semigroupAlgebraAlgebra (k := k) h
  classical
  have hmap : ∀ x : semigroupAlgebra k S,
      ((algebraMap (semigroupAlgebra k S) (semigroupAlgebra k T) x : semigroupAlgebra k T) :
        AddMonoidAlgebra k G) = x := fun _ => rfl
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    have e1 : single u (1 : k) * single (-u) 1 = 1 := by
      rw [single_mul_single, add_neg_cancel, one_mul, ← AddMonoidAlgebra.one_def]
    have hunit : IsUnit (algebraMap (semigroupAlgebra k S) (semigroupAlgebra k T)
        ⟨single u 1, single_mem_semigroupAlgebra hu 1⟩) :=
      isUnit_iff_exists_inv.2 ⟨⟨single (-u) 1, single_mem_semigroupAlgebra hu' 1⟩, Subtype.ext e1⟩
    rw [map_pow]
    exact hunit.pow n
  · intro z
    have hz : ∀ m ∈ (z : AddMonoidAlgebra k G).coeff.support, ∃ j : ℕ, m + j • u ∈ S :=
      fun m hm => hT m (z.2 hm)
    choose! f hf using hz
    set n := (z : AddMonoidAlgebra k G).coeff.support.sup f
    have hmem : single (n • u) 1 * (z : AddMonoidAlgebra k G) ∈ semigroupAlgebra k S := by
      rw [mem_semigroupAlgebra]
      intro m hm
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1
        (support_coeff_single_mul_subset (z : AddMonoidAlgebra k G) 1 (n • u) hm)
      have hle : f m' ≤ n := Finset.le_sup hm'
      have : n • u + m' = (m' + f m' • u) + (n - f m') • u := by
        rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hle, add_comm]
      rw [this]
      exact S.add_mem (hf m' hm') (S.nsmul_mem hu _)
    refine ⟨(⟨_, hmem⟩, ⟨_, n, rfl⟩), ?_⟩
    apply Subtype.ext
    simp only [map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap, single_pow, one_pow]
    rw [mul_comm]
  · intro x y hxy
    have hxy' : x = y := Subtype.ext (by
      have := congrArg (fun z : semigroupAlgebra k T => (z : AddMonoidAlgebra k G)) hxy
      simpa only [hmap] using this)
    exact ⟨1, by rw [hxy']⟩
end GroundTheory.Arith.Toric
