-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.exists_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:10.747525+00:00
-- url     : https://prove2.me/submissions/16e92d66-4d8d-42c0-bd4d-063494dda348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Formalism.UG
open GlobalTheory GlobalTheory.WittTransitivity
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
namespace GlobalTheory.WittTransitivity
theorem _root_.solution (hdet : IsUnit J.det) (g : Matrix (Fin M) (Fin M) A)
    (hg : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z) :
    ∃ G ∈ UJ c J, (G : Matrix (Fin M) (Fin M) A) = g := by
  have hsingle : ∀ k l, hform c J (Pi.single k 1) (Pi.single l 1) = J k l := by
    intro k l
    simp [Formalism.UG.hform, Pi.single_apply, apply_ite c]
  have hcol : ∀ k, g *ᵥ Pi.single k 1 = fun i => g i k := by
    intro k
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : (g.map c)ᵀ * J * g = J := by
    ext k l
    have h1 := hg (Pi.single k 1) (Pi.single l 1)
    rw [hcol, hcol, hsingle] at h1
    rw [← h1]
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  have hdg : IsUnit g.det := by
    have h2 := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have h3 : J.det * ((g.map c)ᵀ.det * g.det) = J.det * 1 := by
      linear_combination h2
    have h4 := hdet.mul_left_cancel h3
    exact isUnit_of_mul_isUnit_right (by rw [h4]; exact isUnit_one)
  refine ⟨Matrix.nonsingInvUnit g hdg, ?_, rfl⟩
  simp only [Formalism.UG.UJ, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Formalism.UG.cT]
  exact key
end GlobalTheory.WittTransitivity
