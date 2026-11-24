-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.isUnit_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:37.31084+00:00
-- url     : https://prove2.me/submissions/c1d59a07-a890-40c0-a2f4-d3aef675e8e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) {g : Matrix (Fin n) (Fin n) O}
    (hdet : IsUnit g.det) (hg : Shape α β g) (i : Fin n) : IsUnit (g i i) := by
  let f := IsLocalRing.residue O
  have h0 : ∀ x, f x = 0 ↔ ¬ IsUnit x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h1 : (g.map f).BlockTriangular id := fun i j h =>
    (h0 _).2 fun hu => hβ (isUnit_of_dvd_unit ((hg i j).2 h) hu)
  have h2 : f g.det = ∏ k, f (g k k) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular h1]
    rfl
  by_contra hi
  have h3 : f g.det = 0 := by
    rw [h2]; exact Finset.prod_eq_zero (Finset.mem_univ i) ((h0 _).2 hi)
  exact (h0 _).1 h3 hdet
end GlobalTheory.IwahoriFactor
