-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.submatrix_mul_of_isUpperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:49.380937+00:00
-- url     : https://prove2.me/submissions/551aee5f-251d-470c-b0c8-5b07af0f6a70

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {u M : Matrix (Fin n) (Fin n) F}
    (hu : u.IsUpperTriangular) {m p : ℕ} {r : Fin m → Fin n} (hr : Function.Injective r)
    (hup : ∀ a s, r a ≤ s → ∃ b, r b = s) (c : Fin p → Fin n) :
    (u * M).submatrix r c = u.submatrix r r * M.submatrix r c := by
  classical
  ext a b
  simp only [submatrix_apply, mul_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := r) (fun x _ y _ h => hr h)
    (f := fun s => u (r a) s * M s (c b))]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => ?_
  have hlt : s < r a := by
    by_contra h
    obtain ⟨b', rfl⟩ := hup a s (not_lt.1 h)
    exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rw [hu (show id s < id (r a) from hlt), zero_mul]
end GroundTheory.Automorphic.Whittaker
