-- Prove2me | solution 1 for GlobalTheory.CubeTop.topTerm_res_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:25.04389+00:00
-- url     : https://prove2.me/submissions/55916353-3e7d-422e-a5da-4a513150fb70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
namespace GlobalTheory.CubeTop
theorem _root_.solution (A : Cube.{0} ι R) {p : ℕ} (hn : Fintype.card ι = p + 1) (i : ι)
    (x : A.obj (Finset.univ.erase i)) :
    ∃ y, Cube.d A p y = topTerm A hn (Cube.res A (Finset.erase_subset i _) x) := by
  let y : ∀ s, A.obj s := Pi.single (Finset.univ.erase i) (cubeSign Finset.univ i • x)
  refine ⟨fun s => y s.1, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  rw [Cube.d_apply_eq_totalD A _ y (fun _ => rfl), Cube.totalD_apply, Finset.sum_eq_single i]
  · simp only [y, Pi.single_eq_same, map_zsmul, cubeSign_smul_smul]
    exact (Cube.res_self A _ _).symm
  · intro j _ hji
    have : (Finset.univ.erase j : Finset ι) ≠ Finset.univ.erase i := fun h => by
      have : j ∈ (Finset.univ.erase i : Finset ι) := by simp [hji]
      rw [← h] at this
      simp at this
    simp only [y, Pi.single_eq_of_ne this, map_zero, smul_zero]
  · simp
end GlobalTheory.CubeTop
