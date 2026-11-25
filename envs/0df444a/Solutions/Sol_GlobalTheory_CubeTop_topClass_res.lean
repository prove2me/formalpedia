-- Prove2me | solution 1 for GlobalTheory.CubeTop.topClass_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:55.669741+00:00
-- url     : https://prove2.me/submissions/72615f1e-486b-42a3-9381-0779e7edb1b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Theorems.Thm_GlobalTheory_CubeTop_topTerm_res_mem
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
theorem _root_.solution (A : Cube.{0} ι R) (i : ι) (x : A.obj (Finset.univ.erase i)) :
    topClass A (Cube.res A (Finset.erase_subset i _) x) = 0 := by
  have key : ∀ (n : ℕ) (hn : Fintype.card ι = n), ((cubeComplex A).pOpcycles n).hom
      (topTerm A hn (Cube.res A (Finset.erase_subset i _) x)) = 0 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 :=
      Nat.exists_eq_succ_of_ne_zero (hn ▸ (Fintype.card_pos_iff.2 ⟨i⟩).ne')
    obtain ⟨y, hy⟩ := topTerm_res_mem A hn i x
    have := (cubeComplex A).d_pOpcycles p (p + 1)
    rw [cubeComplex_d] at this
    rw [← hy]
    exact congr(($this).hom y)
  have := key _ rfl
  let g := ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
    (d_top A)).inv.hom
  exact (congrArg g this).trans (map_zero g)
end GlobalTheory.CubeTop
