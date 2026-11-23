-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.red_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:04.755302+00:00
-- url     : https://prove2.me/submissions/f781adf3-0d45-4077-bb83-d0adc8356b94

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution (ϖ : R) (k j : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (ϖ ^ (k + j) • x) = 0 := by
  have : red ϖ k (ϖ ^ (k + j) • x) = red ϖ k 0 := by
    rw [red_eq_iff]
    intro i l
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, sub_zero, pow_add]
    exact ⟨ϖ ^ j * x i l, by ring⟩
  rw [this]; ext i l; simp [red]
end GlobalTheory.CompanionTheory.LocalDens
