-- Prove2me | solution 1 for GlobalTheory.CycCoinv.norm_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:34.678908+00:00
-- url     : https://prove2.me/submissions/4f43c26b-4ea8-4c66-9f14-24e828dc9884

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycCoinv
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) : ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  have hu : ‖(χ g : ℚ_[l]) - 1‖ < 1 := by
    rw [hg.2]
    exact zpow_lt_one_of_neg₀ h1 (by have := hj.1; omega)
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (χ g : ℚ_[l]) - 1) (y := 1)
    (by rw [norm_one]; exact hu.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right hu.le] at this
end GlobalTheory.CycCoinv
