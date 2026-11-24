-- Prove2me | solution 1 for GlobalTheory.spanCovol_eq_sqrt_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:36.634668+00:00
-- url     : https://prove2.me/submissions/772e459e-628e-4808-82c0-613795cc632b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_sqrt_det_gram_eq_relIndex_mul
import Theorems.Thm_GlobalTheory_Hadamard_det_gram_comp_equiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {L : Submodule ℤ E} (b : Basis ι ℤ L) :
    spanCovol L = √(gram ℝ fun i => (b i : E)).det := by
  have hf : Module.Finite ℤ L := .of_basis b
  have hfg : L.FG := Module.Finite.iff_fg.1 hf
  have : Module.Free ℤ L := .of_basis b
  let e := (finBasis ℤ L).indexEquiv b
  rw [spanCovol, dif_pos hfg, sqrt_det_gram_eq_relIndex_mul le_rfl b ((finBasis ℤ L).reindex e),
    AddSubgroup.relIndex_self, Nat.cast_one, one_mul, ← Hadamard.det_gram_comp_equiv _ e]
  congr 3
  ext i
  simp
end GlobalTheory
