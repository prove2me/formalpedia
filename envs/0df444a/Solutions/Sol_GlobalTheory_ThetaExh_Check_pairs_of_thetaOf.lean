-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.pairs_of_thetaOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:29.714546+00:00
-- url     : https://prove2.me/submissions/ed7f3edc-3cb2-453a-b1e1-f1a0393176a8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (h : thetaOf N A i σ P) :
    Pairs N A i σ P := by
  obtain ⟨hne, hle⟩ := h
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 hy
  refine ⟨f, hf, y, hle hy, ?_⟩
  rw [hfy]
  exact inner_self_ne_zero.2 hy0
end GlobalTheory.ThetaExh.Check
