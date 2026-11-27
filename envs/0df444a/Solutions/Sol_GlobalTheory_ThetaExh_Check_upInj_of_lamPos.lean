-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.upInj_of_lamPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:42.193796+00:00
-- url     : https://prove2.me/submissions/a0cf574a-af09-46b5-8299-531216c121e8

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
theorem _root_.solution (i : N.Loc) (h : LamPos N i) : UpInj N i := by
  intro σ f hf h0
  obtain ⟨hscal, hpos⟩ := h σ
  have key := hscal f hf
  rw [h0, map_zero] at key
  by_cases hb : what₂.isot (N.j i) σ = ⊥
  · rw [hb] at hf
    exact (Submodule.mem_bot ℂ).1 hf
  · have hne : ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (hpos hb).ne'
    exact (smul_eq_zero.1 key.symm).resolve_left hne
end GlobalTheory.ThetaExh.Check
