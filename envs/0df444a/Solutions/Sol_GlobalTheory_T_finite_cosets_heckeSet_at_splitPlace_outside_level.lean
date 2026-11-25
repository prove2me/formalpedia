-- Prove2me | solution 1 for GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:00.926362+00:00
-- url     : https://prove2.me/submissions/a3fb51fa-3c32-4f98-837e-275b98c4cc19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Theorems.Thm_GlobalTheory_TSetFin_finite_image_tSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFin.finite_image_tSet | exact GlobalTheory.TSetFin.finite_image_tSet | (intros; apply GlobalTheory.TSetFin.finite_image_tSet <;> assumption)
end _root_.GlobalTheory.T
