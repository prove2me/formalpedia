-- Prove2me | solution 1 for GlobalTheory.HL.StabFix.eq_one_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:59.399558+00:00
-- url     : https://prove2.me/submissions/33e91b8b-08af-44ba-a544-f160ac94c31b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalCommonStabiliserEqOneOfFixesSecondFrame
import Theorems.Thm_GlobalTheory_HL_StabFix_local_eq_one
import Theorems.Thm_GlobalTheory_HL_StabFix_nonempty_place
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_RatExt_rational_extend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StabFix
namespace GlobalTheory.HL.StabFix
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St,
    (∀ b, x (G.f' b) = G.f' b) → x = 1 := by
  intro F E _ _ _ _ _ sig A r k G x hx hfix
  obtain ⟨p⟩ := nonempty_place F
  have := (A.loc p).lf
  have := (A.loc p).char0
  obtain ⟨x', hx'St, hext⟩ := hx p
  have hloc : ∀ b, x' ((G.S p).f' b) = (G.S p).f' b := by
    intro b
    let u : ((A.loc p).Ep)ˣ := Units.map (algebraMap (A.loc p).Fp (A.loc p).Ep).toMonoidHom (G.c p ^ (r - (b : ℕ)))
    have hu : ((u : (A.loc p).Ep)) = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (b : ℕ))) := by
      simp [u]
    have h1 : x' ((u : (A.loc p).Ep) • (G.S p).f' b) = (u : (A.loc p).Ep) • (G.S p).f' b := by
      rw [hu, G.f'_eq p b, hext, hfix b]
    rw [map_smul] at h1
    have h2 := congrArg (fun v => ((u⁻¹ : ((A.loc p).Ep)ˣ) : (A.loc p).Ep) • v) h1
    simpa [smul_smul] using h2
  have h1 : x' = 1 := local_eq_one (G.S p) x' hx'St hloc
  have hinj := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).1
  refine LinearEquiv.ext fun v => hinj ?_
  rw [← hext v, h1]
  rfl
end GlobalTheory.HL.StabFix
