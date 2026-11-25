-- Prove2me | solution 1 for GlobalTheory.HL.GlobalOrbits.drel_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:33.585369+00:00
-- url     : https://prove2.me/submissions/9096ff2b-fe76-473f-a0e0-2559d95a7a96

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUniqueGlobalLatticeOfLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproxStabStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesTermsOrbitsLocal
import Theorems.Thm_GlobalTheory_HL_FrameClose_inv_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlobalOrbits
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}
namespace GlobalTheory.HL.GlobalOrbits
theorem _root_.solution (G : GFrames A r k) : Equivalence G.DRel := by
  refine ⟨fun d => ⟨1, fun p => ⟨1, (G.S p).H0.one_mem, fun _ => rfl, one_smul _ _⟩⟩, ?_, ?_⟩
  · rintro d d' ⟨g, hg⟩
    refine ⟨g⁻¹, fun p => ?_⟩
    obtain ⟨g', h0, he, hd⟩ := hg p
    refine ⟨g'⁻¹, (G.S p).H0.inv_mem h0, fun x => ?_, ?_⟩
    · have h := he (g.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      change g'.symm (A.bc p x) = A.bc p (g.symm x)
      rw [← h, LinearEquiv.symm_apply_apply]
    · rw [← hd, inv_smul_smul]
  · rintro a b c ⟨g, hg⟩ ⟨g2, hg2⟩
    refine ⟨g2 * g, fun p => ?_⟩
    obtain ⟨g', h0, he, hd⟩ := hg p
    obtain ⟨g2', h20, he2, hd2⟩ := hg2 p
    refine ⟨g2' * g', (G.S p).H0.mul_mem h20 h0, fun x => ?_, ?_⟩
    · change g2' (g' (A.bc p x)) = A.bc p (g2 (g x))
      rw [he x, he2 (g x)]
    · rw [mul_smul, hd, hd2]
end GlobalTheory.HL.GlobalOrbits
