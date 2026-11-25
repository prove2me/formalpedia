-- Prove2me | solution 1 for GlobalTheory.HL.GlobalOrbits.lrel_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:01.298812+00:00
-- url     : https://prove2.me/submissions/30fc7a68-28e6-4345-a6c4-0979e758ce67

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameClose_inv_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlobalOrbits
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}
namespace GlobalTheory.HL.GlobalOrbits
theorem _root_.solution (G : GFrames A r k) : Equivalence G.LRel := by
  refine ⟨fun Λ => ⟨1, G.St.one_mem, ?_⟩, ?_, ?_⟩
  · ext x; simp
  · rintro Λ Λ' ⟨g, hg, rfl⟩
    refine ⟨g⁻¹, G.St.inv_mem hg, ?_⟩
    rw [← Submodule.map_comp]
    ext x; simp
  · rintro a b c ⟨g, hg, rfl⟩ ⟨g2, hg2, rfl⟩
    refine ⟨g2 * g, G.St.mul_mem hg2 hg, ?_⟩
    rw [← Submodule.map_comp]
    rfl
end GlobalTheory.HL.GlobalOrbits
