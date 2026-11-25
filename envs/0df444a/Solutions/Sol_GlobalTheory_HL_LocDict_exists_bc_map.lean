-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.exists_bc_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:43:39.956631+00:00
-- url     : https://prove2.me/submissions/1f9a5fe7-8de5-43d1-b7bb-65da7366dd27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocDict
theorem _root_.solution {m : ℕ} (f : (Fin n → E) →ₗ[E] (Fin m → E)) :
    ∃ g : (Fin n → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (Fin m → (A.loc p).Ep),
      ∀ x, g (A.bc p x) = A.bc p (f x) := by
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' f).map (A.loc p).ιE), fun x => ?_⟩
  funext i
  rw [Matrix.toLin'_apply]
  simp only [Places.bc]
  rw [← LinearMap.toMatrix'_mulVec f x, RingHom.map_mulVec]
  rfl
end GlobalTheory.HL.LocDict
