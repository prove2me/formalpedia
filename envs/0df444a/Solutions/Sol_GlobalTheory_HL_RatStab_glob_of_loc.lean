-- Prove2me | solution 1 for GlobalTheory.HL.RatStab.glob_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:43.243811+00:00
-- url     : https://prove2.me/submissions/ad0346d6-6ab2-451c-823e-737aaac13703

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairs
import Theorems.Thm_GlobalTheory_HL_RatStab_sc_mul_sci
import Theorems.Thm_GlobalTheory_HL_RatStab_bc_sum
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.RatStab
theorem _root_.solution (u : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (v : Fin (r + 1) → G.V)
    (hu : ∀ a, u a = sc G p a • A.bc p (v a)) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep))
    (hl : ∀ j, h' (u j) = ∑ i, locM G p s i j • u i) (j : Fin (r + 1)) :
    h' (A.bc p (v j)) = A.bc p (∑ i, s i j • v i) := by
  have hb : ∀ a, A.bc p (v a) = sci G p a • u a := fun a => by
    rw [hu a, smul_smul, mul_comm (sci G p a), sc_mul_sci, one_smul]
  rw [hb j, map_smul, hl j, bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb i, smul_smul, smul_smul]
  congr 1
  simp only [locM, Matrix.of_apply]
  linear_combination (sci G p i * (A.loc p).ιE (s i j)) * sc_mul_sci G p j
end GlobalTheory.HL.RatStab
