-- Prove2me | solution 1 for GlobalTheory.HL.LatClose.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:43.546866+00:00
-- url     : https://prove2.me/submissions/a0f95795-d464-4b80-9ac9-4a69a42395ad

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CloseOnCompletedLatticeOfCloseOnFrames
import Theorems.Thm_GlobalTheory_HL_LatClose_bc_smul
import Theorems.Thm_GlobalTheory_HL_LatClose_bc_mem_lat
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatClose
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.LatClose
theorem _root_.solution (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (D : ℤ) (h : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (g : Fin m → Fin n → E) (Mx : Matrix (Fin m) (Fin m) (A.loc p).Ep) (t : (A.loc p).Fp)
    (hg : ∀ j, h (A.bc p (g j)) = ∑ i, Mx i j • A.bc p (g i))
    (hMx : ∀ i j, ∃ o ∈ (A.L p).O, (Mx - 1) i j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o)
    (hgΛ : ∀ i, (D : 𝓞 E) • g i ∈ Λ) (a : E) (ha : ∃ o : 𝓞 E, (D : E) ^ 2 * a = o) (j : Fin m) :
    ∃ z ∈ A.lat p Λ, (A.loc p).ιE a • (h (A.bc p (g j)) - A.bc p (g j)) =
      algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
  obtain ⟨oa, hoa⟩ := ha
  choose o ho hoeq using hMx
  have hdiff : h (A.bc p (g j)) - A.bc p (g j) = ∑ i, (Mx - 1) i j • A.bc p (g i) := by
    rw [hg]
    simp [Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib]
  refine ⟨∑ i, (⟨o i j, ho i j⟩ : (A.L p).O) • A.bc p (oa • ((D : 𝓞 E) • g i)),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bc_mem_lat A p Λ (Λ.smul_mem _ (hgΛ i))), ?_⟩
  rw [hdiff, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (oa • ((D : 𝓞 E) • g i) : Fin n → E) = ((D : E) ^ 3 * a) • g i := by
    change (oa : E) • (((D : 𝓞 E) : E) • g i) = _
    have hD : ((D : 𝓞 E) : E) = (D : E) := by simp
    rw [smul_smul, ← hoa, hD]
    congr 1
    ring
  rw [Subring.smul_def, e1, bc_smul, hoeq, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, map_pow, map_intCast]
  ring
end GlobalTheory.HL.LatClose
