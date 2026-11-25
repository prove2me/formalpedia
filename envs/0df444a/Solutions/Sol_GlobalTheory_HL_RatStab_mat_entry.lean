-- Prove2me | solution 1 for GlobalTheory.HL.RatStab.mat_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:55:30.870564+00:00
-- url     : https://prove2.me/submissions/eddafa50-87c0-41b7-ae63-118cbc9bae82

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
import Theorems.Thm_GlobalTheory_HL_RatStab_cj_sc
import Theorems.Thm_GlobalTheory_HL_RatStab_cj_sci
import Theorems.Thm_P2M_GlobalTheory_HL_RatStab_cj___036ff7d21889
import Theorems.Thm_GlobalTheory_HL_RatStab_Zh_scale
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
  {sig : E →ₐ[F] E}
variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.RatStab
theorem _root_.solution (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    (cT (A.L p) (locM G p s) * (G.S p).Zh * locM G p s') a b =
      sc G p a * sc G p b * (A.loc p).ιE (((s.map sig).transpose * G.Zh * s') a b) := by
  simp only [Matrix.mul_apply, cT, locM, Matrix.of_apply, Zh_scale, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, cj_sc, cj_sci, cj_ι, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  have h1 := sc_mul_sci G p i
  have h2 := sc_mul_sci G p l
  set X := (A.loc p).ιE (sig (s i a)) * (A.loc p).ιE (G.Zh i l) * (A.loc p).ιE (s' l b)
  linear_combination (sc G p a * sc G p b * X * sc G p l * sci G p l) * h1 + (sc G p a * sc G p b * X) * h2
end GlobalTheory.HL.RatStab
