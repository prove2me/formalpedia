-- Prove2me | solution 1 for GlobalTheory.HL.RatStab.mat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:56.978913+00:00
-- url     : https://prove2.me/submissions/15c26b5c-9696-446a-8bfe-5bce299f3888

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
import Theorems.Thm_GlobalTheory_HL_RatStab_Zh_scale
import Theorems.Thm_GlobalTheory_HL_RatStab_mat_entry

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatStab
open GlobalTheory.HL.FrameStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.RatStab
theorem _root_.solution (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cT (A.L p) (locM G p s) * (G.S p).Zh * locM G p s' = (G.S p).Zh ↔
      (s.map sig).transpose * G.Zh * s' = G.Zh := by
  constructor
  · intro h
    ext a b
    have h1 := congrFun (congrFun h a) b
    rw [mat_entry, Zh_scale] at h1
    haveI : Nontrivial (A.loc p).Ep :=
      Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
    apply (A.loc p).ιE.injective
    have hu := sc_mul_sci G p a
    have hv := sc_mul_sci G p b
    set D := (A.loc p).ιE (((s.map sig).transpose * G.Zh * s') a b) - (A.loc p).ιE (G.Zh a b)
    linear_combination (sci G p a * sci G p b) * h1 - (D * sc G p b * sci G p b) * hu - D * hv
  · intro h
    ext a b
    rw [mat_entry, h, Zh_scale]
    ring
end GlobalTheory.HL.RatStab
