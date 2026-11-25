-- Prove2me | solution 1 for GlobalTheory.HL.PhaseProduct.coef_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:47.220974+00:00
-- url     : https://prove2.me/submissions/52e2913d-188b-4971-955a-8994b4fe72c6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinprodPsiEEqExpTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PsiOfEq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PhaseProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.PhaseProduct
theorem _root_.solution (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) (a : Fin r) :
    (G.S p).coef sf se m a = algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) *
      (A.loc p).ιE (∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) := by
  have hexp : r - (a : ℕ) = (r - ((a.succ : Fin (r + 1)) : ℕ)) + 1 := by
    have := a.isLt
    simp only [Fin.val_succ]
    omega
  set t := algebraMap (A.loc p).Fp (A.loc p).Ep
    ((G.c p : (A.loc p).Fp) ^ (r - ((a.succ : Fin (r + 1)) : ℕ))) with ht
  set u := algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) with hu
  have key : ∀ i, t * m (sf a.succ) i = (A.loc p).ιE (n (f a.succ) i) := by
    intro i
    have h1 := congrArg m (hsf a.succ)
    rw [map_smul, hx] at h1
    exact congrFun h1 i
  have hcj : ∀ j, (A.L p).cj (se a j) = t * u * (A.loc p).ιE (sig (es a j)) := by
    intro j
    rw [A.L_cj p, hse a]
    change (A.loc p).cj (algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) * (A.loc p).ιE (es a j)) = _
    rw [map_mul, AlgEquiv.commutes, (A.loc p).cj_ιE, hexp, pow_succ, map_mul]
  simp only [Frames.coef, Frames.h, hf, map_sum, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcj j, (G.Hm_eq p), Matrix.map_apply]
  linear_combination (u * (A.loc p).ιE (G.Hm i j) * (A.loc p).ιE (sig (es a j))) * key i
end GlobalTheory.HL.PhaseProduct
