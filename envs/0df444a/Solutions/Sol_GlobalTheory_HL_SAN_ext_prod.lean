-- Prove2me | solution 1 for GlobalTheory.HL.SAN.ext_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:05.217126+00:00
-- url     : https://prove2.me/submissions/e28ca8fc-255e-41c2-b4b0-ee05e43d36b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SAN
namespace _root_.GlobalTheory.HL.SAN
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ} : ∀ (m : ℕ)
    (a : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (b : Fin m → (Fin N → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin N → (A.loc p).Ep)),
    (∀ i, A.Ext p (a i) (b i)) →
      A.Ext p (List.ofFn a).prod (List.ofFn b).prod := by
  intro m
  induction m with
  | zero =>
    intro a b _
    simp only [_root_.GlobalTheory.HL.Places.Ext]
    intro x
    simp
  | succ m ih =>
    intro a b h
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)
    simp only [_root_.GlobalTheory.HL.Places.Ext] at h ih' ⊢
    intro x
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, ih', h 0]
end _root_.GlobalTheory.HL.SAN
end GlobalTheory.HL.SAN
