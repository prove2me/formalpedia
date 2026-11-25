-- Prove2me | solution 1 for GlobalTheory.HL.PhaseProduct.psiOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:51.769912+00:00
-- url     : https://prove2.me/submissions/a7d6501c-480f-4685-9de5-ee3f8625b301

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinprodPsiEEqExpTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PsiOfEq
import Theorems.Thm_GlobalTheory_HL_PhaseProduct_coef_eq
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
    (δ : ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹)))
    (h2 : (G.c p : (A.loc p).Fp) * g = δ * (G.S p).th)
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) :
    (G.S p).psiOf sf se m = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) / g))) := by
  have hth : (G.S p).th ≠ 0 := by
    unfold Frames.th
    split_ifs
    · exact fun h => (G.S p).ϖ_irr.ne_zero (Subtype.ext h)
    · exact one_ne_zero
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  set X : E := ∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j) with hX
  have hXg : (A.loc p).ιE X = (A.loc p).ιE (X / g) * algebraMap (A.loc p).Fp (A.loc p).Ep (g : (A.loc p).Fp) := by
    rw [map_natCast, ← map_natCast (A.loc p).ιE g, ← map_mul, div_mul_cancel₀ _ hgE]
  have hsc : (G.S p).th⁻¹ * ((G.c p : (A.loc p).Fp) * g) * (δ : (A.loc p).Fp)⁻¹ = 1 := by
    rw [h2]
    field_simp
  have hsum : ∑ j, (G.S p).coef sf se m j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X := by
    rw [hX, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => coef_eq A G p n m hx sf se f es hsf hse a
  have harg : algebraMap (A.loc p).Fp (A.loc p).Ep (G.S p).th⁻¹ *
      (algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X) *
      algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹ = (A.loc p).ιE (X / g) := by
    have h3 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) hsc
    simp only [map_mul, map_one] at h3
    rw [hXg]
    linear_combination ((A.loc p).ιE (X / g)) * h3
  unfold Frames.psiOf
  rw [hsum, h1, harg, map_neg (A.loc p).ιE]
end GlobalTheory.HL.PhaseProduct
