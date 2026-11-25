-- Prove2me | solution 1 for GlobalTheory.HL.RatExt.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:40:01.009232+00:00
-- url     : https://prove2.me/submissions/f28db8a7-a710-4480-a69a-3e85eb204ac8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatExt
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)
namespace GlobalTheory.HL.RatExt
namespace _root_.GlobalTheory.HL.RatExt
theorem _root_.solution {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    ∃ g' : (Fin n → R) ≃ₗ[R] (Fin n → R), ∀ x, g' (fun i => ι (x i)) = fun i => ι (g x i) := by
  set M := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  set N := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hMN : M * N = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hNM : N * M = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  refine ⟨LinearEquiv.ofLinear (Matrix.toLin' (M.map ι)) (Matrix.toLin' (N.map ι)) ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · intro x
    funext i
    simp only [LinearEquiv.ofLinear_apply, Matrix.toLin'_apply]
    have h := LinearMap.toMatrix'_mulVec (g : (Fin n → E) →ₗ[E] (Fin n → E)) x
    rw [show g x = M.mulVec x from h.symm, RingHom.map_mulVec]
    rfl
end _root_.GlobalTheory.HL.RatExt
end GlobalTheory.HL.RatExt
