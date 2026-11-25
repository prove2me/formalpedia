-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.mem_of_forall_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:59.67657+00:00
-- url     : https://prove2.me/submissions/050c251e-4cf6-4cf9-95b6-d668bf7a5583

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Theorems.Thm_GlobalTheory_HL_PlacesRec_exists_smul_mem
import Theorems.Thm_GlobalTheory_HL_PlacesRec_exists_coeffs
import Theorems.Thm_GlobalTheory_HL_PlacesRec_exists_dual_basis
import Theorems.Thm_GlobalTheory_HL_PlacesRec_functional_integral
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_integers_local
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesRec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}
variable (A : Places F E sig)
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsLattice E Λ)
    (x : Fin n → E) (hx : ∀ p, A.bc p x ∈ A.lat p Λ) : x ∈ Λ := by
  obtain ⟨m, g, φ, hφ⟩ := exists_dual_basis Λ h
  choose c hc using fun i => exists_coeffs Λ h.span_eq_top (φ i)
  have hint : ∀ i, ∃ o : 𝓞 E, (o : E) = ∑ k, c i k * x k := by
    intro i
    refine ((PlacesInt.integers_local A).1 _).1 fun p => ?_
    have := functional_integral A p Λ (c i)
      (fun y hy => ⟨φ i ⟨y, hy⟩, (hc i ⟨y, hy⟩).symm⟩) _ (hx p)
    rw [map_sum]
    simpa [Places.bc] using this
  choose o ho using hint
  obtain ⟨D, hD, hDx⟩ := exists_smul_mem Λ h.span_eq_top x
  have hDE : (D : E) ≠ 0 := by simpa using hD
  have h1 : x = ∑ i, o i • (g i : Fin n → E) := by
    have h2 := congrArg (Subtype.val) (hφ ⟨D • x, hDx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    have h3 : ∀ i, ((φ i ⟨D • x, hDx⟩ : 𝓞 E) : E) = (D : E) * (o i : E) := by
      intro i
      rw [← hc i ⟨D • x, hDx⟩, ho i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, Algebra.smul_def (R := 𝓞 E) (A := E)]
      change _ * ((algebraMap (𝓞 E) E D) * _) = (algebraMap (𝓞 E) E D) * _
      ring
    ext j
    have h4 := congrFun h2 j
    simp only [Pi.smul_apply, Finset.sum_apply, Algebra.smul_def (R := 𝓞 E) (A := E)] at h4 ⊢
    apply mul_left_cancel₀ hDE
    refine Eq.trans h4 ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h5 := h3 i
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E D * algebraMap (𝓞 E) E _ at h5
    rw [h5]
    change _ = algebraMap (𝓞 E) E D * _
    ring
  rw [h1]
  exact Λ.sum_mem fun i _ => Λ.smul_mem _ (g i).2
end GlobalTheory.HL.PlacesRec
