-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.exists_dual_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:45:37.580883+00:00
-- url     : https://prove2.me/submissions/1ee91c9c-99a0-4100-b442-bf32d48efa00

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesRec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsLattice E Λ) :
    ∃ (m : ℕ) (g : Fin m → Λ) (φ : Fin m → Λ →ₗ[𝓞 E] 𝓞 E), ∀ y, y = ∑ i, φ i y • g i := by
  haveI := h
  have := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E (Fin n → E)
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 h.fg
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite (𝓞 E) Λ
  have : Module.Flat (𝓞 E) Λ := inferInstance
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨m, fun i => f fun j => if i = j then 1 else 0, fun i => LinearMap.proj i ∘ₗ s, fun y => ?_⟩
  have h1 : f (s y) = y := LinearMap.congr_fun hs y
  conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ f (s y)]
  rfl
end GlobalTheory.HL.PlacesRec
