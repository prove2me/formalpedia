-- Prove2me | solution 1 for GlobalTheory.HL.PlacesRec.functional_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:01.067805+00:00
-- url     : https://prove2.me/submissions/4a454d5e-e9a9-4939-957d-b8b794c643ee

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesRec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {n : ℕ}
variable (A : Places F E sig)
namespace GlobalTheory.HL.PlacesRec
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (c : Fin n → E) (hc : ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = ∑ k, c k * y k)
    (z : Fin n → (A.loc p).Ep) (hz : z ∈ A.lat p Λ) :
    ∑ k, (A.loc p).ιE (c k) * z k ∈ (A.L p).O := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨o, ho⟩ := hc y hy
    have : ∑ k, (A.loc p).ιE (c k) * A.bc p y k = (A.loc p).ιE (o : E) := by
      rw [ho, map_sum]
      simp [Places.bc]
    rw [this]
    exact int_mem A p o
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem ha hb
  | smul o a _ ha =>
    have : ∑ k, (A.loc p).ιE (c k) * (o • a) k = (o : (A.loc p).Ep) * ∑ k, (A.loc p).ιE (c k) * a k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
    rw [this]
    exact mul_mem o.2 ha
end GlobalTheory.HL.PlacesRec
