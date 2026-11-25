-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.approxE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:13.257071+00:00
-- url     : https://prove2.me/submissions/e607382d-df62-4070-8676-1dc47a523c9f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_approxF
import Theorems.Thm_GlobalTheory_HL_StrongApprox_exists_d
import Theorems.Thm_GlobalTheory_HL_StrongApprox_O_of_int
import Theorems.Thm_GlobalTheory_HL_StrongApprox_decomp
import Theorems.Thm_GlobalTheory_HL_StrongApprox_fin_two
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (y : ∀ p, (A.loc p).Ep) (hy : {p | y p ∉ (A.L p).O}.Finite) :
    ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  obtain ⟨d, hd, hd0⟩ := exists_d A
  have hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O := (PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩
  have hdi := (PlacesInt.integers_local A).2.1 (d : E)⁻¹
  choose a b hab _ hint using fun p => decomp A d hd hd0 p (y p)
  have hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪
      {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} →
      a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp] := by
    intro p hp
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    exact hint p hp.1.1 hp.1.2 hp.2
  have hfin := (hy.union hdi).union (fin_two A)
  obtain ⟨α, hα⟩ := approxF A c hc a (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).1)
  obtain ⟨β, hβ⟩ := approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)
  refine ⟨algebraMap F E α + algebraMap F E β * d, fun p => ?_⟩
  obtain ⟨o1, ho1⟩ := hα p
  obtain ⟨o2, ho2⟩ := hβ p
  refine ⟨algebraMap _ _ (o1 : (A.loc p).Fp) + algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d,
    add_mem (O_of_int A p o1) (mul_mem (O_of_int A p o2) (hdO p)), ?_⟩
  have e1 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho1
  have e2 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2
  rw [map_sub, map_mul] at e1 e2
  rw [map_add, map_mul, (A.loc p).compat, (A.loc p).compat]
  linear_combination e1 + (A.loc p).ιE d * e2 - hab p
end GlobalTheory.HL.StrongApprox
