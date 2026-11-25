-- Prove2me | solution 1 for GlobalTheory.HL.PlacesInt.mem_O_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:56:45.730345+00:00
-- url     : https://prove2.me/submissions/a20c0019-2fef-4a58-a904-06da99f1631c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Theorems.Thm_GlobalTheory_HL_PlacesInt_mem_int_iff
import Theorems.Thm_GlobalTheory_HL_PlacesInt_nontrivial_Ep
import Theorems.Thm_GlobalTheory_HL_PlacesInt_isIntegral_of_quad
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PlacesInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.HL.PlacesInt
theorem _root_.solution (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) (t n : F)
    (ht : algebraMap F E t = x + sig x) (hn : algebraMap F E n = x * sig x) :
    (A.loc p).ιE x ∈ (A.L p).O ↔ p.valuation F t ≤ 1 ∧ p.valuation F n ≤ 1 := by
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  haveI := nontrivial_Ep (A.loc p)
  have ht' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF t)
      = (A.loc p).ιE x + (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, ht, map_add, A.L_cj, (A.loc p).cj_ιE]
  have hn' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF n)
      = (A.loc p).ιE x * (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, hn, map_mul, A.L_cj, (A.loc p).cj_ιE]
  rw [← mem_int_iff (A.loc p), ← mem_int_iff (A.loc p)]
  constructor
  · intro hx
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[(A.loc p).Fp]
    obtain ⟨-, ⟨c, hc⟩, d, hd⟩ := (GlobalTheory.UnramOrder.order_facts (A.L p) ϖ hϖ).2.1 _ hx
    have hinj := (algebraMap (A.loc p).Fp (A.loc p).Ep).injective
    rw [hinj (ht'.trans hc), hinj (hn'.trans hd)]
    exact ⟨c.2, d.2⟩
  · rintro ⟨h1, h2⟩
    rw [(A.L p).O_def]
    exact isIntegral_of_quad (R := 𝒪[(A.loc p).Fp]) _ _ ⟨_, h1⟩ ⟨_, h2⟩ ht' hn'
end GlobalTheory.HL.PlacesInt
