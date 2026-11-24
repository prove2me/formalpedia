-- Prove2me | solution 1 for GlobalTheory.NormCompat.finite_setOf_under_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:42.948389+00:00
-- url     : https://prove2.me/submissions/f4e4f91c-3357-4978-920f-8a50270c2ab9

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ProdLocalValuesGlobalOverPlacesAbove
import Theorems.Thm_GlobalTheory_NormCompat_under_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.NormCompat
namespace GlobalTheory.NormCompat
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← (under_eq_iff w v).mp hw]
end GlobalTheory.NormCompat
