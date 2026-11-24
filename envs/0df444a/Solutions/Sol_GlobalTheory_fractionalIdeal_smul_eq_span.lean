-- Prove2me | solution 1 for GlobalTheory.fractionalIdeal_smul_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:01.0119+00:00
-- url     : https://prove2.me/submissions/6546cd0b-0457-4d47-8e2f-b5cc22b3d474

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsPosNatMemFractionalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by
  refine le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, u, hu, rfl⟩
  exact Submodule.smul_mem_smul hα hu
end GlobalTheory
