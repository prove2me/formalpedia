-- Prove2me | solution 1 for GlobalTheory.Up.Definite.card_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:16.432814+00:00
-- url     : https://prove2.me/submissions/9f4e7bdf-9b58-4e21-9dbe-5c23f824991e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.Definite
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Up.Definite
theorem _root_.solution (X : Data E r) (h : Module.finrank ℚ E = 2) : Fintype.card X.Ψ = 1 := by
  classical
  have hc : Fintype.card (E →+* ℂ) = 2 := by rw [Embeddings.card, h]
  have hb : X.Ψ.card = X.Ψᶜ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ)
      (fun τ hτ => Finset.mem_compl.mpr ((X.cmType τ).mp hτ)) (fun _ _ _ _ h => star_injective h)
      fun τ hτ => ⟨ComplexEmbedding.conjugate τ, (X.cmType _).mpr ?_, star_star τ⟩
    rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ]
    exact Finset.mem_compl.mp hτ
  have := X.Ψ.card_add_card_compl
  rw [Fintype.card_coe]
  omega
end GlobalTheory.Up.Definite
