-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.integral_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:50.330634+00:00
-- url     : https://prove2.me/submissions/55215447-251b-461c-9048-3285b353a897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart
import Theorems.Thm_GlobalTheory_Reg_Transfer_nonneg_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing NumberField IsDedekindDomain Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  refine nonneg_at S hF h0 j x hxE hx0 V φ 1 (q F) (hChV a n F hF) ?_
  have hm : maximalIdeal S.O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
  exact hcen ϖ hϖ
end GlobalTheory.Reg.Transfer
