-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism.IsShortRule.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:14.924942+00:00
-- url     : https://prove2.me/submissions/17ef8586-41a5-4dc1-a3b4-432a1805d7fb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
namespace IsShortRule
theorem _root_.solution (h : CoverTot Δ) {n N : ℕ} {Λ : Lat E n} {β : c.F} {x₀ : Fin n → ConjCl Dw l}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hd : IsSeriesData Δ Λ N β a P) {f g : Rul Xo c}
    (hf : IsShortRule Δ Λ N β x₀ a P f) (hg : IsShortRule Δ Λ N β x₀ a P g) : f = g := by
  funext p y
  obtain ⟨⟨S', _, _, φ, y₂, hff, hl⟩, hf2⟩ := hf p y
  obtain ⟨v, hv, hfv⟩ := hf2 S' φ y₂ hl
  obtain ⟨w, hw, hgw⟩ := (hg p y).2 S' φ y₂ hl
  obtain ⟨u, -, hu⟩ := h n N Λ β x₀ a P hd S' y₂
  have hvw : v = w := (hu v hv).trans (hu w hw).symm
  apply hff.injective
  rw [hfv, hgw, hvw]
end IsShortRule
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
