-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism.std_mem_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:33.04648+00:00
-- url     : https://prove2.me/submissions/9b374b40-fca2-49d2-a3e8-905326e9cd80

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
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)
private theorem eqAtPrime_refl {n : ℕ} (p : ℕ) (hp : p.Prime) (L : Submodule (𝓞 E) (Fin n → E)) :
    EqAtPrime p L L :=
  ⟨fun x hx => ⟨1, hp.not_dvd_one, by simpa using hx⟩, fun x hx => ⟨1, hp.not_dvd_one, by simpa using hx⟩⟩
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
end
end

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
theorem _root_.solution (n : ℕ) (s : ℕ+) : Lat.std E n ∈ reps Δ n s := by
  refine ⟨fun p hp => ⟨LinearEquiv.refl E _, fun x y => rfl, ?_⟩, fun p hp _ => eqAtPrime_refl p hp _⟩
  have hm : ((Lat.std E n).map (LinearEquiv.refl E _)).L = (Lat.std E n).L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hm]
  exact eqAtPrime_refl p hp _
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
