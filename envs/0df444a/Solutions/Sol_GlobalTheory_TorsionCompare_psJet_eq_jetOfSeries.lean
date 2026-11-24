-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.psJet_eq_jetOfSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:31:14.823875+00:00
-- url     : https://prove2.me/submissions/42121c03-e96e-4c97-aae5-7e05dd96dad2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R]
namespace GlobalTheory.TorsionCompare
theorem _root_.solution {n d : ℕ} [Nonempty (Fin n × Fin d)] (m : ℕ) (f : PS R n d) :
    psJet m f = jetOfSeries m f := by
  classical
  unfold psJet jetOfSeries
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_trunc, MvPowerSeries.coeff_truncTotal _ hx,
    if_pos, sub_self]
  have hle : ∀ q, x q < m + 1 := fun q => lt_of_le_of_lt (Finsupp.le_degree q x) hx
  refine lt_of_le_of_ne (fun q => by simpa using (hle q).le) fun h => ?_
  obtain ⟨q⟩ := ‹Nonempty (Fin n × Fin d)›
  have := hle q
  rw [h] at this
  simp at this
end GlobalTheory.TorsionCompare
