-- Prove2me | solution 1 for GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:01:24.512175+00:00
-- url     : https://prove2.me/submissions/6ef998a5-8cb7-4875-86e1-55d52938d67e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPoints
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPointsStatement
import Theorems.Thm_GlobalTheory_ChF_exists_series_of_natural


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (n d : ℕ) (L : ∀ (S : Type) [CommRing S] [Algebra R S], Prop), (∀ (k m : ℕ), L (Geo.Tor.JetR R (Fin n × Fin d) m ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) m)))) → ∀ (c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin n → Fin d → S) → S), (∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (a : Fin n → Fin d → S), L S → L S' → (∀ y : S, ∃ r : R, IsNilpotent (y - algebraMap R S r)) → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → φ (c S a) = c S' (fun i j => φ (a i j))) → ∃ f : PS R n d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S a = nv (algebraMap R S) f a := by
  first | exact @GlobalTheory.ChF.exists_series_of_natural | exact GlobalTheory.ChF.exists_series_of_natural | (intros; apply GlobalTheory.ChF.exists_series_of_natural <;> assumption)
end _root_.GlobalTheory.T
