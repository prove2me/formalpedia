-- Prove2me | solution 1 for GlobalTheory.ChartCmp.univJ_dim_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:44.014378+00:00
-- url     : https://prove2.me/submissions/b11ee1a9-6dbd-4830-8954-e8610b234df9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
import Theorems.Thm_GlobalTheory_ChartCmp_JetDim_card_le_of_surjective
import Theorems.Thm_GlobalTheory_ChartCmp_JetDim_exists_surjective

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by
  intro V _ _ G _ d d' x x' h h'
  obtain ⟨ψ, hψ⟩ := JetDim.exists_surjective h h' 1
  obtain ⟨ψ', hψ'⟩ := JetDim.exists_surjective h' h 1
  have a := JetDim.card_le_of_surjective ψ hψ
  have b := JetDim.card_le_of_surjective ψ' hψ'
  simp only [Fintype.card_prod, Fintype.card_fin, one_mul] at a b
  omega
end GlobalTheory.ChartCmp
