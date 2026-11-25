-- Prove2me | solution 1 for GlobalTheory.SeriesValue.ValAt.nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:31.329817+00:00
-- url     : https://prove2.me/submissions/862abb50-73d3-43db-8a93-aef7fbd82e26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange GlobalTheory.TorsionCharacter ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev addOf)
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}
variable {O : Type} [CommRing O] [Algebra V O]
variable {x : Fam G (Fin d)} {u : PS O 1 d} {A : Type} [CommRing A] [Algebra O A]
omit [GrpObj G]
namespace GlobalTheory.SeriesValue
namespace ValAt
theorem _root_.solution {m : ℕ} {g : Spec (CommRingCat.of A) ⟶ G.left}
    {z : Fin d → A} {k : A} (h : ValAt x u m g z k) : IsNilpotent (Ideal.span (Set.range z)) := by
  obtain ⟨ψ, h1, -, -⟩ := h
  refine ⟨m + 1, eq_bot_iff.2 ?_⟩
  have : Ideal.span (Set.range z) ≤ (RingHom.ker (jetAug O (Fin 1 × Fin d) m)).map ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← h1 (0, j)]
    exact Ideal.mem_map_of_mem _ (zR_mem_ker m _)
  refine (Ideal.pow_right_mono this _).trans ?_
  rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot]
end ValAt
end GlobalTheory.SeriesValue
