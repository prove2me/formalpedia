-- Prove2me | solution 1 for GlobalTheory.SeriesValue.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:14:04.271026+00:00
-- url     : https://prove2.me/submissions/6b048c6e-a60f-4a82-b22a-10d3750a5cbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_ValAt_mono
import Theorems.Thm_GlobalTheory_SeriesValue_ValAt_nilpotent
import Theorems.Thm_GlobalTheory_FamGerm_Pt1_Red_mono


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
namespace GlobalTheory.SeriesValue
theorem _root_.solution (hx : IsUnivChart G d x) {g g' : Spec (CommRingCat.of A) ⟶ G.left} {k k' : A}
    (h : HasVal x u g k) (h' : HasVal x u g' k') :
    ∃ (m : ℕ) (z z' : Fin d → A) (J : Ideal A), J ^ (m + 1) = ⊥ ∧ (∀ j, z j ∈ J) ∧ (∀ j, z' j ∈ J) ∧
      ValAt x u m g z k ∧ ValAt x u m g' z' k' := by
  obtain ⟨m, z, h⟩ := h
  obtain ⟨m', z', h'⟩ := h'
  obtain ⟨n, hn⟩ := (Commute.all _ _).isNilpotent_add h.nilpotent h'.nilpotent
  refine ⟨m + m' + n, z, z', Ideal.span (Set.range z) + Ideal.span (Set.range z'), ?_,
    fun j => Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩), fun j => Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩),
    h.mono hx (by omega), h'.mono hx (by omega)⟩
  exact pow_eq_zero_of_le (by omega) hn
end GlobalTheory.SeriesValue
