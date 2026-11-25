-- Prove2me | solution 1 for GlobalTheory.SeriesValue.existsUnique_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:44.797941+00:00
-- url     : https://prove2.me/submissions/62db2051-97c3-4ea8-b08b-a9b71ae87c76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_ChartBaseChange_chart_aug
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_pt_of_aug
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_cond
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_ker
import Theorems.Thm_GlobalTheory_ChartBaseChange_pt_eps_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
namespace GlobalTheory.SeriesValue
theorem _root_.solution [IsLocalRing V] {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (q : A →ₐ[V] B) (hq : Function.Surjective q) {m : ℕ}
    (hJ : (RingHom.ker q) ^ (m + 1) = ⊥) (y : sp (R₀ := V) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃! ψ : JetR V (Fin d) m →ₐ[V] A, (∀ j, q (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m := by
  obtain ⟨C⟩ := exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug V (Fin d) m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (chart_aug hx m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJ) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  refine ⟨(fibSnd q).comp ψ₀, ⟨fun j => ?_, ?_⟩, ?_⟩
  · show q (fibSnd q (ψ₀ (zR m j))) = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  · rw [← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro v ⟨hψa, hψ⟩
    have hv : q.comp v = (Algebra.ofId V B).comp (jetAug V (Fin d) m) := by
      refine jet_ext fun j => ?_
      show q (v (zR _ j)) = algebraMap V B (jetAug V _ m (zR m j))
      rw [hψa, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, hk, spMap_pt]
    have e := hu (fibLift q (jetAug V (Fin d) m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    rw [← e]
    rfl
end GlobalTheory.SeriesValue
