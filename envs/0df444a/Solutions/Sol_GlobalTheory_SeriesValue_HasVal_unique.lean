-- Prove2me | solution 1 for GlobalTheory.SeriesValue.HasVal.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:37.21761+00:00
-- url     : https://prove2.me/submissions/e7cea20d-1565-413c-b6ff-74d5eb5762d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_existsUnique_jet
import Theorems.Thm_GlobalTheory_SeriesValue_jetIn_zR
import Theorems.Thm_GlobalTheory_SeriesValue_exists_common
import Theorems.Thm_GlobalTheory_ChartBaseChange_chart_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
namespace HasVal
theorem _root_.solution [IsLocalRing V] (hx : IsUnivChart G d x) {g : Spec (CommRingCat.of A) ⟶ G.left} {k k' : A}
    (h : HasVal x u g k) (h' : HasVal x u g k') : k = k' := by
  obtain ⟨m, z, z', J, hJ, hz, hz', ⟨ψ, h1, h2, h3⟩, ⟨ψ', h1', h2', h3'⟩⟩ := exists_common hx h h'
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ := (ψ.restrictScalars V).comp (jetIn V d O m)
  let φ' := (ψ'.restrictScalars V).comp (jetIn V d O m)
  let q := Ideal.Quotient.mkₐ V J
  have hφ : ∀ j, φ (zR m j) = z j := fun j => (congrArg ψ (jetIn_zR m j)).trans (h1 _)
  have hφ' : ∀ j, φ' (zR m j) = z' j := fun j => (congrArg ψ' (jetIn_zR m j)).trans (h1' _)
  have hq : ∀ j, q (φ (zR m j)) = 0 := fun j => by rw [hφ]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hz j)
  have hq' : ∀ j, q (φ' (zR m j)) = 0 := fun j => by rw [hφ']; exact Ideal.Quotient.eq_zero_iff_mem.2 (hz' j)
  have e : φ = φ' := (existsUnique_jet hx q Ideal.Quotient.mk_surjective (m := m) ((congrArg (· ^ (m + 1)) (Ideal.mk_ker (I := J))).trans hJ)
    (spMap φ ≫ x m) (by
      have : q.comp φ = (Algebra.ofId V _).comp (jetAug V (Fin d) m) := jet_ext fun j => by
        rw [AlgHom.comp_apply, hq, AlgHom.comp_apply, jetAug_zR, map_zero]
      rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, chart_aug hx, MonObj.comp_one])).unique
    ⟨hq, rfl⟩ ⟨hq', Over.OverMorphism.ext (h2.symm.trans h2')⟩
  have e' : ψ = ψ' := jet_ext fun r => by rw [h1, h1', ← hφ, ← hφ', e]
  rw [h3, h3', e']
end HasVal
end GlobalTheory.SeriesValue
