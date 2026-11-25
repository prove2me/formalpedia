-- Prove2me | solution 1 for GlobalTheory.SeriesValue.exists_hasVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:30:22.661387+00:00
-- url     : https://prove2.me/submissions/238fa2c6-eeb6-46b8-9f7a-7d795ac59fae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_existsUnique_jet
import Theorems.Thm_GlobalTheory_SeriesValue_jetIn_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
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
theorem _root_.solution [IsLocalRing V] (hx : IsUnivChart G d x) (u : PS O 1 d) (J : Ideal A) (hJ : IsNilpotent J)
    (g : specV (algebraMap V O) A ⟶ G)
    (hg : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (1 : specV (algebraMap V O) A ⟶ G).left) :
    ∃ k, HasVal x u g.left k := by
  obtain ⟨m, hm⟩ := hJ
  have hJ : J ^ (m + 1) = ⊥ := pow_eq_zero_of_le (Nat.le_succ m) hm
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let q := Ideal.Quotient.mkₐ V J
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := existsUnique_jet hx q Ideal.Quotient.mk_surjective (m := m)
    ((congrArg (· ^ (m + 1)) (Ideal.mk_ker (I := J))).trans hJ) g (by
      rw [← MonObj.comp_one (spMap q)]
      exact Over.OverMorphism.ext hg)
  let ψ : JetR O (Fin 1 × Fin d) m →ₐ[O] A :=
    jetLift O J hJ (fun r => φ (zR m r.2)) (fun r => Ideal.Quotient.eq_zero_iff_mem.1 (h1 r.2))
  have e : φ = (ψ.restrictScalars V).comp (jetIn V d O m) := jet_ext fun j => by
    show _ = ψ (jetIn V d O m _)
    rw [jetIn_zR, jetLift_zR]
  refine ⟨_, m, fun j => φ (zR m j), ψ, fun r => jetLift_zR _ _ _ _ r, ?_, rfl⟩
  rw [h2, e]
  rfl
end GlobalTheory.SeriesValue
