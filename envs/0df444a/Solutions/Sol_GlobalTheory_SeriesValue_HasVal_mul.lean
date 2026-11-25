-- Prove2me | solution 1 for GlobalTheory.SeriesValue.HasVal.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:40.631004+00:00
-- url     : https://prove2.me/submissions/0190cab2-6ee2-47f0-9c1f-642a6339ad3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_jetIn_zR
import Theorems.Thm_GlobalTheory_SeriesValue_exists_common
import Theorems.Thm_GlobalTheory_ChartBaseChange_const_map
import Theorems.Thm_GlobalTheory_ChartBaseChange_eval_standard_points_two
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_test
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_toJet
import Theorems.Thm_GlobalTheory_JetSer_jetAlg
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


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
theorem _root_.solution (hx : IsUnivChart G d x) {L : Fin d → PS V 2 d} (hL : IsLawOf x L)
    (hu : ev (n := 2) ![fun i => MvPowerSeries.map (algebraMap V O) (L i)] u =
      ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0] u * ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1] u)
    {g g' : specV (algebraMap V O) A ⟶ G} {k k' : A}
    (h : HasVal x u g.left k) (h' : HasVal x u g'.left k') : HasVal x u (g * g').left (k * k') := by
  obtain ⟨m, z, z', J, hJ, hz, hz', ⟨ψ, h1, h2, h3⟩, ⟨ψ', h1', h2', h3'⟩⟩ := exists_common hx h h'
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let Θ : JetR O (Fin 2 × Fin d) m →ₐ[O] A := jetLift O J hJ (fun r => ![z, z'] r.1 r.2) (by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [hz j, hz' j])
  have hΘ : ∀ r, Θ (zR m r) = ![z, z'] r.1 r.2 := jetLift_zR _ _ _ _
  let Θv := (Θ.restrictScalars V).comp (jetCoeff V O (Fin 2 × Fin d) m)
  have sub : ∀ a : Pt O 2 d, (∀ j, MvPowerSeries.constantCoeff (a j) = 0) →
      ∃ ρ : JetR O (Fin 1 × Fin d) m →ₐ[O] JetR O (Fin 2 × Fin d) m, (∀ r, ρ (zR m r) = toJet m (a r.2)) ∧
        ρ (toJet m u) = toJet m (ev ![a] u) := fun a ha => by
    have H := (jetAlg O (Fin 2 × Fin d)).2.2.2.2 (Fin 1 × Fin d) (fun r => (![a] : Fin 1 → Pt O 2 d) r.1 r.2)
      (fun r => by rw [Subsingleton.elim r.1 0]; exact ha _) m
    obtain ⟨ρ, hρ⟩ := H.1
    exact ⟨ρ, fun r => (hρ r).trans (by rw [Subsingleton.elim r.1 0]; rfl), H.2 ρ hρ u⟩
  obtain ⟨ρ, hρ, hρu⟩ := sub (fun i => MvPowerSeries.map (algebraMap V O) (L i)) (fun i => const_map (hL.1 i))
  obtain ⟨ρ₀, hρ₀, hρ₀u⟩ := sub (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0) (gp_pt 0)
  obtain ⟨ρ₁, hρ₁, hρ₁u⟩ := sub (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1) (gp_pt 1)
  have e₀ : ψ = Θ.comp ρ₀ := jet_ext fun r => by
    rw [h1, AlgHom.comp_apply, hρ₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, toJet_X, hΘ]; rfl
  have e₁ : ψ' = Θ.comp ρ₁ := jet_ext fun r => by
    rw [h1', AlgHom.comp_apply, hρ₁, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, toJet_X, hΘ]; rfl
  obtain ⟨t, ht⟩ := exists_test jetAlg x 2
  obtain ⟨χ, hχ, hχ'⟩ := (hL.2 2 _ _ _ _ (ht 0) (ht 1)).2 m
  have key : ∀ (a : Pt V 2 d) (χ : JetR V (Fin d) m →ₐ[V] JetR V (Fin 2 × Fin d) m)
      (ρ : JetR O (Fin 1 × Fin d) m →ₐ[O] JetR O (Fin 2 × Fin d) m), (∀ j, χ (zR m j) = toJet m (a j)) →
      (∀ r, ρ (zR m r) = toJet m (MvPowerSeries.map (algebraMap V O) (a r.2))) →
      spMap (((Θ.comp ρ).restrictScalars V).comp (jetIn V d O m)) ≫ x m = spMap Θv ≫ spMap χ ≫ x m :=
    fun a χ ρ hχ hρ => by
      rw [← Category.assoc, spMap_comp]
      congr 2
      refine jet_ext fun j => ?_
      show Θ (ρ (jetIn V d O m _)) = Θ (jetCoeff V O _ m (χ _))
      rw [jetIn_zR, hρ, hχ, jetCoeff_toJet]
  have hg : ∀ (i : Fin 2) (ρ : JetR O (Fin 1 × Fin d) m →ₐ[O] JetR O (Fin 2 × Fin d) m),
      (∀ r, ρ (zR m r) = toJet m (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d i r.2)) →
      spMap (((Θ.comp ρ).restrictScalars V).comp (jetIn V d O m)) ≫ x m = spMap Θv ≫ t i m := fun i ρ hρ => by
    obtain ⟨χ, hχ, hχ'⟩ := (ht i).2 m
    rw [hχ']
    exact key _ χ ρ hχ fun r => (hρ r).trans (by
      unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt; rw [MvPowerSeries.map_X])
  have g0 : g = spMap Θv ≫ t 0 m := (Over.OverMorphism.ext (by rw [h2, e₀]; rfl)).trans (hg 0 ρ₀ hρ₀)
  have g1 : g' = spMap Θv ≫ t 1 m := (Over.OverMorphism.ext (by rw [h2', e₁]; rfl)).trans (hg 1 ρ₁ hρ₁)
  refine ⟨m, fun j => Θ (toJet m (MvPowerSeries.map (algebraMap V O) (L j))), Θ.comp ρ,
    fun r => congrArg Θ (hρ r), ?_, ?_⟩
  · have := key _ χ ρ hχ fun r => (hρ r).trans (by unfold addOf; rw [eval_standard_points_two])
    rw [← hχ', MonObj.comp_mul, ← g0, ← g1] at this
    exact (congrArg (·.left) this).symm
  · obtain ⟨τ, hτ, -⟩ := (jetAlg O (Fin 2 × Fin d)).1 m
    rw [h3, h3', e₀, e₁, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, hρu, hρ₀u, hρ₁u, hu, ← hτ (_ * _),
      map_mul, map_mul, hτ, hτ]
end HasVal
end GlobalTheory.SeriesValue
