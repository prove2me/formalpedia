-- Prove2me | solution 1 for GlobalTheory.ChartJLaw.isLawOf_of_isChartJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:00:43.243869+00:00
-- url     : https://prove2.me/submissions/abd8f6c3-205b-4b93-a9c0-c7b79b54f5a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Theorems.Thm_GlobalTheory_ChartJLaw_substJ_zR
import Theorems.Thm_GlobalTheory_ChartJLaw_constantCoeff_ev
import Theorems.Thm_GlobalTheory_ChartJLaw_read_pt
import Theorems.Thm_GlobalTheory_JetSer_exists_jetHom
import Theorems.Thm_GlobalTheory_JetSer_jetAlg
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJLaw
variable {T : Type} [CommRing T] {d : ℕ}
namespace GlobalTheory.ChartJLaw
theorem _root_.solution : ∀ (T : Type) [CommRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 → (∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left) → GlobalTheory.JetSer.IsLawOf x0 F.F := by
  intro T _ G _ _ d F x hx x0 _ ⟨ρ, hρ1, hρ2⟩
  refine ⟨F.const, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt T n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  have hF : ∀ j, MvPowerSeries.constantCoeff (addOf F.F a b j) = 0 :=
    fun j => constantCoeff_ev _ hab _ (F.const j)
  refine ⟨hF, fun m => ?_⟩
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg T (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d)
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt T n d) p.1 p.2) (fun p => hab p.1 p.2) m
  obtain ⟨ψ, hψ⟩ := JetSer.exists_jetHom (addOf F.F a b) hF m
  have key : ∀ (i : Fin 2) (χ : Chart.JetR T (Fin d) m →ₐ[T] Chart.JetR T (Fin n × Fin d) m),
      (∀ j, χ (Chart.zR m j) = JetSer.toJet m ((![a, b] : Fin 2 → Pt T n d) i j)) →
      χ.comp (ρ m) = Φ.comp (jetPt (d := d) i m) := by
    intro i χ hχ
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hχ, jetPt, substJ_zR, JetSer.toJet_X, hΦ]
  have keyF : ψ.comp (ρ m) = Φ.comp (substJ m F.F F.const) := by
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hψ, substJ_zR, hsub Φ hΦ]
    rfl
  refine ⟨ψ, hψ, ?_⟩
  show y m * z m = _
  rw [read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψ keyF, hx.law m, MonObj.comp_mul, ha2, hb2,
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψa (key 0 ψa ha1),
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψb (key 1 ψb hb1)]
end GlobalTheory.ChartJLaw
