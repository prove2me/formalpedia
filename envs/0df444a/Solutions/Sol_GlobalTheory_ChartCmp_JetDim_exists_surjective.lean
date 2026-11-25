-- Prove2me | solution 1 for GlobalTheory.ChartCmp.JetDim.exists_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:56.816725+00:00
-- url     : https://prove2.me/submissions/15079888-7dcb-4e79-b524-3f8d07666602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_UniversalJetCoordinatesDimUnique
import Theorems.Thm_GlobalTheory_ChartCmp_JetDim_homAt_comp
import Theorems.Thm_GlobalTheory_ChartCmp_JetDim_homAt_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JetDim
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.JetDim
theorem _root_.solution {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} {z : GlobalTheory.PowGerm.JetPts G κ}
    {z' : GlobalTheory.PowGerm.JetPts G κ'} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) (hz' : GlobalTheory.PowGerm.IsUnivJ G κ' z') (m : ℕ) :
    ∃ ψ : Jet V κ' m →ₐ[V] Jet V κ m, Function.Surjective ψ := by
  have hk : ∀ σ : Type, RingHom.ker (jetAug : Jet V σ m →ₐ[V] V) ^ (m + 1) = ⊥ := fun σ => by
    have ea : (jetAug : Jet V σ m →ₐ[V] V) = Chart.jetAug V σ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow σ m
  obtain ⟨ψ, ⟨a, b⟩, -⟩ := hz'.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)
  obtain ⟨ψ', ⟨a', b'⟩, -⟩ := hz.2.2 _ jetAug m (hk κ') (z' m) (hz'.2.1 m)
  obtain ⟨χ, -, hu⟩ := hz.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)
  have e1 := hu (AlgHom.id V _) ⟨AlgHom.comp_id _, by rw [homAt_id, Category.id_comp]⟩
  have e2 := hu (ψ.comp ψ') ⟨by rw [← AlgHom.comp_assoc, a, a'], by
    rw [← homAt_comp, Category.assoc, ← b', ← b]⟩
  exact ⟨ψ, fun y => ⟨ψ' y, AlgHom.congr_fun (e2.trans e1.symm) y⟩⟩
end GlobalTheory.ChartCmp.JetDim
