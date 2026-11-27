-- Prove2me | solution 1 for GlobalTheory.JetLinSub.jetMap_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:38:02.869352+00:00
-- url     : https://prove2.me/submissions/416f9c61-c984-45c3-bc75-a6461b92b439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Theorems.Thm_GlobalTheory_JetLinSub_colsOf_flatL
import Theorems.Thm_GlobalTheory_JetLinSub_subst_renN
import Theorems.Thm_GlobalTheory_JetLinSub_isHolFam_clm
import Theorems.Thm_GlobalTheory_JetLinSub_jetPt_clm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anSpMap_comp


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.JetLinSub
theorem _root_.solution {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetMap m ψ Λ) :
    Φ.JetMap m (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ ψ) (Λ ∘ₗ B) := by
  obtain ⟨hol, rfl⟩ := h
  have he : ∀ v : Fin (n' * g) → ℂ, (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left =
      (Φ.e (Λ (colsOf n g (flatL B v)))).left := fun v => by rw [colsOf_flatL]; rfl
  have hol' : IsHolFam (fun v : Fin (n' * g) → ℂ => (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left) := by
    rw [funext he]
    exact isHolFam_clm _ hol (flatL B)
  refine ⟨hol', ?_⟩
  rw [← jetPt_clm _ hol (flatL B) _ hol' he m, ← Category.assoc, ← Category.assoc, ← anSpMap_comp, ← anSpMap_comp]
  congr 2
  exact RingHom.ext fun a => subst_renN B σ hσ a
end GlobalTheory.JetLinSub
