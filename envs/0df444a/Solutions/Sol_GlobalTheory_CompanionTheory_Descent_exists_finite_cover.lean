-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.exists_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:10.037988+00:00
-- url     : https://prove2.me/submissions/9013eb2e-b83d-4521-95c1-736f80c67d8b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution {P : Type} (v : P → X.affineOpens) (W : X.affineOpens)
    (hcov : ⨆ a, (v a).1 = W.1) : ∃ T : Finset P, W.1 ≤ ⨆ a : T, (v a.1).1 := by
  obtain ⟨T, hT⟩ := W.2.isCompact.elim_finite_subcover (fun a ↦ ((v a).1 : Set X))
    (fun a ↦ (v a).1.isOpen) (by
      intro x hx
      have : x ∈ ((⨆ a, (v a).1 : X.Opens) : Set X) := by rw [hcov]; exact hx
      simpa [TopologicalSpace.Opens.coe_iSup] using this)
  refine ⟨T, fun x hx ↦ ?_⟩
  have := hT hx
  simpa [TopologicalSpace.Opens.coe_iSup] using this
end GlobalTheory.CompanionTheory.Descent
