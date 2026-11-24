-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.Ext.pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:58.933353+00:00
-- url     : https://prove2.me/submissions/2d2a3f00-7217-466c-b66a-b398e80eaa58

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
variable {R R'}
namespace GlobalTheory.CompanionTheory.PerfExt
namespace Ext
theorem _root_.solution {J : Type} [Finite J] {N Q : J → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module R' (Q i)] (c : ∀ i, N i → Q i) (h : ∀ i, Ext R R' (c i)) :
    Ext R R' (fun (f : ∀ i, N i) i ↦ c i (f i)) := by
  classical
  have := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' N).trans (LinearEquiv.piCongrRight e), fun b ↦ funext fun i ↦ ?_⟩
  simp [he]
end Ext
end GlobalTheory.CompanionTheory.PerfExt
