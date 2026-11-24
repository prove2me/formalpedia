-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotKer.mul_eq_zero_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:32.265367+00:00
-- url     : https://prove2.me/submissions/b584210f-0585-48d5-9709-83eadc1d523b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer
namespace GlobalTheory.CompanionTheory.CotKer
theorem _root_.solution {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (a b : Γ(Sp Q, ⊤))
    (ha : (spMap q).appTop.hom a = 0) (hb : (spMap q).appTop.hom b = 0) : a * b = 0 := by
  have key : ∀ x : Γ(Sp Q, ⊤), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap q).appTop.hom x) =
      q ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom x) := fun x =>
    congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
  have hφ : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom hxy
    simpa using h
  apply hφ
  rw [map_mul, map_zero]
  apply hq
  · rw [← key, ha, map_zero]
  · rw [← key, hb, map_zero]
end GlobalTheory.CompanionTheory.CotKer
