-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:42.250809+00:00
-- url     : https://prove2.me/submissions/48863eac-53a1-45e8-bef6-1a115fb4c4c0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
import Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_mul_eq_zero_open
import Theorems.Thm_GlobalTheory_CompanionTheory_CotKer_comp_comp_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer
namespace GlobalTheory.CompanionTheory.CotKer
theorem _root_.solution : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  intro R Q B _ _ _ U e _ q ρ y _ hq hcomm
  show _ ≤ Scheme.IdealSheafData.ofIdeals (fun V => RingHom.ker (y.app V).hom)
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro V
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply e V, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb ⊢
  have key : ∀ s, (e.app V).hom s = 0 → ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = 0 := by
    intro s hs
    have h1 : ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = ((spMap q ≫ y).app V).hom s := by
      rw [Scheme.Hom.comp_app]
      rfl
    rw [h1, Scheme.Hom.congr_app hcomm V, Scheme.Hom.comp_app]
    exact comp_comp_apply_eq_zero _ _ _ s hs
  rw [map_mul]
  exact mul_eq_zero_open q hq (y ⁻¹ᵁ V) _ _ (key a ha) (key b hb)
end GlobalTheory.CompanionTheory.CotKer
