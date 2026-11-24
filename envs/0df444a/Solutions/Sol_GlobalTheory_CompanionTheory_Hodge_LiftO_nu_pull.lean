-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.nu_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:57.580716+00:00
-- url     : https://prove2.me/submissions/01714500-aa64-4e7b-ab47-2a889226c268

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exterior_map_iota_two
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_qOm_wedge
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m : CoefMap (RingHom.id R) F G)
    (νF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2) (νG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, νF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, νG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (t : ⋀[R]^2 (Glob1 F)) (T : E) :
    νG (exteriorPower.map 2 (pullGlob1 m) t) T = qOm m 2 T (νF t _) := by
  have e : (LinearMap.proj T : W0 G 2 →ₗ[R] _) ∘ₗ νG ∘ₗ exteriorPower.map 2 (pullGlob1 m) =
      (qOm m 2 T) ∘ₗ (LinearMap.proj (m.G.obj T) : W0 F 2 →ₗ[R] _) ∘ₗ νF := ext2 fun a b ↦ by
    simp only [LinearMap.comp_apply, exterior_map_iota_two, LinearMap.proj_apply]
    rw [hG, hF, qOm_wedge]
    rfl
  exact LinearMap.congr_fun e t
end GlobalTheory.CompanionTheory.Hodge.LiftO
