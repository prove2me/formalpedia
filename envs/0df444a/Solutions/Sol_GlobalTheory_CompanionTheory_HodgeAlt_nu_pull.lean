-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.nu_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:41.259238+00:00
-- url     : https://prove2.me/submissions/b84a8d24-988e-4332-b044-539324f1b7a4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_map2
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (m : CoefMap (RingHom.id R) F G) (nuF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (nuG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, nuF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, nuG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (τ : ⋀[R]^2 (Glob1 F)) (T : D) :
    nuG (exteriorPower.map 2 (pullGlob1 m) τ) T = qOm m 2 T (nuF τ (m.G.obj T)) := by
  have e : (LinearMap.proj (φ := fun T ↦ Om R (G.obj T) 2) T ∘ₗ nuG ∘ₗ
      exteriorPower.map 2 (pullGlob1 m)) =
      ((qOm m 2 T : _ →ₗ[R] _) ∘ₗ LinearMap.proj (φ := fun T ↦ Om R (F.obj T) 2) (m.G.obj T) ∘ₗ nuF) :=
    ext2 fun a b ↦ by
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, map2, hG, hF]
      exact (qOm_wedge m (a.1 _) (b.1 _)).symm
  exact LinearMap.congr_fun e τ
end GlobalTheory.CompanionTheory.HodgeAlt
