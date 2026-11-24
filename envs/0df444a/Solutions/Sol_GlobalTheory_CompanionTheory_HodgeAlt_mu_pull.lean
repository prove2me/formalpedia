-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.mu_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:28:02.908996+00:00
-- url     : https://prove2.me/submissions/5e7b5f60-89de-4b3e-a5b8-4107748c1af8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_prodFirstProjection_smul
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
theorem _root_.solution (m : CoefMap (RingHom.id R) F G) (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) {T T' : D} (φ : T ⟶ T') :
    muG (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) T T' φ =
      q1 m T' (muF t _ _ (m.G.map φ)) := by
  induction t with
  | zero => simp
  | tmul f ω =>
    rw [TensorProduct.map_tmul, hG, hF, prodFirstProjection_smul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
end GlobalTheory.CompanionTheory.HodgeAlt
