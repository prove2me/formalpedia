-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.mu_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:04.132747+00:00
-- url     : https://prove2.me/submissions/cd0fcd5f-9d5a-4ed1-a0ea-efe53252c919

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m : CoefMap (RingHom.id R) F G)
    (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F) (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (t : Z1 F ⊗[R] Glob1 F) {T T' : E} (φ : T ⟶ T') :
    muG (TensorProduct.map m.pullbackOneCocycle (pullGlob1 m) t) T T' φ = q1 m T' (muF t _ _ (m.G.map φ)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f ω =>
    rw [TensorProduct.map_tmul, hG, hF, prodFirstProjection_smul]; rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
end GlobalTheory.CompanionTheory.Hodge.LiftO
