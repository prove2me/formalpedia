-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.Lc_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:39.09303+00:00
-- url     : https://prove2.me/submissions/79124755-d1d4-4183-b49b-b48f20996a62

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (u : H1 F ⊗[R] Glob1 F) :
    (Lc hcl τ u).1.1 = 0 ∧ (Lc hcl τ u).1.2.1 = mu (sR τ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    constructor
    · rw [map_add]
      change (Lc hcl τ a).1.1 + (Lc hcl τ b).1.1 = 0
      rw [ha.1, hb.1, add_zero]
    · rw [map_add, map_add, map_add]
      change (Lc hcl τ a).1.2.1 + (Lc hcl τ b).1.2.1 = _
      rw [ha.2, hb.2]
  | tmul v w =>
    constructor
    · funext T T' T'' φ ψ
      change (cupTot F (τ v).1 (cl hcl w).1).1 T T' T'' φ ψ = 0
      simp [cupTot_apply, cl_coe]
    · funext T T' φ
      change (cupTot F (τ v).1 (cl hcl w).1).2.1 T T' φ = mu ((cechDeRhamTotalCocyclesOne.fn F (τ v)) ⊗ₜ w) T T' φ
      rw [hmu, cupTot_a]
      simp [cl_coe]
      rfl
end GlobalTheory.CompanionTheory.HypWedge
