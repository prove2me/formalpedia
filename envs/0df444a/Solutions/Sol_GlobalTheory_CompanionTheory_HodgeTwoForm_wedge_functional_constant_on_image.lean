-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.wedge_functional_constant_on_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:57.895595+00:00
-- url     : https://prove2.me/submissions/46a85e76-886e-4723-97e7-851cb1c9a2c1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wedge_functional_iota_multi
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_eq_two
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_Lf_ev
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) (T : C)
    (t : ⋀[R]^2 (Glob1 F)) :
    L2 (fun i ↦ Lf hP (l i) T) i j (nu F t T) = algebraMap R (F.obj T) (L2 l i j t) := by
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := Glob1 F))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, nu_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    change Lf hP (l i) T (evForm F T _) * Lf hP (l j) T (evForm F T _) -
      Lf hP (l j) T (evForm F T _) * Lf hP (l i) T (evForm F T _) = _
    simp only [Lf_ev, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
  | smul c x _ hx =>
    simp only [map_smul, Pi.smul_apply, hx, smul_eq_mul, map_mul]
    rw [← algebraMap_smul (F.obj T) c, map_smul, hx, smul_eq_mul]
end GlobalTheory.CompanionTheory.HodgeTwoForm
