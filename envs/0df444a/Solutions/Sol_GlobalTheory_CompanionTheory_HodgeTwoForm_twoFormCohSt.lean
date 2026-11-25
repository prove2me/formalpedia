-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:37.460462+00:00
-- url     : https://prove2.me/submissions/5200c607-b864-4cfb-8783-b6ee44fa56b6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_expand
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_Lf_expand
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wedge_functional_two_form_naturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wedge_functional_constant_on_image
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution : TwoFormCohSt := by
  intro R _ C _ F ⟨hS, hP, hF, hPr⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (Glob1 F)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let w : Fin n → Glob1 F := fun i ↦ f (Pi.single i 1)
  let l : Fin n → Module.Dual R (Glob1 F) := fun i ↦ LinearMap.proj i ∘ₗ s
  have hdual : ∀ x, x = ∑ i, l i x • w i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]
    simp [w, l, map_sum, map_smul]
  have hexp : ∀ (T : C) (z : Om R (F.obj T) 2), z = ∑ i, ∑ j ∈ Finset.Ioi i,
      L2 (fun i ↦ Lf hP (l i) T) i j z • wedge R _ (evForm F T (w i)) (evForm F T (w j)) := by
    intro T z
    conv_lhs => rw [expand (fun i ↦ evForm F T (w i)) (fun i ↦ Lf hP (l i) T)
      (Lf_expand hP w l hdual T) z]
    simp only [wb_apply, wedge_eq_ιMulti]
  refine ⟨nu F, nu_ιMulti F, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have h0 : ∀ i j, L2 l i j t = 0 := by
      intro i j
      apply hS.2
      rw [map_zero]
      funext T
      have := wedge_functional_constant_on_image hP l i j T t
      rw [ht] at this
      simpa using this.symm
    rw [expand w l hdual t]
    simp [h0]
  · intro u hu
    have hc : ∀ i j, ∃ r : R, ∀ T, algebraMap R (F.obj T) r = L2 (fun i ↦ Lf hP (l i) T) i j (u T) := by
      intro i j
      have hz : d0 F (fun T ↦ L2 (fun i ↦ Lf hP (l i) T) i j (u T)) = 0 := by
        funext T T' φ
        rw [amitsur_d0_apply, hu T T' φ, wedge_functional_two_form_naturality, sub_self]
        rfl
      obtain ⟨r, hr⟩ := (hS.1 _).1 hz
      exact ⟨r, fun T ↦ congrFun hr T⟩
    choose r hr using hc
    refine ⟨∑ i, ∑ j ∈ Finset.Ioi i, r i j • wb (A := R) (w i) (w j), ?_⟩
    funext T
    conv_rhs => rw [hexp T (u T)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, wb_apply, nu_ιMulti]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hr, algebraMap_smul]
    rfl
end GlobalTheory.CompanionTheory.HodgeTwoForm
