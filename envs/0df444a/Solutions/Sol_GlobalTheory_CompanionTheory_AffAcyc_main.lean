-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:22.123865+00:00
-- url     : https://prove2.me/submissions/5c1df1f3-a358-4066-bda6-8572adc1122d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_res_bij
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_z_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_z_cocycle
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution : CxSt → HtpySt → AffAcycSt := by
  intro hC hH R _ X s W P _ _ u hle hinf hcov F aug
  refine ⟨?_, fun z ↦ ⟨fun hz ↦ ?_, ?_⟩, fun n z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · refine (injective_iff_map_eq_zero aug).2 fun b hb ↦ ?_
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun a ↦ (u a).1) W.1 (fun a ↦ homOfLE (hle a))
      hcov.ge b 0 fun a ↦ ?_
    exact (congrFun hb ((Functor.const (Fin 1)).obj (op a))).trans (map_zero _).symm
  · obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun a ↦ (u a).1) W.1
      (fun a ↦ homOfLE (hle a)) hcov.ge (fun a ↦ z ((Functor.const (Fin 1)).obj (op a))) (by
        intro i j
        have e := hinf i j
        refine (res_bij s (le_of_eq e) e.symm).1 ?_
        have l := z_cocycle F z hz (homOfLE (inf_le_left : i ⊓ j ≤ i)).op
        have r := z_cocycle F z hz (homOfLE (inf_le_right : i ⊓ j ≤ j)).op
        exact ((Sec.res_res s inf_le_left (le_of_eq e) _).symm.trans l).trans
          ((Sec.res_res s inf_le_right (le_of_eq e) _).symm.trans r).symm)
    refine ⟨t, funext fun c ↦ ?_⟩
    exact (ht (c.obj (Fin.last 0)).unop).trans (z_eq F z c).symm
  · rintro ⟨b, rfl⟩
    funext c
    have h : ∀ (T T' : Pᵒᵖ) (φ : T ⟶ T'), mp F φ (Sec.res s (hle T.unop) b) = Sec.res s (hle T'.unop) b :=
      fun T T' φ ↦ (Sec.res_res _ _ _ b).symm
    rw [dn_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
    exact add_neg_eq_zero.2 ((h _ _ _).trans (h _ _ _).symm)
  · exact pos s W u hle hC hH hinf hcov n z hz
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun ((hC R Pᵒᵖ F).1 n) y
end GlobalTheory.CompanionTheory.AffAcyc
