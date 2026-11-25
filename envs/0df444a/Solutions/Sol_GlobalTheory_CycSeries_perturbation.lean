-- Prove2me | solution 1 for GlobalTheory.CycSeries.perturbation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:25.117077+00:00
-- url     : https://prove2.me/submissions/721f4404-4f42-4538-add7-c6cacb5c5bca

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Theorems.Thm_GlobalTheory_CycSeries_inj_of_small
import Theorems.Thm_GlobalTheory_CycSeries_surj_of_small
import Theorems.Thm_GlobalTheory_CycSeries_exists_quot
import Theorems.Thm_GlobalTheory_CycSeries_twAct_sub
import Theorems.Thm_GlobalTheory_CycSeries_mul_mem_intC
import Theorems.Thm_GlobalTheory_CycSeries_exists_factor
import Theorems.Thm_GlobalTheory_CycSeries_norm_le_one_of_Ohat
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix
import Theorems.Thm_GlobalTheory_Cyc_TateS_zeta_sub_one_mem
import Theorems.Thm_GlobalTheory_Cyc_exists_tate_operator
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycSeries
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycSeries
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  intro l hl act χ hact hχ K j hj g hg r U hU hU1 i
  obtain ⟨-, -, hXO, hmul, hstab, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ hact hχ K j hj.1
  have hX1 : ∀ x ∈ Xj K j, ‖x‖ ≤ 1 := fun x hx => norm_le_one_of_Ohat K (hXO x hx)
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  constructor
  · intro y hy hfix
    have : NeZero l := ⟨hl.1.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
    obtain ⟨S, hS, -, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨q, B', hq0, hq1, hqO, hB', rfl⟩ := exists_factor B hB hBO
    rw [smul_smul] at hBe
    refine inj_of_small (Xj K j) hX1 (act g) hgX (ζ - 1) q
      (sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)) hq0 hq1 (TateS.act_fix hact K hg.1 hqO.1) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩)
      (hlin _ (mul_mem_intC (TateS.zeta_sub_one_mem K hj.1 hζ) hqO))
      B' (fun a b => hmul _ (hB' a b)) y hy fun a => ?_
    rw [← twAct_sub hBe, hfix, sub_self, Pi.zero_apply]
  · intro ζ hζ w hw
    obtain ⟨S, hS, -, -⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨q, B', hq0, hq1, hqO, hB', rfl⟩ := exists_factor B hB hBO
    rw [smul_smul] at hBe
    obtain ⟨y, hy, he⟩ := surj_of_small (Xj K j) (AddSubgroup.isClosed_topologicalClosure _) hX1
      (act g) (AddMonoidHomClass.isometry_of_norm (act g) (hact.2 g)).continuous hgX (ζ - 1) q hq1
      (TateS.act_fix hact K hg.1 hqO.1) (hmul _ hqO) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩) B' (fun a b => hmul _ (hB' a b)) w hw
    refine ⟨y, hy, funext fun a => ?_⟩
    rw [twAct_sub hBe, he, Pi.smul_apply, smul_eq_mul]
end GlobalTheory.CycSeries
