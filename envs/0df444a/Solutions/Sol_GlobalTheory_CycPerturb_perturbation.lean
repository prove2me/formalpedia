-- Prove2me | solution 1 for GlobalTheory.CycPerturb.perturbation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:45.571801+00:00
-- url     : https://prove2.me/submissions/51c076ad-69b5-4975-956f-e7650e3fe02c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CycPerturb_inj_of_lattice
import Theorems.Thm_GlobalTheory_CycPerturb_surj_of_lattice
import Theorems.Thm_GlobalTheory_CycPerturb_rho_lt_one
import Theorems.Thm_GlobalTheory_CycPerturb_norm_root_sub_one
import Theorems.Thm_GlobalTheory_CycPerturb_mem_inC_iff
import Theorems.Thm_GlobalTheory_CycPerturb_root_mem_inC
import Theorems.Thm_GlobalTheory_CycPerturb_exists_quot
import Theorems.Thm_GlobalTheory_CycPerturb_twAct_sub
import Theorems.Thm_GlobalTheory_CycPerturb_mul_mem_intC
import Theorems.Thm_GlobalTheory_CycPerturb_neg_pow_mem_intC
import Theorems.Thm_GlobalTheory_CycPerturb_exists_factor
import Theorems.Thm_GlobalTheory_CycPerturb_act_fix
import Theorems.Thm_GlobalTheory_CycPerturb_norm_le_one_of_mem_Ohat
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix
import Theorems.Thm_GlobalTheory_Cyc_exists_tate_operator
import Theorems.Thm_GlobalTheory_TateDecomp_tate_decomposition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycPerturb
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  intro l hl act χ hact hχ K j hj g hg r U hU hU1 i
  obtain ⟨-, -, hO, hmul, hstab, -⟩ := GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  have hX1 : ∀ x ∈ Xj K j, ‖x‖ ≤ 1 := fun x hx => norm_le_one_of_mem_Ohat (hO x hx)
  constructor
  · intro y hy hfix
    haveI : NeZero l := ⟨hl.1.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
    obtain ⟨S, hS, -, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, c, -, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨π, B', hπO, hπ, hB'O, rfl⟩ := exists_factor B (fun a b => (hB a b).trans_lt hc1) hBO
    have hp : ζ - 1 ∈ intC (Ks K j) :=
      ⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)),
        ((norm_root_sub_one hζ).trans_lt rho_lt_one).le⟩
    refine inj_of_lattice (Xj K j) hX1 (act g) hgX (ζ - 1)
      (sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)) π hπ (act_fix hact hg.1 hπO.1) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.2⟩)
      (fun k x hx => hlin _ (mul_mem_intC hp (neg_pow_mem_intC hπO k)) x hx)
      B' (fun a b => hmul _ (hB'O a b)) y hy fun a => ?_
    rw [← twAct_sub hBe, hfix, sub_self, Pi.zero_apply]
  · intro ζ hζ w hw
    obtain ⟨S, hS, -, -⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
    obtain ⟨B, c, -, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
    obtain ⟨π, B', hπO, hπ, hB'O, rfl⟩ := exists_factor B (fun a b => (hB a b).trans_lt hc1) hBO
    obtain ⟨y, hy, he⟩ := surj_of_lattice (Xj K j) (AddSubgroup.isClosed_topologicalClosure _) hX1
      (act g) (hact.2 g) hgX (ζ - 1) π hπ (act_fix hact hg.1 hπO.1) (hmul _ hπO) S
      (fun x hx => ⟨(hS x hx).1, (hS x hx).2.1⟩) B' (fun a b => hmul _ (hB'O a b)) w hw
    refine ⟨y, hy, funext fun a => ?_⟩
    rw [twAct_sub hBe, he, Pi.smul_apply, smul_eq_mul]
end GlobalTheory.CycPerturb
