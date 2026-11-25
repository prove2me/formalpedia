-- Prove2me | solution 1 for GlobalTheory.CycEigen.twAct_fixed_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:42.127958+00:00
-- url     : https://prove2.me/submissions/91a39575-805f-44d3-a0b4-4b6ddd9264ce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Theorems.Thm_GlobalTheory_CycEigen_mulVec_mem
import Theorems.Thm_GlobalTheory_CycEigen_map_mulVec
import Theorems.Thm_GlobalTheory_CycEigen_eq_zero_of_small
import Theorems.Thm_GlobalTheory_CycEigen_rho_lt_one
import Theorems.Thm_GlobalTheory_CycEigen_norm_root_sub_one
import Theorems.Thm_GlobalTheory_CycEigen_mem_inC_iff
import Theorems.Thm_GlobalTheory_CycEigen_root_mem_inC
import Theorems.Thm_GlobalTheory_CycEigen_exists_quot
import Theorems.Thm_GlobalTheory_CycEigen_twAct_sub
import Theorems.Thm_GlobalTheory_CycEigen_act_inC
import Theorems.Thm_GlobalTheory_CycEigen_ohat_norm
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
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {j : ℕ} (hj : Lev l j)
    {g : GQ l} (hg : IsGen χ K j g) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (hU : ∀ a b, U g a b ∈ intC (Ks K j)) (hU1 : ∀ a b, ‖(U g - 1) a b‖ < rho1 l) (i : ℤ)
    (y : Fin r → PadicComplex l) (hy : ∀ a, y a ∈ Xj K j) (hfix : twAct act χ i U g y = y) :
    y = 0 := by
  obtain ⟨-, -, hO, hmul, hstab, -⟩ :=
    GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K j hj.1
  have hg0 : g ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (le_sup_left : K0 K ≤ Ks K j) hg.1
  have hgX := hstab g hg0
  haveI : NeZero l := ⟨hl.1.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicComplex l) l
  obtain ⟨S, hS, hadd, hlin⟩ := GlobalTheory.Cyc.exists_tate_operator l act χ hact hχ K j hj g hg ζ hζ
  obtain ⟨B, c, hc0, hc1, hB, hBO, hBe⟩ := exists_quot hj hg (U g) hU hU1 i hζ
  have hBO' : ∀ a b, (-B) a b ∈ intC (Ks K j) := fun a b =>
    ⟨(mem_inC_iff _ _).2 (neg_mem ((mem_inC_iff _ _).1 (hBO a b).1)), by
      rw [Matrix.neg_apply, norm_neg]; exact (hBO a b).2⟩
  have hp : ζ - 1 ∈ intC (Ks K j) :=
    ⟨(mem_inC_iff _ _).2 (sub_mem ((mem_inC_iff _ _).1 (root_mem_inC K hj.1 hζ)) (one_mem _)), by
      rw [norm_root_sub_one hζ]; exact rho_lt_one.le⟩
  have hp0 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one hl.1.one_lt)
  refine eq_zero_of_small (Xj K j) (fun x hx => ohat_norm K (hO x hx)) _ hmul
    (fun x => S (act g x)) (fun x hx => (hS _ (hgX x hx)).1)
    (fun x hx x' hx' => by rw [map_add, hadd _ (hgX x hx) _ (hgX x' hx')])
    (fun o ho x hx => by rw [map_mul, act_inC hact hg.1 ho.1, hlin _ ho _ (hgX x hx)])
    (-B) hBO' hc0 hc1 (fun a b => by rw [Matrix.neg_apply, norm_neg]; exact hB a b) y hy ?_
  rw [← map_mulVec (Xj K j) _ hmul S hadd hlin (-B) hBO' _ fun a => hgX _ (hy a)]
  funext a
  have h1 : act g (y a) - y a = (ζ - 1) * (-B).mulVec (fun b => act g (y b)) a := by
    have := twAct_sub (act := act) hBe y a
    rw [hfix, sub_self, Pi.zero_apply] at this
    rw [Matrix.neg_mulVec, Pi.neg_apply]
    linear_combination -this
  have h2 := (hS _ (hy a)).2.2
  rw [h1, hlin _ hp _ (mulVec_mem (Xj K j) (-B) (fun a b => hmul _ (hBO' a b)) _
    (fun b => hgX _ (hy b)) a)] at h2
  exact (mul_left_cancel₀ hp0 h2).symm
end GlobalTheory.CycEigen
