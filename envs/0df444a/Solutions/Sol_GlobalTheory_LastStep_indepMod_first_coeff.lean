-- Prove2me | solution 1 for GlobalTheory.LastStep.indepMod_first_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:58.215359+00:00
-- url     : https://prove2.me/submissions/666a3905-ef1e-4fa3-8c43-a8c1b387d212

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IndependentModFirstCoeffChainLastStep
import Theorems.Thm_GlobalTheory_LastStep_mm_mul_int
import Theorems.Thm_GlobalTheory_LastStep_mm_sum
import Theorems.Thm_GlobalTheory_LastStep_mm_of_tan
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_comb
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_alt_step
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_parity_of_alt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_GlobalTheory_FrobRoot_ge_of_pow
import Theorems.Thm_GlobalTheory_FrobRoot_mm_add
import Theorems.Thm_GlobalTheory_FrobRoot_mm_pow
import Theorems.Thm_GlobalTheory_FrobRoot_mm_sum_pow
import Theorems.Thm_GlobalTheory_LeafTerm_Adapted_good
import Theorems.Thm_GlobalTheory_MainTerm_l_mul_be_one_int
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_Cart_c0__comb_22429d26040d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot
open GlobalTheory GlobalTheory.LastStep
namespace GlobalTheory.LastStep
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  intro C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum
  haveI := X.algClosed
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)
  have hr0 : ∀ δ, V.Ge 0 (r δ) := fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)
  set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw
  have hw0 : ∀ c, V.Ge 0 (w c) := fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)
  set T := Finset.univ.filter (fun c => D.lev c = s) with hT
  have hbig : X.big g (a + ((2 * s : ℕ) : ZMod d)) :=
    (S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)
  have hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 : D.lev c = s := (Finset.mem_filter.1 hc).2
    have h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i := h1 ▸ hs
    have h3 := hD.2.2.2.2 c h2
    rw [h1] at h3
    rw [← h3]
    exact hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))
  have hG := Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood
  have hR := X.R2 hA g _ hbig _ _ hG (by
    intro κ
    rw [Cart.c0'_comb]
    have h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ)) := by
      refine mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)
      have := mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))
      simpa only [pow_one] using this
    have h2 := mm_add h1 (hsum κ)
    convert h2 using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
    rfl)
  have hwm : ∀ c, V.MM (if D.lev c = s then w c else 0) := by
    refine mm_of_tan S _ fun k => ?_
    convert hR k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]
  intro δ
  rw [← hr δ]
  refine mm_pow (hind r hr0 (fun c => ?_) δ) hl
  convert hwm c using 1
  by_cases hc : D.lev c = s <;> simp [hw, hc]
end GlobalTheory.LastStep
