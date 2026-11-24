-- Prove2me | solution 1 for GlobalTheory.SymbolOne.word_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:09.545364+00:00
-- url     : https://prove2.me/submissions/effd2b02-233c-473c-a6a9-a26ee94a817d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Theorems.Thm_GlobalTheory_SymbolOne_word_mem
import Theorems.Thm_GlobalTheory_SymbolOne_word_add
import Theorems.Thm_GlobalTheory_SymbolOne_word_smul
import Theorems.Thm_GlobalTheory_SymbolOne_sum_update_pred
import Theorems.Thm_GlobalTheory_SymbolOne_deriv_prod_pow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolOne
variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SymbolOne
theorem _root_.solution (π : A →ₐ[k] k) (D : ι → Derivation k A A) (lam : ι → A)
    (hlam : ∀ l, π (lam l) = 0) (α : ι → k) (w : List ι) (a : ι → ℕ) (E : A)
    (hD : ∀ l l', a l ≠ 0 → l' ∈ w → π (D l' (lam l)) = if l = l' then α l else 0)
    (hw : w.length ≤ ∑ l, a l) :
    π (w.foldl (fun g l => D l g) ((∏ l, lam l ^ a l) * E)) =
      if (∀ l, w.count l = a l) then (∏ l, ((a l).factorial : k) * α l ^ a l) * π E else 0 := by
  induction w generalizing a with
  | nil =>
    simp only [List.foldl_nil, map_mul, map_prod, map_pow, hlam]
    by_cases h : ∀ l, ([] : List ι).count l = a l
    · rw [if_pos h]
      simp [← h]
    · rw [if_neg h]
      simp only [List.count_nil] at h
      push Not at h
      obtain ⟨l, hl⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ l) (zero_pow hl.symm), zero_mul]
  | cons l₀ w ih =>
    set I : Ideal A := RingHom.ker π
    have key := deriv_prod_pow_mul (D l₀) I lam hlam a l₀ (α l₀) (fun l hl => by
      rw [RingHom.mem_ker, map_sub, hD l l₀ hl List.mem_cons_self, AlgHom.commutes]
      split_ifs with h
      · simp [h]
      · simp) E
    have key2 := word_mem D I w _ (Ideal.pow_le_pow_right (by simpa using hw) key)
    rw [RingHom.mem_ker] at key2
    rw [List.foldl_cons, ← sub_add_cancel (D l₀ _) (((a l₀ : k) * α l₀) •
      ((∏ l, lam l ^ Function.update a l₀ (a l₀ - 1) l) * E)), word_add, map_add, key2, zero_add,
      word_smul, map_smul]
    by_cases h0 : a l₀ = 0
    · rw [if_neg]
      · simp [h0]
      · intro h
        have := h l₀
        simp [h0] at this
    · have hs := sum_update_pred a l₀ h0
      rw [ih (Function.update a l₀ (a l₀ - 1))]
      · have hiff : (∀ l, w.count l = Function.update a l₀ (a l₀ - 1) l) ↔
            ∀ l, (l₀ :: w).count l = a l := by
          refine forall_congr' fun l => ?_
          by_cases hl : l = l₀
          · subst hl
            simp only [Function.update_self, List.count_cons_self]
            omega
          · rw [Function.update_of_ne hl, List.count_cons_of_ne (Ne.symm hl)]
        simp only [hiff]
        split_ifs with h
        · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l₀),
            ← Finset.mul_prod_erase _ (fun l => ((a l).factorial : k) * α l ^ a l) (Finset.mem_univ l₀),
            Function.update_self]
          have : ∏ l ∈ Finset.univ.erase l₀, (((Function.update a l₀ (a l₀ - 1) l).factorial : k) *
              α l ^ Function.update a l₀ (a l₀ - 1) l) =
              ∏ l ∈ Finset.univ.erase l₀, (((a l).factorial : k) * α l ^ a l) :=
            Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
          rw [this]
          obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
          rw [hn, smul_eq_mul]
          simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.factorial_succ]
          push_cast
          ring
        · simp
      · intro l l' hl hl'
        refine hD l l' ?_ (List.mem_cons_of_mem _ hl')
        by_cases h : l = l₀
        · rw [h]; exact h0
        · rwa [Function.update_of_ne h] at hl
      · simp only [List.length_cons] at hw
        omega
end GlobalTheory.SymbolOne
