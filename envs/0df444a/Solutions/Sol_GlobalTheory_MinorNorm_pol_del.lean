-- Prove2me | solution 1 for GlobalTheory.MinorNorm.pol_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:17.064446+00:00
-- url     : https://prove2.me/submissions/af464ca8-9002-4c79-a1b9-ddcb186cf94a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_pol_minor
import Theorems.Thm_GlobalTheory_MinorNorm_partition_induction
import Theorems.Thm_GlobalTheory_MinorNorm_del_zero
import Theorems.Thm_GlobalTheory_MinorNorm_del_addCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
variable {σ : Type} (v : Fin l → Fin l → σ)
variable {v}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) {k : ℕ} (hk : k ≤ l)
    (i j : Fin k) (hij : i ≤ j) (a : Fin l → ℕ) (ha : Antitone a) :
    (∀ t : Fin l, k ≤ t → a t = 0) →
      pol (fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
        (fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) i j (del v a) =
        ((if i = j then a (Fin.castLE hk j) else 0 : ℕ) : MvPolynomial σ ℂ) * del v a := by
  classical
  have hd : ∀ r j s c, pderiv (v (Fin.castLE hk r) (Fin.castLE hk j))
      (X (v (Fin.castLE hk s) (Fin.castLE hk c)) : MvPolynomial σ ℂ) =
      if r = s ∧ j = c then 1 else 0 := by
    intro r j s c
    split_ifs with h
    · rw [h.1, h.2, pderiv_X_self]
    · refine pderiv_X_of_ne fun h' => h ?_
      obtain ⟨h1, h2⟩ := hv _ _ _ _ h'.symm
      exact ⟨Fin.castLE_injective _ h1, Fin.castLE_injective _ h2⟩
  refine partition_induction (fun a => (∀ t : Fin l, k ≤ t → a t = 0) →
      pol (fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
        (fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) i j (del v a) =
        ((if i = j then a (Fin.castLE hk j) else 0 : ℕ) : MvPolynomial σ ℂ) * del v a) ?_ ?_ a ha
  · intro _
    simp [del_zero]
  · intro a K ha _ ih h0
    have hK : (K : ℕ) + 1 ≤ k := by
      by_contra h
      have := h0 K (by omega)
      simp [addCol] at this
    have ih' := ih fun t ht => by
      have := h0 t ht
      simp only [addCol] at this
      omega
    have hm := pol_minor (x := fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
      (d := fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) hd hK i j hij
    change pol _ _ i j (minor v K) = _ * minor v K at hm
    rw [del_addCol v ha, Derivation.leibniz, ih', hm]
    simp only [addCol, smul_eq_mul, Fin.le_def, Fin.val_castLE, Nat.lt_succ_iff]
    by_cases h : i = j
    · simp only [h, true_and, if_true]
      push_cast
      ring
    · simp [h]
end GlobalTheory.MinorNorm
