-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:01.577906+00:00
-- url     : https://prove2.me/submissions/7ced2818-3da8-4c6f-96b9-12a04a085664

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_fock_eq_sum
import Theorems.Thm_GlobalTheory_MinorNorm_fock_det_mul
import Theorems.Thm_GlobalTheory_MinorNorm_det_X_ne_zero
import Theorems.Thm_GlobalTheory_MinorNorm_partition_induction
import Theorems.Thm_GlobalTheory_MinorNorm_hookProd_zero
import Theorems.Thm_GlobalTheory_MinorNorm_addCol_antitone
import Theorems.Thm_GlobalTheory_MinorNorm_hookProd_addCol
import Theorems.Thm_GlobalTheory_MinorNorm_prod_ite_le
import Theorems.Thm_GlobalTheory_MinorNorm_del_zero
import Theorems.Thm_GlobalTheory_MinorNorm_del_addCol
import Theorems.Thm_GlobalTheory_MinorNorm_pol_del

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
theorem _root_.solution (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) (a : Fin l → ℕ)
    (ha : Antitone a) : Formalism.E.fock (del v a) (del v a) = ((hookProd a : ℚ) : ℂ) := by
  classical
  refine partition_induction (fun a => Formalism.E.fock (del v a) (del v a) = ((hookProd a : ℚ) : ℂ))
    ?_ ?_ a ha
  · simp only [del_zero, hookProd_zero]
    rw [fock_eq_sum _ _ {0} (by rw [← C_1, C_apply]; exact support_monomial_subset)]
    simp [Formalism.A.mfact]
  · intro a K ha hK ih
    have hv' : ∀ r c s e : Fin (K + 1), v (Fin.castLE K.2 r) (Fin.castLE K.2 c) =
        v (Fin.castLE K.2 s) (Fin.castLE K.2 e) → r = s ∧ c = e := by
      intro r c s e h
      obtain ⟨h1, h2⟩ := hv _ _ _ _ h
      exact ⟨Fin.castLE_injective _ h1, Fin.castLE_injective _ h2⟩
    have h0 : ∀ t : Fin l, (K : ℕ) + 1 ≤ t → addCol a K t = 0 := by
      intro t ht
      have : K < t := ht
      simp [addCol, hK t this, not_le.mpr this]
    have h := fock_det_mul (fun r c : Fin (K + 1) => v (Fin.castLE K.2 r) (Fin.castLE K.2 c)) hv'
      (fun t => addCol a K (Fin.castLE K.2 t)) (del v a) (del v (addCol a K)) (del_addCol v ha K)
      (det_X_ne_zero _ hv')
      (fun i j hij => by
        rw [pol_del hv K.2 i j hij.le _ (addCol_antitone ha K) h0, if_neg hij.ne]; simp)
      (fun j => by rw [pol_del hv K.2 j j le_rfl _ (addCol_antitone ha K) h0, if_pos rfl])
    rw [h, ih, hookProd_addCol ha K hK, prod_ite_le]
    push_cast
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    have ht : Fin.castLE K.2 t ≤ K := by
      have := t.2
      simp only [Fin.le_def, Fin.val_castLE]
      omega
    simp only [addCol, ht, if_true, Fin.val_castLE]
    rw [Nat.cast_sub (show (t : ℕ) ≤ K from ht)]
    push_cast
    ring
end GlobalTheory.MinorNorm
