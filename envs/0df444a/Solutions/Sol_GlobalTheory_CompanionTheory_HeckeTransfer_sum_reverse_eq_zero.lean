-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.sum_reverse_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:56.182103+00:00
-- url     : https://prove2.me/submissions/de0b6101-5b16-4979-bff5-e668f5e53c77

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_word_one
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {R : Type*} [Ring R]
namespace GlobalTheory.CompanionTheory.HeckeTransfer
theorem _root_.solution {M : ℕ} (b : Fin M → R) (h : stdPoly (1 : R) b = 0) :
    ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod = 0 := by
  have h' : ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod = 0 := by
    rw [← h]
    unfold CompanionTheory.D.gk.admitted.stdPoly
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [word_one, zsmul_eq_mul]
  have hrev : ∀ f : Fin M → R, (List.ofFn f).reverse = List.ofFn fun i => f i.rev := by
    intro f
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp only [Fin.val_rev]
      simp only [List.length_reverse, List.length_ofFn] at h1
      omega
  have hsq : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) *
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  calc ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod
      = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ((Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [hrev, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, mul_comm (Equiv.Perm.sign π : ℤ),
          ← mul_assoc, hsq, one_mul]
        all_goals rfl
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod := by
        rw [Finset.smul_sum]
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulRight Fin.revPerm)
          (fun π : Equiv.Perm (Fin M) => (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod)
    _ = 0 := by rw [h', smul_zero]
end GlobalTheory.CompanionTheory.HeckeTransfer
