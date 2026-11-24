-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.card_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:30:43.023151+00:00
-- url     : https://prove2.me/submissions/72579c1b-b0af-446f-86c4-00a18f11a655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
import Theorems.Thm_GlobalTheory_HermitianGauss_sum_char
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
variable {σ : R →+* R} {β : M → M → ℂ}
namespace GlobalTheory.HermitianGauss
theorem _root_.solution (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    {B C N N' : Submodule R M} (hCN : C ≤ N) (hNB : N ≤ B) (hrad : ∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1)
    (hN' : ∀ x, x ∈ N' ↔ x ∈ B ∧ ∀ y ∈ N, β x y = 1) :
    (pts C).card * (pts B).card = (pts N').card * (pts N).card := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have e1 : ∀ y ∈ pts B, ∑ z ∈ pts N, β y z =
      if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0 := fun y _ => sum_char N (β y) (hr y)
  have h1 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts N').card : ℂ) * (pts N).card := by
    rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
    have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by
      ext y
      simp [pts, hN']
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∀ z ∈ pts N, ∑ y ∈ pts B, β y z =
      if ∀ y ∈ B, β y z = 1 then ((pts B).card : ℂ) else 0 := fun z _ =>
    sum_char B (fun y => β y z) (fun a b => hadd a b z)
  have h2 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts C).card : ℂ) * (pts B).card := by
    rw [Finset.sum_comm, Finset.sum_congr rfl e2, ← Finset.sum_filter]
    have hf : (pts N).filter (fun z => ∀ y ∈ B, β y z = 1) = pts C := by
      ext z
      simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hz, h⟩
        exact (hrad z (hNB hz)).mpr fun y hy => by rw [hsym]; exact h y hy
      · intro hz
        exact ⟨hCN hz, fun y hy => by rw [hsym]; exact (hrad z (hNB (hCN hz))).mp hz y hy⟩
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  exact_mod_cast h2.symm.trans h1
end GlobalTheory.HermitianGauss
