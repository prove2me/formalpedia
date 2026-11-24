-- Prove2me | solution 1 for GlobalTheory.RegBound.exists_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:13:59.021025+00:00
-- url     : https://prove2.me/submissions/88a013b6-41d7-4a3c-a0e4-359ca50a29e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_comp_succ_mul
import Theorems.Thm_GlobalTheory_RegBound_eventually_mem_of_X_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution [Finite σ] {J : Ideal (MvPolynomial σ K)}
    (hJ : ∀ F ∈ J, ∀ e, homogeneousComponent e F ∈ J) :
    ∃ J' : Ideal (MvPolynomial σ K), J ≤ J' ∧ (∀ F ∈ J', ∀ e, homogeneousComponent e F ∈ J') ∧
      (∀ F, (∀ i, X i * F ∈ J') → F ∈ J') ∧
      ∀ᶠ e in atTop, ∀ F ∈ J', F.IsHomogeneous e → F ∈ J := by
  obtain ⟨J', ⟨h1, h2, h3⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2
    (inferInstance : IsNoetherian (MvPolynomial σ K) (MvPolynomial σ K)))
    {J' | J ≤ J' ∧ (∀ F ∈ J', ∀ e, homogeneousComponent e F ∈ J') ∧
      ∀ᶠ e in atTop, ∀ F ∈ J', F.IsHomogeneous e → F ∈ J}
    ⟨J, le_rfl, hJ, Eventually.of_forall fun _ _ h _ => h⟩
  refine ⟨J', h1, h2, ?_, h3⟩
  let L : Ideal (MvPolynomial σ K) :=
    { carrier := {F | ∀ i, X i * F ∈ J'}
      add_mem' := fun ha hb i => by rw [mul_add]; exact J'.add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c x hx i => by
        rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left J' _ (hx i) }
  have hle : J' ≤ L := fun F hF i => Ideal.mul_mem_left J' _ hF
  have hL := hmax L ⟨h1.trans hle, fun F hF e i => by
      rw [← comp_succ_mul (isHomogeneous_X K i)]; exact h2 _ (hF i) _, by
      filter_upwards [h3, eventually_mem_of_X_mul (L := L) h2 fun F hF => hF] with e a b F hF hFe
      exact a F (b F hF hFe) hFe⟩
  have : J' = L := by
    by_contra hne
    exact hL (lt_of_le_of_ne hle hne)
  intro F hF
  rw [this]; exact hF
end GlobalTheory.RegBound
