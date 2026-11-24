-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:09:30.432195+00:00
-- url     : https://prove2.me/submissions/f86ca4f6-198c-44b1-b119-8bfc7382ecc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_pr_zero_right
import Theorems.Thm_GlobalTheory_SW_Vac_ex_add
import Theorems.Thm_GlobalTheory_SW_Vac_ex_zero
import Theorems.Thm_GlobalTheory_SW_Vac_exists_ex_of_pow
import Theorems.Thm_GlobalTheory_SW_Vac_exists_graph
import Theorems.Thm_GlobalTheory_SW_Vac_fg_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ))
    (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) (hA : A.FG)
    (hε : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2))
    {m : ℕ} (hm : 0 < m) (hm' : ∀ y ∈ A, ε (m • y) = 1) :
    ∃ x₀, ∀ a, (a, 0) ∈ A → ε (a, 0) * ex (2 * pr x₀ a) = 1 := by
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  have hadd : ∀ a a', (a, 0) ∈ A → (a', 0) ∈ A → ε (a + a', 0) = ε (a, 0) * ε (a', 0) := by
    intro a a' h h'
    simpa [pr_zero_right, ex_zero] using hε _ h _ h'
  let Γ : AddSubgroup (Matrix κ ι ℚ × ℚ) :=
    { carrier := {p | (p.1, 0) ∈ A ∧ ε (p.1, 0) * ex (2 * p.2) = 1}
      zero_mem' := ⟨A.zero_mem, by
        have : ε (0, 0) = 1 := h0
        simp [this, ex_zero]⟩
      add_mem' := by
        rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
        refine ⟨by simpa using A.add_mem hp hq, ?_⟩
        rw [Prod.fst_add, Prod.snd_add, hadd _ _ hp hq, mul_add, ex_add, mul_mul_mul_comm, hp', hq',
          one_mul]
      neg_mem' := by
        rintro p ⟨hp, hp'⟩
        have hn : (-p.1, 0) ∈ A := by simpa using A.neg_mem hp
        refine ⟨hn, ?_⟩
        have h1 := hadd _ _ hp hn
        have h2 := ex_add (2 * p.2) (2 * -p.2)
        rw [add_neg_cancel] at h1
        have h3 : ε (0, 0) = 1 := h0
        rw [h3] at h1
        rw [show 2 * p.2 + 2 * -p.2 = 0 by ring, ex_zero] at h2
        change ε (-p.1, 0) * ex (2 * -p.2) = 1
        calc _ = (ε (p.1, 0) * ex (2 * p.2)) * (ε (-p.1, 0) * ex (2 * -p.2)) := by
              rw [hp', one_mul]
          _ = 1 := by rw [mul_mul_mul_comm, ← h1, ← h2, one_mul] }
  obtain ⟨x, hx⟩ := exists_graph Γ (A.map (AddMonoidHom.fst _ _)) (fg_map hA _)
    (fun p hp => ⟨_, hp.1, rfl⟩)
  refine ⟨x, fun a ha => ?_⟩
  have hpow : ∀ n : ℕ, ε (n • a, 0) = ε (a, 0) ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact h0
    | succ n ih =>
      rw [succ_nsmul, hadd _ _ (by simpa using A.nsmul_mem ha n) ha, ih, pow_succ]
  have : ε (a, 0) ^ m = 1 := by
    rw [← hpow]; simpa using hm' _ ha
  obtain ⟨r, hr⟩ := exists_ex_of_pow hm this
  exact (hx (a, r) ⟨ha, hr⟩).2
end GlobalTheory.SW.Vac
