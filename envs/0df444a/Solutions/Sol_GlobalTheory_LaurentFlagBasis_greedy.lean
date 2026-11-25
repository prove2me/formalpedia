-- Prove2me | solution 1 for GlobalTheory.LaurentFlagBasis.greedy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:47.016504+00:00
-- url     : https://prove2.me/submissions/db8cbba3-b62b-41d6-8573-404631730bdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
import Theorems.Thm_GlobalTheory_LaurentFlagBasis_exists_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory GlobalTheory.LaurentFlagBasis
variable {F : Type} [Field F]
namespace GlobalTheory.LaurentFlagBasis
theorem _root_.solution {n : ℕ} (V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j)) :
    ∀ m, m ≤ n → ∃ c : Fin m → (Fin n → PowerSeries F), (∀ j : Fin m, lift (c j) ∈ V j) ∧
      LinearIndependent F (fun j => red (c j))
  | 0, _ => ⟨Fin.elim0, fun j => j.elim0, linearIndependent_empty_type⟩
  | m+1, hm => by
    obtain ⟨c, hcV, hci⟩ := solution V hV m (by omega)
    obtain ⟨y, hyV, hyi⟩ := exists_indep (Module.finrank (LaurentSeries F) (V m)) (V m) le_rfl
    have : ∃ b, red (y b) ∉ Submodule.span F (Set.range fun j => red (c j)) := by
      by_contra h; push_neg at h
      have h1 : Submodule.span F (Set.range fun b => red (y b)) ≤
          Submodule.span F (Set.range fun j => red (c j)) :=
        Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact h b)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hyi, finrank_span_eq_card hci] at h2
      simp at h2
      have := hV m (by omega)
      omega
    obtain ⟨b, hb⟩ := this
    refine ⟨Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b), ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]; exact hyV b
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]; exact hcV j
    · have e : (fun j => red ((Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b)) j)) =
          Fin.snoc (α := fun _ => Fin n → F) (fun j => red (c j)) (red (y b)) := by
        ext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      rw [e, linearIndependent_finSnoc]
      exact ⟨hci, hb⟩
end GlobalTheory.LaurentFlagBasis
