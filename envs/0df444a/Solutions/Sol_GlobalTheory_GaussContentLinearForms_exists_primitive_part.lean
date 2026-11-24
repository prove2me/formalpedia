-- Prove2me | solution 1 for GlobalTheory.GaussContentLinearForms.exists_primitive_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:59.343247+00:00
-- url     : https://prove2.me/submissions/5d123d66-b0db-475b-aaeb-82e911bdedf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_C_mul
import Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.GaussContentLinearForms
variable {V : Type} [CommRing V] {σ : Type}
namespace GlobalTheory.GaussContentLinearForms
theorem _root_.solution [IsDomain V] [IsDiscreteValuationRing V] (f : MvPolynomial σ V) :
    ∃ (a : V) (g : MvPolynomial σ V), f = C a * g ∧
      Ideal.span (Set.range fun s => g.coeff s) = ⊤ := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span (Set.range fun s => f.coeff s))).principal
  have ha' : Ideal.span (Set.range fun s => f.coeff s) = Ideal.span {a} := ha
  have hd : C a ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro s
    rw [← Ideal.mem_span_singleton, ← ha']
    exact Ideal.subset_span ⟨s, rfl⟩
  obtain ⟨g, rfl⟩ := hd
  by_cases h0 : a = 0
  · exact ⟨0, 1, by simp [h0], span_coeff_one⟩
  · refine ⟨a, g, rfl, ?_⟩
    rw [span_coeff_C_mul] at ha'
    have hne : Ideal.span {a} ≠ (0 : Ideal V) := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact h0
    apply mul_left_cancel₀ hne
    rw [ha', Ideal.mul_top]
end GlobalTheory.GaussContentLinearForms
