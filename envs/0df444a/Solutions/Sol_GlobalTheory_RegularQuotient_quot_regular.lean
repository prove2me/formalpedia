-- Prove2me | solution 1 for GlobalTheory.RegularQuotient.quot_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:36.688811+00:00
-- url     : https://prove2.me/submissions/1d268b79-13cf-4e8a-acf4-f07a5596f1f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientSpanRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.RegularQuotient
open IsLocalRing Matrix
namespace GlobalTheory.RegularQuotient
namespace _root_.GlobalTheory.RegularQuotient
theorem _root_.solution (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (t : ι → Λ) (z : κ → Λ)
    (hs : Ideal.span (Set.range t ∪ Set.range z) = maximalIdeal Λ)
    (hd : ringKrullDim Λ = ((Fintype.card ι + Fintype.card κ : ℕ) : ℕ)) :
    ∃ _ : IsRegularLocalRing (Λ ⧸ Ideal.span (Set.range z)),
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range z))) (maximalIdeal Λ) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range z)) (t i)) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      ringKrullDim (Λ ⧸ Ideal.span (Set.range z)) = (Fintype.card ι : ℕ) := by
  set I := Ideal.span (Set.range z) with hIdef
  have hIm : I ≤ maximalIdeal Λ := by
    rw [Ideal.span_le, ← hs]
    exact (Set.subset_union_right).trans Ideal.subset_span
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal Λ).ne_top hIm
  haveI : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (Λ ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal Λ) = maximalIdeal (Λ ⧸ I) := by
    have hc : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (Λ ⧸ I)) = maximalIdeal Λ :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (t i)) =
      maximalIdeal (Λ ⧸ I) := by
    rw [← hmap, ← hs, Ideal.span_union, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hgen : ((maximalIdeal (Λ ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (Fintype.card ι : ℕ) := by
    rw [← hspan]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (t i))
    have h' : (Set.range fun i => Ideal.Quotient.mk I (t i)).ncard ≤ Fintype.card ι := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hle : ringKrullDim (Λ ⧸ I) ≤ (Fintype.card ι : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans hgen
  have hI : (I.spanFinrank : WithBot ℕ∞) ≤ (Fintype.card κ : ℕ) := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ) (Set.finite_range z)
    have h' : (Set.range z).ncard ≤ Fintype.card κ := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hge := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)
  rw [hd] at hge
  have h1 : ((Fintype.card ι + Fintype.card κ : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Λ ⧸ I) + (Fintype.card κ : ℕ) :=
    hge.trans (add_le_add le_rfl hI)
  have hdim : ringKrullDim (Λ ⧸ I) = (Fintype.card ι : ℕ) := by
    generalize ringKrullDim (Λ ⧸ I) = e at h1 hle ⊢
    induction e using WithBot.recBotCoe with
    | bot => simp at h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (by exact_mod_cast (not_le.mpr (ENat.coe_lt_top _)))
      | coe n =>
        norm_cast at h1 hle ⊢
        omega
  exact ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hgen.trans hdim.ge), hmap, hspan,
    hdim⟩
end _root_.GlobalTheory.RegularQuotient
end GlobalTheory.RegularQuotient
