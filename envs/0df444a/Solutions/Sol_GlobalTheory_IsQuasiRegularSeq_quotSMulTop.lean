-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:00.454599+00:00
-- url     : https://prove2.me/submissions/5098bc52-33c6-4fde-887d-6f77b5486608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_mem_pow_smul_of_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : Option ι → R} (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (QuotSMulTop (f none) M) (f ∘ some) := by
  have hJI : Ideal.span (Set.range (f ∘ some)) ≤ Ideal.span (Set.range f) :=
    Ideal.span_mono (Set.range_comp_subset_range _ _)
  have hI : ∀ m : M, m ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) →
      (Submodule.Quotient.mk m : QuotSMulTop (f none) M) ∈
        (Ideal.span (Set.range (f ∘ some)) • ⊤ : Submodule R (QuotSMulTop (f none) M)) := by
    intro m hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr n _
      rw [Submodule.Quotient.mk_smul]
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨_ | i, rfl⟩ := hr
        · rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr
            (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)]
          exact zero_mem _
        · exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) trivial
      | zero => simp
      | add r s _ _ hr hs => rw [add_smul]; exact add_mem hr hs
      | smul t r _ hr => rw [smul_assoc]; exact Submodule.smul_mem _ _ hr
    · intro x y hx hy
      rw [Submodule.Quotient.mk_add]
      exact add_mem hx hy
  rw [isQuasiRegularSeq_iff_eq_zero]
  intro a c hc β
  choose d hd using fun α => Submodule.Quotient.mk_surjective _ (c α)
  obtain rfl : c = fun α => Submodule.Quotient.mk (d α) := funext fun α => (hd α).symm
  have hc' : (Submodule.Quotient.mk (∑ α, monoVal (f ∘ some) α.1 • d α) :
      QuotSMulTop (f none) M) = 0 := by
    rw [← hc, ← Submodule.mkQ_apply, map_sum]
    rfl
  obtain ⟨ω, -, hω⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hc')
  cases a with
  | zero =>
    have hs : ∀ β : MonoDeg ι 0, β.1 = 0 := fun β => (Finsupp.degree_eq_zero_iff _).mp β.2
    rw [Finset.sum_eq_single β (fun γ _ hγ => absurd (Subtype.ext ((hs γ).trans (hs β).symm)) hγ)
      (by simp), hs β, monoVal_zero, one_smul] at hc
    rw [hc]
    exact zero_mem _
  | succ a =>
    have h1 : ω ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
      refine h.mem_pow_smul_of_smul_mem none ?_
      rw [hω]
      exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI _)
        ((mem_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩)
    obtain ⟨g, rfl⟩ := (mem_pow_smul_top_iff f a ω).mp h1
    let e := MonoDeg.optionEquiv ι a
    have he₁ : ∀ β : MonoDeg ι (a + 1), e.symm β.toOption = Sum.inl β :=
      fun β => e.symm_apply_apply (Sum.inl β)
    have he₂ : ∀ γ : MonoDeg (Option ι) a, e.symm (MonoDeg.mulVar none γ) = Sum.inr γ :=
      fun γ => e.symm_apply_apply (Sum.inr γ)
    have := (isQuasiRegularSeq_iff_eq_zero f).mp h (a + 1) (fun α => Sum.elim d (-g) (e.symm α))
      (by
        rw [sum_monoVal_smul_option]
        simp only [he₁, he₂, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, smul_neg,
          Finset.sum_neg_distrib, hω, add_neg_cancel]) β.toOption
    rw [he₁] at this
    exact hI _ this
end IsQuasiRegularSeq
end GlobalTheory
