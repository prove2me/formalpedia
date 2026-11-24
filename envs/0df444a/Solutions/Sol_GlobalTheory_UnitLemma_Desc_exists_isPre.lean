-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.exists_isPre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:45.748855+00:00
-- url     : https://prove2.me/submissions/4df55a56-bc7c-4712-a5e5-9fdc0ca6bd02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_FieldIdem_eq_of_mul_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_FieldIdem_map
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_exists_fieldIdem_family
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isReduced_of_separable_P


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (K : UQ) (B : InvAlg K) (hP : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  have := InvAlg.isReduced_of_separable_P K B hP
  have : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  obtain ⟨M, _, f, hf, hF⟩ := exists_fieldIdem_family (R := B.A)

  have hex : ∀ m, ∃ m', B.σ (f m) = f m' := by
    intro m
    by_contra hcon
    push Not at hcon
    have hσ := (hF m).map B.σ
    have hzero : ∀ m', B.σ (f m) * f m' = 0 := fun m' => by
      by_contra h
      exact hcon m' (hσ.eq_of_mul_ne_zero (hF m') h)
    apply hσ.2.1
    calc B.σ (f m) = B.σ (f m) * 1 := (mul_one _).symm
      _ = ∑ m', B.σ (f m) * f m' := by rw [← hf.complete, Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero (fun m' _ => hzero m')
  choose τ hτ using hex
  have finj : Function.Injective f := by
    intro a b hab
    by_contra h
    apply (hF a).2.1
    calc f a = f a * f a := (hF a).1.eq.symm
      _ = f a * f b := congrArg (f a * ·) hab
      _ = 0 := hf.ortho h
  have hττ : ∀ m, τ (τ m) = m := by
    intro m
    apply finj
    calc f (τ (τ m)) = B.σ (f (τ m)) := (hτ (τ m)).symm
      _ = B.σ (B.σ (f m)) := by rw [hτ m]
      _ = f m := B.σ_σ _

  obtain ⟨rep, rep_mem, rep_tau⟩ : ∃ rep : M → M, (∀ m, rep m = m ∨ rep m = τ m) ∧
      ∀ m, rep (τ m) = rep m := by
    let enc := Fintype.equivFin M
    refine ⟨fun m => if enc m ≤ enc (τ m) then m else τ m, fun m => ?_, fun m => ?_⟩
    · dsimp only
      split_ifs <;> simp
    · dsimp only
      rw [hττ m]
      by_cases h1 : enc m ≤ enc (τ m) <;> by_cases h2 : enc (τ m) ≤ enc m
      · have h3 : m = τ m := enc.injective (le_antisymm h1 h2)
        rw [if_pos h2, if_pos h1]
        exact h3.symm
      · rw [if_neg h2, if_pos h1]
      · rw [if_pos h2, if_neg h1]
      · exact (le_total (enc m) (enc (τ m))).elim (fun h => absurd h h1) (fun h => absurd h h2)
  have rep_rep : ∀ m, rep (rep m) = rep m := by
    intro m
    rcases rep_mem m with h | h
    · rw [h, h]
    · rw [h, rep_tau, h]
  obtain ⟨g, hg⟩ : ∃ g : M → {m : M // rep m = m}, ∀ m, (g m).1 = rep m :=
    ⟨fun m => ⟨rep m, rep_rep m⟩, fun _ => rfl⟩
  have hfib : ∀ (i : {m : M // rep m = m}) (m : M), g m = i ↔ m = i.1 ∨ m = τ i.1 := by
    intro i m
    rw [Subtype.ext_iff, hg]
    constructor
    · intro h
      rcases rep_mem m with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · right
        have h3 : τ m = i.1 := h'.symm.trans h
        calc m = τ (τ m) := (hττ m).symm
          _ = τ i.1 := by rw [h3]
    · rintro (h | h)
      · rw [h]
        exact i.2
      · rw [h, rep_tau]
        exact i.2
  obtain ⟨e, he⟩ : ∃ e : {m : M // rep m = m} → B.A,
      ∀ i, e i = ∑ m ∈ Finset.univ.filter (fun m => g m = i), f m := ⟨_, fun _ => rfl⟩
  have hsum : ∀ i, e i = if τ i.1 = i.1 then f i.1 else f i.1 + f (τ i.1) := by
    intro i
    have hfil : Finset.univ.filter (fun m => g m = i) = {i.1, τ i.1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib i m
    rw [he, hfil]
    split_ifs with h
    · simp [h]
    · exact Finset.sum_pair (Ne.symm h)
  refine ⟨{m : M // rep m = m}, inferInstance, e, Finset.univ.filter (fun i => τ i.1 = i.1),
    ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · rw [he]
    exact hf.1.isIdempotentElem_sum
  · show e i * e j = 0
    rw [he, he, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply hf.1.mul_sum_of_notMem
    intro ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hij (ha.symm.trans ha')
  · simp_rw [he]
    rw [Finset.sum_fiberwise]
    exact hf.complete
  · refine ⟨f i.1, (hF _).1, (hF _).2.1, (hF _).2.2, fun hi => ?_, fun hi => ?_⟩
    · have hi' : τ i.1 = i.1 := (Finset.mem_filter.mp hi).2
      exact ⟨by rw [hsum i, if_pos hi'], by rw [hτ, hi']⟩
    · have hi' : τ i.1 ≠ i.1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact ⟨by rw [hτ]; exact hf.ortho (Ne.symm hi'), by rw [hsum i, if_neg hi', hτ]⟩
end GlobalTheory.UnitLemma.Desc
