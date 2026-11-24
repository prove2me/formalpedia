-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.isLat_iff_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:47.260861+00:00
-- url     : https://prove2.me/submissions/02347d5c-e384-47ea-9455-def4349c6954

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {O O' E E' A : Type} [CommRing O] [CommRing O'] [Field E] [Field E'] [CommRing A]
    [Algebra O A] [Algebra O' A] [Algebra E A] [Algebra E' A] {d : ℕ} (u : Fin d → O')
    (h1 : ∀ a : O, ∃ b : O', algebraMap O' A b = algebraMap O A a)
    (h2 : ∀ y : O', ∃ a : Fin d → O, algebraMap O' A y = ∑ i, algebraMap O A (a i) * algebraMap O' A (u i))
    (h3 : ∀ e : E, ∃ e' : E', algebraMap E' A e' = algebraMap E A e)
    (h4 : ∀ e' : E', ∃ (e : E) (b : O'), algebraMap E' A e' = algebraMap E A e * algebraMap O' A b)
    (L : Submodule O' A) (M : Submodule O A) (h : (L : Set A) = (M : Set A)) :
    IsLat O' E' L ↔ IsLat O E M := by
  classical
  have hm : ∀ y, y ∈ L ↔ y ∈ M := fun y => by
    rw [← SetLike.mem_coe, h, SetLike.mem_coe]
  refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨S, hS⟩
    refine ⟨(Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact (hm _).1 (L.smul_mem _ (hS ▸ Submodule.subset_span hp.2))
    · intro x hx
      have hx' : x ∈ Submodule.span O' (S : Set A) := hS ▸ (hm x).2 hx
      set N := Submodule.span O
        ((((Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2 : Finset A)) : Set A) with hN
      have key : ∀ c : O', c • x ∈ N := by
        clear hx
        induction hx' using Submodule.span_induction with
        | mem s hs =>
          intro c
          obtain ⟨a, ha⟩ := h2 c
          rw [Algebra.smul_def, ha, Finset.sum_mul]
          refine N.sum_mem fun i _ => ?_
          rw [mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
          refine N.smul_mem _ (Submodule.subset_span ?_)
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
          exact ⟨(i, s), ⟨Finset.mem_univ _, hs⟩, rfl⟩
        | zero => intro c; simp
        | add x z _ _ hx hz => intro c; rw [smul_add]; exact N.add_mem (hx c) (hz c)
        | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
      simpa using key 1
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, h, ← hS]
      exact Submodule.subset_span
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set A) := hS ▸ (hm x).1 hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem s hs => exact Submodule.subset_span hs
      | zero => exact zero_mem _
      | add x z _ _ hx hz => exact add_mem hx hz
      | smul e x _ hx =>
        obtain ⟨b, hb⟩ := h1 e
        rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hx
  · intro hL
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E' (L : Set A) := hL ▸ Submodule.mem_top
    have key : ∀ c : E', c • x ∈ Submodule.span E (M : Set A) := by
      induction hx' using Submodule.span_induction with
      | mem s hs =>
        intro c
        obtain ⟨e, b, hb⟩ := h4 c
        rw [Algebra.smul_def, hb, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).1 (L.smul_mem _ hs)))
      | zero => intro c; simp
      | add x z _ _ hx hz => intro c; rw [smul_add]; exact add_mem (hx c) (hz c)
      | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
    simpa using key 1
  · intro hM
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
    induction hx' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ((hm s).2 hs)
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      obtain ⟨b, hb⟩ := h3 e
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
end GlobalTheory.UnitLemma.Unr
