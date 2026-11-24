-- Prove2me | solution 1 for GlobalTheory.finite_submodules_between_smul_and_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:47.530841+00:00
-- url     : https://prove2.me/submissions/0085a650-dcdd-4afe-9154-a44e194d3df1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelf
import Theorems.Thm_GlobalTheory_finite_quot_span_singleton_of_dvr_sandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  intro O A _ _ _ _ _ _ C hC c hc
  haveI := finite_quot_span_singleton_of_dvr_sandwich O c hc
  haveI : Module.Finite O C := Module.Finite.iff_fg.mpr hC
  let K : Submodule O C := (Ideal.span {c}) • (⊤ : Submodule O C)
  haveI : Finite (C ⧸ K) := Submodule.finite_quotient_smul (Ideal.span {c}) Module.Finite.fg_top
  let f : Submodule O A → Set (C ⧸ K) := fun N => K.mkQ '' {x : C | (x : A) ∈ N}
  have key : ∀ N M : Submodule O A, (N ≤ C ∧ ∀ x ∈ C, c • x ∈ N) → (M ≤ C ∧ ∀ x ∈ C, c • x ∈ M) →
      f N = f M → N ≤ M := by
    intro N M hN hM h x hx
    have h1 : K.mkQ ⟨x, hN.1 hx⟩ ∈ f M := h ▸ ⟨⟨x, hN.1 hx⟩, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h1
    have h2 : y - ⟨x, hN.1 hx⟩ ∈ K := (Submodule.Quotient.eq K).mp hxy
    have h3 : ∀ z ∈ K, (z : A) ∈ M := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [Submodule.coe_smul, mul_smul]
        exact M.smul_mem a (hM.2 n n.2)
      · intro a b ha hb
        exact M.add_mem ha hb
    have h4 := M.sub_mem hy (h3 _ h2)
    simpa using h4
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro N hN M hM h
  exact le_antisymm (key N M hN hM h) (key M N hM hN h.symm)
end GlobalTheory
