-- Prove2me | solution 1 for GlobalTheory.DI.phi_mem_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:07.008436+00:00
-- url     : https://prove2.me/submissions/46fb95b8-e334-4842-b257-bb45d36c8fcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductIntegral
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_SplittingIntegralFormsBound
import Theorems.Thm_GlobalTheory_DI_pow_smul_mem_forms_powMul
import Theorems.Thm_GlobalTheory_T_alternating_product_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  intro K _ V _ _ ι _ p f h Φ A B L s hΦ hf hh a q t hts hq x hx
  unfold forms at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [show Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v from hΦ c a v, Pi.smul_apply]
    exact pow_smul_mem_forms_powMul p (A : Set K) B L q c hc _
      (GlobalTheory.T.alternating_product_integral f h A L s hf hh a v t hv hts q hq)
  | zero =>
    rw [map_zero, Pi.zero_apply]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, Pi.add_apply]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [map_neg, Pi.neg_apply]
    exact neg_mem hx
end GlobalTheory.DI
