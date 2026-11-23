-- Prove2me | solution 1 for GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.exists_common_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:11.375529+00:00
-- url     : https://prove2.me/submissions/0d66f265-a4ea-4c55-a5e5-089c9fd730ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
open Module
namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
theorem _root_.solution {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : ι → Module.End k V)
    (hcomm : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, (f i : V → V) w ∈ W) →
        ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ i, ∃ c : k, (f i : V → V) x = c • x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hinv
  by_cases hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    let g : Module.End k W := (f i).restrict (fun w hw => hinv i w hw)
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hgv : g v = c • v := hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'
    have hvW' : (v : V) ∈ W' := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hgv
      simpa [g] using this
    have hW'ne : W' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hvW'
      exact hv0 (Subtype.ext hvW')
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      obtain ⟨w, hw, hne⟩ := hi c
      have : w ∈ W' := h ▸ hw
      exact hne ((Module.End.mem_eigenspace_iff).mp this.2)
    have hdlt : Module.finrank k W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W' := by
      intro j w hw
      refine ⟨hinv j w hw.1, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h1 : f i w = c • w := (Module.End.mem_eigenspace_iff).mp hw.2
      have h2 := congrArg (fun F : Module.End k V => F w) (hcomm i j)
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨x, hx, hx0, hxe⟩ := ih _ hdlt W' rfl hW'ne hinv'
    exact ⟨x, hx.1, hx0, hxe⟩
end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
