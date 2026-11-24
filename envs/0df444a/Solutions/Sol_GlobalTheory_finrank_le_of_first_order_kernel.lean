-- Prove2me | solution 1 for GlobalTheory.finrank_le_of_first_order_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:47.14487+00:00
-- url     : https://prove2.me/submissions/69e04758-9485-4956-9693-f564ef949af2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt

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
theorem _root_.solution (k V U : Type) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup U] [Module k U] [Module.Finite k U] (e : ℕ) (t u : V →ₗ[k] U)
    (h : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) :
    Module.finrank k V ≤ Module.finrank k U + e := by
  classical
  set q : LinearMap.ker t →ₗ[k] U ⧸ LinearMap.range t :=
    (LinearMap.range t).mkQ ∘ₗ u ∘ₗ (LinearMap.ker t).subtype

  have hq : Module.finrank k (LinearMap.ker q) ≤ e := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k) (M := LinearMap.ker q)
      (n := e + 1) hlt
    have hmem : ∀ j, u ((f j : LinearMap.ker t) : V) ∈ LinearMap.range t := by
      intro j
      have hj : (LinearMap.range t).mkQ (u ((f j : LinearMap.ker t) : V)) = 0 :=
        LinearMap.mem_ker.mp (f j).2
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hj
      exact hj
    choose y hy using fun j => LinearMap.mem_range.mp (hmem j)
    have hli : LinearIndependent k (fun j => ((f j : LinearMap.ker t) : V)) :=
      (hf.map' _ (Submodule.ker_subtype _)).map' _ (Submodule.ker_subtype _)
    exact h (fun j => ((f j : LinearMap.ker t) : V)) y
      (fun j => ⟨LinearMap.mem_ker.mp (f j : LinearMap.ker t).2, hy j⟩) hli
  have h1 := LinearMap.finrank_range_add_finrank_ker t
  have h2 := LinearMap.finrank_range_add_finrank_ker q
  have h3 := Submodule.finrank_le (LinearMap.range q)
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.range t)
  omega
end GlobalTheory
