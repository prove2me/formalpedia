-- Prove2me | solution 1 for GlobalTheory.DimDrop.topologicalKrullDim_lt_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:41:03.516992+00:00
-- url     : https://prove2.me/submissions/7bc0dcc0-f331-4fb1-9e8f-2c581bc9f6d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero
import Theorems.Thm_GlobalTheory_DimDrop_length_le_topologicalKrullDim_of_last_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace Order
open GlobalTheory GlobalTheory.DimDrop
namespace GlobalTheory.DimDrop
theorem _root_.solution (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    (C : Set S) (d : ℕ) (hC : IsClosed C) (hS : topologicalKrullDim S ≤ d)
    (hZ : ∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) :
    topologicalKrullDim C < d := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨p, hp⟩ := le_krullDim_iff.1 hlt
  let q : LTSeries (IrreducibleCloseds S) :=
    p.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
      (IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal)
  have hql : q.length = d := hp
  have hWC : (q.last : Set S) ⊆ C := by
    show closure (Subtype.val '' (p.last : Set C)) ⊆ C
    refine closure_minimal ?_ hC
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨Z, hZc, hWZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ q.last.isIrreducible
  by_cases hEq : (q.last : Set S) = Z
  · refine hZ Z hZc ?_ (hEq ▸ hWC)
    have := length_le_topologicalKrullDim_of_last_subset Z q hEq.le
    rwa [hql] at this
  · let Zt : IrreducibleCloseds S := ⟨Z, hZc.1, isClosed_of_mem_irreducibleComponents Z hZc⟩
    have hlt' : q.last < Zt := lt_of_le_of_ne hWZ fun e => hEq (congrArg SetLike.coe e)
    have h1 := LTSeries.length_le_krullDim (q.snoc Zt hlt')
    have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      have e : (q.snoc Zt hlt').length = d + 1 := by simp [hql]
      rw [e] at h1
      exact h1.trans hS
    norm_cast at h2
    omega
end GlobalTheory.DimDrop
