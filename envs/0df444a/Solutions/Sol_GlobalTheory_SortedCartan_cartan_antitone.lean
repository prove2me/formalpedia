-- Prove2me | solution 1 for GlobalTheory.SortedCartan.cartan_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:13:17.759406+00:00
-- url     : https://prove2.me/submissions/d78a5889-ed19-4821-8632-31e8933b414f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
import Theorems.Thm_GlobalTheory_SortedCartan_permUnit_mem_KO
import Theorems.Thm_GlobalTheory_SortedCartan_torusElt_conj
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LocalCartan_cartan_decomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
open GlobalTheory GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SortedCartan
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ' := by
  intro k _ _ _ _ N ϖ hϖ g
  obtain ⟨x, hx, y, hy, m, rfl⟩ := GlobalTheory.LocalCartan.cartan_decomposition k (Fin N) ϖ g hϖ
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin N), Monotone ((fun i => -m i) ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  refine ⟨m ∘ σ, fun a b hab => ?_, x * (permUnit σ)⁻¹, mul_mem hx (inv_mem (permUnit_mem_KO σ)),
    permUnit σ * y, mul_mem (permUnit_mem_KO σ) hy, ?_⟩
  · have := hmono hab
    simp only [Function.comp_apply] at this ⊢
    omega
  · have h := torusElt_conj ϖ m σ
    rw [torusElt] at h
    rw [h]
    group
end GlobalTheory.SortedCartan
