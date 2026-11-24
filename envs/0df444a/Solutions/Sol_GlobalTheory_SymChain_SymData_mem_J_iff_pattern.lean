-- Prove2me | solution 1 for GlobalTheory.SymChain.SymData.mem_J_iff_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:43:40.386386+00:00
-- url     : https://prove2.me/submissions/8ada7382-484c-450e-bd0b-980f8c4639cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Theorems.Thm_GlobalTheory_SymPattern_pat_of_mul
import Theorems.Thm_GlobalTheory_SymPattern_exists_of_pat
import Theorems.Thm_GlobalTheory_SymPattern_entry_lt_iff
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
namespace GlobalTheory.SymChain.SymData
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k),
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  intro k _ _ _ _ s κ S g
  rw [S.sym.1 g]
  constructor
  · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
    refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
    rw [← hg₀, SymPattern.entry_lt_iff, hgb]
    exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
  · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
    obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
        rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
    exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
end GlobalTheory.SymChain.SymData
