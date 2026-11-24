-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:12:01.566874+00:00
-- url     : https://prove2.me/submissions/717fdbb6-63e8-4e32-817f-715a54c21096

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
import Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_exists_chains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JordanChain
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.CompanionTheory.JordanChain
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ :=
  exists_chains _ V f rfl hf
end GlobalTheory.CompanionTheory.JordanChain
