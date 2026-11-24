-- Prove2me | solution 1 for GlobalTheory.nEval_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:48.221502+00:00
-- url     : https://prove2.me/submissions/d7534579-edaf-4fea-8f90-7d86d812b412

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_GlobalTheory_evBasic_map_nEval
import Theorems.Thm_GlobalTheory_evBasic_nEval_sub_coeff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) := by
  intro R₀ _ ι _ _ f S _ _ a
  exact ⟨fun N hN => evBasic_nEval_eq_tEval f a N hN,
    fun ha => ⟨fun S' _ _ φ => evBasic_map_nEval φ f a ha, evBasic_nEval_sub_coeff_mem f a ha⟩⟩
end GlobalTheory
