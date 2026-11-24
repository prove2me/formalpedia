-- Prove2me | solution 1 for GlobalTheory.evBasic_map_nEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:14.724807+00:00
-- url     : https://prove2.me/submissions/a4c1aca4-1047-48aa-97d5-5b8b89845d3d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_GlobalTheory_evBasic_exists_pow
import Theorems.Thm_GlobalTheory_evBasic_map_tEval

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
variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]
namespace GlobalTheory
theorem _root_.solution {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S')
    (f : MvPowerSeries ι R₀) (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    φ (nEval f a) = nEval f (fun i => φ (a i)) := by
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow a ha
  have hN' : ∀ i, φ (a i) ^ N = 0 := fun i => by rw [← map_pow, hN i, map_zero]
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_nEval_eq_tEval f _ N hN', evBasic_map_tEval]
end GlobalTheory
