-- Prove2me | solution 1 for GlobalTheory.evBasic_tEval_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:01.335947+00:00
-- url     : https://prove2.me/submissions/4176af9e-dc94-4643-958a-14a048bf6c32

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem

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
theorem _root_.solution (N : ℕ) (f : MvPowerSeries ι R₀) (a : ι → S) :
    tEval N f a = ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range N),
      algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) f) *
        ∏ i, a i ^ e i := by
  unfold tEval
  refine Finset.sum_bij' (fun e _ => fun i => (e i : ℕ))
    (fun e he => fun i => ⟨e i, Finset.mem_range.mp (Fintype.mem_piFinset.mp he i)⟩) ?_ ?_ ?_ ?_ ?_
  · intro e _
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (e i).isLt
  · intro e _
    exact Finset.mem_univ _
  · intro e _
    rfl
  · intro e _
    rfl
  · intro e _
    rfl
end GlobalTheory
