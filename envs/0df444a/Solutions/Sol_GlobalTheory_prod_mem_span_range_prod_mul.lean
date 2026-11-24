-- Prove2me | solution 1 for GlobalTheory.prod_mem_span_range_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:56.070456+00:00
-- url     : https://prove2.me/submissions/1f47d1ac-b09e-4e83-ba7a-2aefe437cd41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecializationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type*} [Fintype J] (g : J → A) (m : ℕ) (f : Fin m → A)
    (hf : ∀ l, f l ∈ Submodule.span R (Set.range g)) (y : A) :
    (∏ l, f l) * y ∈
      Submodule.span R (Set.range fun u : Fin m → J => (∏ l, g (u l)) * y) := by
  choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun R).1 (hf l)
  have h : (∏ l, f l) * y = ∑ u : Fin m → J, (∏ l, c l (u l)) • ((∏ l, g (u l)) * y) := by
    simp_rw [← hc, Fintype.prod_sum, Finset.sum_mul, Algebra.smul_def, Finset.prod_mul_distrib,
      map_prod, mul_assoc]
  rw [h]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)
end GlobalTheory
