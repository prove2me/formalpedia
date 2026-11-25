-- Prove2me | solution 1 for GroundTheory.ProfCoh.coindHomotopy_identity_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:11.508258+00:00
-- url     : https://prove2.me/submissions/75c8f23c-d52d-47d7-87ef-168cd448e207

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Theorems.Thm_GroundTheory_ProfCoh_contractNth_zero_cons
import Theorems.Thm_GroundTheory_ProfCoh_contractNth_succ_cons
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology Filter Topology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {X : Type u} [AddCommGroup X] [Module k X]
omit [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {n : ℕ}
    (f : (Fin (n + 1) → G) → LocallyConstant G X) (φ : (Fin n → G) → LocallyConstant G X)
    (ψ : (Fin (n + 1) → G) → LocallyConstant G X)
    (hφ : ∀ g x, φ g x = f (Fin.cons x g) 1)
    (hψ : ∀ g x, ψ g x =
      ((inhomogeneousCochains.d (discreteCoind k G X) (n + 1)).hom f (Fin.cons x g) :
        LocallyConstant G X) 1)
    (g : Fin (n + 1) → G) (x : G) :
    ((inhomogeneousCochains.d (discreteCoind k G X) n).hom φ g : LocallyConstant G X) x +
      ψ g x = f g x := by
  have hsum : ∀ (F : Fin (n + 1) → LocallyConstant G X) (y : G), (∑ i, F i) y = ∑ i, F i y :=
    fun F y => map_sum (LocallyConstant.evalAddMonoidHom y) F Finset.univ
  have hs : ∀ j : Fin (n + 1), ((-1 : k) ^ ((j : ℕ) + 1 + 1)) =
      -((-1 : k) ^ ((j : ℕ) + 1)) := fun j => by
    rw [pow_succ, mul_neg_one]
  rw [hψ, inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply,
    Fin.sum_univ_succ (n := n + 1)]
  simp only [LocallyConstant.coe_add, Pi.add_apply, hsum, LocallyConstant.coe_smul,
    Pi.smul_apply, discreteCoindRep_apply, Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons,
    contractNth_succ_cons, hφ, one_mul, Fin.val_zero, Fin.val_succ, hs]
  simp only [zero_add, pow_one, neg_smul, one_smul, Finset.sum_neg_distrib]
  abel
end GroundTheory.ProfCoh
