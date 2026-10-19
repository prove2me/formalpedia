-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjesPhaseProduct_of_escaping_prefix_strict_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/bbc167bf-43e1-4c87-8f34-70a85b350ea2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_stieltjesPhaseProduct_of_escaping_prefix

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {k r q : ℕ}
    (a : ℕ → Fin (k + r + 1) → ℝ)
    (b : ℕ → Fin (k + r) → ℝ)
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (d : Fin k → ℝ)
    (hu : ∀ i : Fin k,
      Tendsto (fun n => a n (i.castAdd (r + 1))) atTop atTop)
    (hd : ∀ i : Fin k,
      Tendsto (fun n =>
        b n (i.castAdd r) / a n (i.castAdd (r + 1)))
        atTop (𝓝 (d i)))
    (ha : ∀ i : Fin (r + 1),
      Tendsto (fun n => a n (i.natAdd k)) atTop (𝓝 (A i)))
    (hb : ∀ i : Fin r,
      Tendsto (fun n => b n (i.natAdd k)) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio A B t = hierarchyStieltjesRatio A' B' t)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop (𝓝 ((∏ i : Fin k, d i ^ 2) * stieltjesPhaseProduct A' B' t)) := by
  have hlimit := tendsto_stieltjesPhaseProduct_of_escaping_prefix
    a b A B d hu hd ha hb hA ht
  convert hlimit using 1
  rw [stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio,
    stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio,
    hratio t ht]
end MetricCodes.Spherical.HigherHierarchy
