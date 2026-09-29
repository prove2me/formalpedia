-- Prove2me | solution 1 for ModularForm.sturm_bound_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ff5e9fdc-5aa0-54d9-8061-812cb50c210c

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_sturm_bound_Gamma0

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

namespace Subgroup p2m_export "Subgroup" "index_comap relIndex comap_map_eq_self_of_injective index strictPeriods" end Subgroup
p2m_open_scoped "Subgroup" in
lemma Subgroup.relIndex_map_mapGL_W2D (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index := by
  rw [← Subgroup.index_comap, Subgroup.comap_map_eq_self_of_injective mapGL_injective]

theorem solution (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma0]
  refine ModularForm.sturm_bound_of_isArithmetic h1 ?_
  rw [Subgroup.relIndex_map_mapGL_W2D]
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ _ fun n hn ↦ ?_)
  exact h n (by lia)
end

end S_ModularForm_sturm_bound_Gamma0
end P2MW
export P2MW.S_ModularForm_sturm_bound_Gamma0 (solution)
