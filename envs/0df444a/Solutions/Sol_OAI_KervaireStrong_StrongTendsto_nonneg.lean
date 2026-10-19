-- Prove2me | solution 1 for OAI.KervaireStrong.StrongTendsto.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:19:26.716596+00:00
-- url     : https://prove2.me/submissions/5e7adefc-4b1f-4258-976b-988921f9fd35

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits

open OAI OAI.KervaireStrong
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder
theorem solution {T : ι → Operator K} {S : Operator K} [l.NeBot]
    (h : StrongTendsto T l S) (hp : ∀ i, 0 ≤ T i) : 0 ≤ S := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hlim : Tendsto (fun i => inner ℂ (T i x) x) l (𝓝 (inner ℂ (S x) x)) :=
    (h x).inner tendsto_const_nhds
  have hclosed : IsClosed {z : ℂ | ((z.re : ℂ) = z) ∧ 0 ≤ z.re} := by
    apply IsClosed.inter
    · exact isClosed_eq (Complex.continuous_ofReal.comp Complex.continuous_re) continuous_id
    · exact isClosed_le continuous_const Complex.continuous_re
  have hmem : ∀ i, inner ℂ (T i x) x ∈ {z : ℂ | ((z.re : ℂ) = z) ∧ 0 ≤ z.re} := by
    intro i
    have := (ContinuousLinearMap.nonneg_iff_isPositive _).1 (hp i)
    rw [ContinuousLinearMap.isPositive_iff_complex] at this
    exact this x
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
