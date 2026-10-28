-- Prove2me | solution 1 for OAI.KaplanskyConsequences.Regular.polynomial_dense_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:42:46.033119+00:00
-- url     : https://prove2.me/submissions/be1ea789-11cd-4af1-8512-71b699cf6e92

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf009
import Definitions.Def_OAIQ15Sf011

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]
lemma polynomial_apply (c : G →₀ ℂ) :
    (polynomial c).val = ∑ g ∈ c.support, c g • left g := by
  simp only [polynomial,Finsupp.linearCombination_apply,Finsupp.sum]
  change (Algebra G).subtype (∑ g ∈ c.support, c g • generator g) = _
  simp only [map_sum,map_smul]
  rfl

lemma adjoin_left_le_polynomial :
    StarAlgebra.adjoin ℂ (Set.range (left (G:=G) (H:=ℂ))) ≤ polynomialAlgebra := by
  apply StarAlgebra.adjoin_le
  exact Submodule.subset_span

lemma polynomial_dense (x : Algebra G) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : G →₀ ℂ, ‖x-polynomial c‖ < ε := by
  have hx : x.val ∈ closure (StarAlgebra.adjoin ℂ (Set.range (left (G:=G) (H:=ℂ))) : Set (Op G)) := x.property
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  have hs := adjoin_left_le_polynomial hy
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hs
  refine ⟨c,?_⟩
  change ‖x.val-(polynomial c).val‖ < ε
  rw [polynomial_apply]
  rw [Finsupp.sum] at hc
  rw [hc]
  simpa only [dist_eq_norm] using hxy

lemma coefficient_norm_le (x : Algebra G) : ‖coefficient x‖ ≤ ‖x‖ := by
  have hd : ‖delta (1:G)‖ = 1 := by simp [delta,lp.norm_single]
  rw [coefficient,←inner_delta]
  calc
    _ ≤ ‖delta (1:G)‖ * ‖x.val (delta 1)‖ := norm_inner_le_norm _ _
    _ ≤ ‖delta (1:G)‖ * (‖x.val‖*‖delta 1‖) := mul_le_mul_of_nonneg_left (x.val.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [hd,mul_one,one_mul]; rfl

lemma polynomial_erase (c : G →₀ ℂ) :
    polynomial (c.erase 1) = polynomial c - c 1 • (1:Algebra G) := by
  rw [Finsupp.erase_eq_sub_single,map_sub]
  congr 1
  simp only [polynomial,Finsupp.linearCombination_single]
  congr 1
  apply Subtype.ext
  exact left_one

lemma polynomial_dense_zero_oai (x : Algebra G) (hx : coefficient x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : G →₀ ℂ, c 1=0 ∧ ‖x-polynomial c‖ < ε := by
  obtain ⟨c,hc⟩ := polynomial_dense x (ε/2) (half_pos hε)
  have hcoeff : ‖c 1‖ ≤ ‖x-polynomial c‖ := by
    have h := coefficient_norm_le (x-polynomial c)
    change ‖canonicalTrace.functional (x-polynomial c)‖ ≤ _ at h
    simp only [map_sub] at h
    change ‖coefficient x-coefficient (polynomial c)‖ ≤ _ at h
    simpa only [hx,coefficient_polynomial,zero_sub,norm_neg] using h
  refine ⟨c.erase 1,Finsupp.erase_same,?_⟩
  rw [polynomial_erase]
  calc
    _ = ‖(x-polynomial c)+c 1•(1:Algebra G)‖ := by congr 1; abel
    _ ≤ ‖x-polynomial c‖+‖c 1•(1:Algebra G)‖ := norm_add_le _ _
    _ ≤ ‖x-polynomial c‖+‖c 1‖ := by
      gcongr
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by change ‖(1:Op G)‖ ≤ 1; exact ContinuousLinearMap.norm_id_le)
    _ < _ := by linarith


end KaplanskyConsequences.Regular

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KaplanskyConsequences.Regular.polynomial_dense_zero_oai.{u_1} := @OAI.KaplanskyConsequences.Regular.polynomial_dense_zero_oai.{u_1}
