-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.small_of_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:38:32.471295+00:00
-- url     : https://prove2.me/submissions/15abfb03-1f28-4a84-afa6-2682c0ad5015

import Mathlib
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_MatrixColumnCorner_minimal_projection
import Theorems.Thm_OAI_Kadison_MatrixColumnCorner_trace_minimal

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerDiffuse
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hone in
lemma small_of_stages_oai (F : ℕ → Stage M)
    (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) {ε : ℝ} (hε : 0<ε) :
    ∃ q : M,IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε := by
  obtain ⟨N,hN,hNε⟩ := Real.exists_nat_pos_inv_lt hε
  obtain ⟨n,hn⟩ := hsize N
  let i : (F n).I := Classical.choice inferInstance
  let q := (F n).hom (Matrix.single i i 1)
  have hqt : τ q=(Fintype.card (F n).I:ℂ)⁻¹ :=
    MatrixColumnCorner.trace_minimal τ hτ hone (F n).hom i
  have hq : IsStarProjection q := (MatrixColumnCorner.minimal_projection i).map (F n).hom
  refine ⟨q,hq,?_,?_⟩
  · intro hz
    rw [hz,map_zero] at hqt
    exact (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero (α:=(F n).I))) hqt.symm
  · rw [hqt,show (Fintype.card (F n).I:ℂ)=((Fintype.card (F n).I:ℝ):ℂ) by simp,
      ←Complex.ofReal_inv,Complex.ofReal_re]
    exact (inv_anti₀ (by exact_mod_cast hN) (by exact_mod_cast hn.le)).trans_lt hNε

end Kadison.MatrixTower

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.MatrixTower.small_of_stages_oai.{u_1} := @OAI.Kadison.MatrixTower.small_of_stages_oai.{u_1}
