-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.scalar_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:37:25.744899+00:00
-- url     : https://prove2.me/submissions/8493822f-c61e-4fa6-878e-c6681f0abd86

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C056

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerIrreducible
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace ComplexStarModule

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hone : τ 1=1)

include hτ hone in
lemma centered_approximation (F : Stage M) (a b : M) :
    ‖algebraVector τ (expectation F.hom a-τ a • (1:M))‖≤
    2*‖algebraVector τ (a-b)‖+‖algebraVector τ (expectation F.hom b-τ b • (1:M))‖ := by
  have he : expectation F.hom a-τ a • (1:M)=
      (expectation F.hom (a-b)-τ (a-b) • (1:M))+
        (expectation F.hom b-τ b • (1:M)) := by
    rw [map_sub,map_sub,sub_smul]
    abel
  have ht : ‖algebraVector τ (τ (a-b) • (1:M))‖≤‖algebraVector τ (a-b)‖ := by
    rw [map_smul,norm_smul]
    have h1 : ‖algebraVector τ (1:M)‖=1 := vacuum_norm τ hone
    rw [h1,mul_one]
    exact MatrixApproximation.trace_norm_le_vector τ hone _
  rw [he,map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  rw [map_sub]
  exact (norm_sub_le _ _).trans (by linarith [norm_vector_le F.hom τ hτ (a-b)])

variable (x : ℕ → M)
  (hxden : ∀ a : M,IsSelfAdjoint a → ∀ ε : ℝ,0<ε → ∃ j,‖algebraVector τ (a-x j)‖<ε)
  (F : ℕ → Stage M)
  (hreq : ∀ j : ℕ,∀ ε : ℝ,0<ε → ∃ n,
    ‖algebraVector τ (expectation (F n).hom (x j)-τ (x j) • (1:M))‖<ε)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)

include hτ hone hxden hreq hfaith in
lemma scalar_of_selfAdjoint_commutes (a : M) (ha : IsSelfAdjoint a)
    (hc : ∀ n b,(F n).hom b*a=a*(F n).hom b) : a=τ a • (1:M) := by
  have hz : algebraVector τ (a-τ a • (1:M))=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨j,hj⟩ := hxden a ha (ε/4) (by positivity)
      obtain ⟨n,hn⟩ := hreq j (ε/2) (half_pos hε)
      have he := centered_approximation M τ hτ hone (F n) a (x j)
      rw [fixes (F n).hom a (hc n)] at he
      linarith
    · exact norm_nonneg _
  apply sub_eq_zero.mp
  apply hfaith
  rw [←inner_algebraVector,hz,inner_zero_left]

include hτ hone hxden hreq hfaith in
theorem scalar_of_commutes_oai (a : M)
    (hc : ∀ n b,(F n).hom b*a=a*(F n).hom b) : a=τ a • (1:M) := by
  have hcs : ∀ n b,(F n).hom b*star a=star a*(F n).hom b := by
    intro n b
    have he := congrArg star (hc n (star b))
    simpa only [star_mul,←map_star,star_star] using he.symm
  have hr : (ℜ a:M)=τ (ℜ a:M) • (1:M) := by
    apply scalar_of_selfAdjoint_commutes M τ hτ hone x hxden F hreq hfaith _ (ℜ a).property
    intro n b
    simp only [realPart_apply_coe,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,hc,hcs]
  have hi : (ℑ a:M)=τ (ℑ a:M) • (1:M) := by
    apply scalar_of_selfAdjoint_commutes M τ hτ hone x hxden F hreq hfaith _ (ℑ a).property
    intro n b
    simp only [imaginaryPart_apply_coe,mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul,hc,hcs]
  have ht : τ a=τ (ℜ a:M)+Complex.I*τ (ℑ a:M) := by
    conv_lhs => rw [←realPart_add_I_smul_imaginaryPart a]
    rw [map_add,map_smul,smul_eq_mul]
  calc
    a=(ℜ a:M)+Complex.I • (ℑ a:M) := (realPart_add_I_smul_imaginaryPart a).symm
    _=τ (ℜ a:M) • (1:M)+Complex.I • (τ (ℑ a:M) • (1:M)) :=
      congrArg₂ (·+·) hr (congrArg (fun z : M => Complex.I • z) hi)
    _=(τ (ℜ a:M)+Complex.I*τ (ℑ a:M)) • (1:M) := by rw [smul_smul,add_smul]
    _=τ a • (1:M) := by rw [←ht]

end Kadison.MatrixTower

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.MatrixTower.scalar_of_commutes_oai.{u_1} := @OAI.Kadison.MatrixTower.scalar_of_commutes_oai.{u_1}
