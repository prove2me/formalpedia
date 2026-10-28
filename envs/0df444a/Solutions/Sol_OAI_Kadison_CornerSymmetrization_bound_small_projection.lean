-- Prove2me | solution 1 for OAI.Kadison.CornerSymmetrization.bound_small_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:28.873478+00:00
-- url     : https://prove2.me/submissions/56099514-22db-4fa6-bb1d-1a34955ac9bc

import Mathlib
import Definitions.Def_OAIQ039C066

section
-- module Solutions.OAIQ039_CM.Commutator_NormalCornerExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem extend_projection_trace (M : VonNeumannAlgebra H)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hone : τ 1=1) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (q : M) (hq : IsStarProjection q) {β : ℝ}
    (hβq : (τ q).re≤β) (hβ : β≤1) :
    ∃ e : M, IsStarProjection e ∧ q≤e ∧ τ e=(β:ℂ) := by
  have htr : β-(τ q).re≤(τ (1-q)).re := by
    rw [map_sub,hone,Complex.sub_re,Complex.one_re]
    linarith
  obtain ⟨r,hr,hrle,hrt⟩ := exists_prescribed_projection_trace M τ hτ hnormal hfaith
    hdiffuse (1-q) hq.one_sub (sub_nonneg.mpr hβq) htr
  have hqr : q*r=0 := by
    have hfix := (hr.le_iff_mul_eq_right hq.one_sub).mp hrle
    calc
      q*r=q*((1-q)*r) := by rw [hfix]
      _=0 := by rw [←mul_assoc,hq.mul_one_sub_self,zero_mul]
  have he := hq.add hr hqr
  refine ⟨q+r,he,le_add_of_nonneg_right hr.nonneg,?_⟩
  apply Complex.ext
  · simp only [map_add,Complex.add_re,Complex.ofReal_re,hrt]; ring
  · exact (τ.map_nonneg he.nonneg).2.symm

end Kadison.NormalGNS

namespace Kadison.CornerSymmetrization

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem bound_small_projection_oai (M : VonNeumannAlgebra H)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hone : τ 1=1) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (P : StarSubalgebra ℂ (K →L[ℂ] K))
    (Ω : K) (hΩ : ∀ a : M, vectorState Ω (π a)=τ a)
    (G : K →L[ℂ] K) (ε β : ℝ) (hβ : β≤1)
    (hbound : ∀ x, CornerElement π.range P Ω (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖)
    (q : M) (hq : IsStarProjection q) (hqt : (τ q).re≤β)
    (x : K →L[ℂ] K) (hx : x∈P) (hl : π q*x=x) (hr : x*π q=x) :
    ‖G*x-x*G‖≤ε*‖x‖ := by
  obtain ⟨e,he,hqe,het⟩ := NormalGNS.extend_projection_trace M τ hτ hnormal hfaith
    hone hdiffuse q hq hqt hβ
  have hleft : π e*π q=π q := by
    rw [←map_mul,(hq.le_iff_mul_eq_right he).mp hqe]
  have hright : π q*π e=π q := by
    rw [←map_mul,(hq.le_iff_mul_eq_left he).mp hqe]
  apply hbound x
  refine ⟨hx,π e,⟨e,rfl⟩,he.map π,(hΩ e).trans het,?_,?_⟩
  · calc
      π e*x=π e*(π q*x) := by rw [hl]
      _=x := by rw [←mul_assoc,hleft,hl]
  · calc
      x*π e=(x*π q)*π e := by rw [hr]
      _=x := by rw [mul_assoc,hright,hr]

end Kadison.CornerSymmetrization

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.CornerSymmetrization.bound_small_projection_oai.{u_1, u_2} := @OAI.Kadison.CornerSymmetrization.bound_small_projection_oai.{u_1, u_2}
