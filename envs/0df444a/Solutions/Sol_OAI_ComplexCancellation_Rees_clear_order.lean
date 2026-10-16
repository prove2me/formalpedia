-- Prove2me | solution 1 for OAI.ComplexCancellation.Rees.clear_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:54:25.674746+00:00
-- url     : https://prove2.me/submissions/3de7b2d5-a62e-4c47-bb35-05dabbe4f2bf

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReesClearing.lean:L61-L77
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Rees.clear_order. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction

-- ---- from OAI.Algebra.AffineCancellation.ReesReduction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial
lemma backRed_red : backRed.comp red=ρ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backRed (red (π (X i)))=ρ (π (X i))
  fin_cases i <;>
    simp [redEval,redValues,backRedEval,backRedValues,Matrix.cons_val,
      Degeneration.p,Degeneration.s,Degeneration.u,Degeneration.F,Degeneration.J]
  exact ρ_q.symm
lemma red_zero_iff (r : B) : red r=0 ↔ q ∣ r := by
  constructor
  · intro hr
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ρ r=0
    rw [← backRed_red]
    simp [hr]
  · rintro ⟨s,rfl⟩
    simp
lemma q_not_isUnit : ¬IsUnit q := by
  intro h
  have := h.map red.toMonoidHom
  change IsUnit (red q) at this
  rw [red_q] at this
  exact not_isUnit_zero this
lemma maximum_q_factor {r : B} (hr : r ≠ 0) :
    ∃ (n : ℕ) (s : B), red s ≠ 0 ∧ r=q^n*s := by
  let : WfDvdMonoid B := IsNoetherianRing.wfDvdMonoid
  obtain ⟨n,s,hs,he⟩ := WfDvdMonoid.max_power_factor' hr q_not_isUnit
  exact ⟨n,s,mt (red_zero_iff s).mp hs,he⟩
end ComplexCancellation.Rees

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReesClearing ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma embedding_q : embedding q=T 1 := by simp [q,eval,values]
lemma clear_coefficient (r : A) : c r ∈ Clearing.subalgebra embedding q := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ r
  change c (aπ r) ∈ _
  induction r using MvPolynomial.induction_on with
  | C z =>
    refine ⟨0,algebraMap ℂ B z,?_⟩
    rw [pow_zero,one_mul]
    have ha : aπ (MvPolynomial.C z)=algebraMap ℂ A z := aπ.commutes z
    rw [ha,c.commutes,embedding.commutes]
  | add r s hr hs => rw [map_add,map_add]; exact add_mem hr hs
  | mul_X r i hr =>
    rw [map_mul,map_mul]
    apply mul_mem hr
    fin_cases i
    · refine ⟨0,q*π (X 1),?_⟩
      simp only [pow_zero,one_mul,map_mul,embedding_q,embedding_π,eval,aeval_X,
        values,Matrix.cons_val_zero,Matrix.cons_val_one,a]
      change c (aπ (X 0))=T 1*(c (aπ (X 0))*T (-1))
      rw [mul_left_comm (T 1 : L),← T_add]
      norm_num
    · refine ⟨0,π (X 2),?_⟩
      simp only [pow_zero,one_mul,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      rfl
    · refine ⟨0,π (X 3),?_⟩
      simp only [pow_zero,one_mul,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      rfl
    · refine ⟨2,π (X 4),?_⟩
      simp only [embedding_q,T_pow,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      change T 2*c (aπ (X 3))=c (aπ (X 3))*T 2
      exact mul_comm (T 2 : L) (c (aπ (X 3)))
    · refine ⟨2,π (X 5),?_⟩
      simp only [embedding_q,T_pow,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      change T 2*c (aπ (X 4))=c (aπ (X 4))*T 2
      exact mul_comm (T 2 : L) (c (aπ (X 4)))

lemma clear_T (n : ℤ) : (T n : L) ∈ Clearing.subalgebra embedding q := by
  obtain ⟨m,hm⟩ : ∃ m : ℕ, 0 ≤ (m : ℤ)+n := ⟨n.natAbs,by omega⟩
  refine ⟨m,q^((m : ℤ)+n).toNat,?_⟩
  rw [map_pow,embedding_q,T_pow,T_pow,← T_add]
  congr 1
  simp only [mul_one,Int.toNat_of_nonneg hm]
lemma clear_all (r : L) : ∃ n : ℕ, ∃ s : B, embedding q^n*r=embedding s := by
  change r ∈ Clearing.subalgebra embedding q
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => exact add_mem hr hs
  | C_mul_T n r => exact mul_mem (clear_coefficient r) (clear_T n)
lemma clear_order (r : L) (hr : r ≠ 0) :
    ∃ (i : ℤ) (s : B), red s ≠ 0 ∧ embedding s=T i*r := by
  obtain ⟨n,b,hb⟩ := clear_all r
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hb
    exact mul_ne_zero (pow_ne_zero n (by rw [embedding_q]; exact (isUnit_T _).ne_zero)) hr hb
  obtain ⟨m,s,hs,hbs⟩ := maximum_q_factor hb0
  refine ⟨(n:ℤ)-m,s,hs,?_⟩
  rw [hbs,map_mul,map_pow,embedding_q,T_pow,T_pow] at hb
  have he := congrArg (fun t : L => T (-(m:ℤ))*t) hb
  simp only [mul_one] at he
  have h₀ : T (-(m:ℤ))*(T (m:ℤ):L)=1 := by rw [← T_add]; simp
  rw [← mul_assoc (T (-(m:ℤ))) (T (m:ℤ)) (embedding s),h₀,one_mul] at he
  rw [← mul_assoc,← T_add] at he
  rw [show -(m:ℤ)+(n:ℤ)=(n:ℤ)-m by omega] at he
  exact he.symm
end ComplexCancellation.Rees

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Rees.clear_order := @_root_.OAI.ComplexCancellation.Rees.clear_order
