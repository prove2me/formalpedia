-- Prove2me | solution 1 for OAI.ComplexCancellation.Rees.primitive_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:58:57.865425+00:00
-- url     : https://prove2.me/submissions/8318771c-9905-45a7-9be1-b072b86d3daa

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReesDerivation.lean:L108-L140
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Rees.primitive_reduction. The node keeps its source
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
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Theorems.Thm_OAI_ComplexCancellation_LND_primitive_of_order

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
lemma q_nonzero : q ≠ 0 := by
  intro h
  have := congrArg embedding h
  rw [embedding_q,map_zero] at this
  exact (isUnit_T (R := A) 1).ne_zero this
end ComplexCancellation.Rees

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReesDerivation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma red_up : red.comp up=Degeneration.π := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [up,redEval,redValues,Matrix.cons_val,
    Degeneration.p,Degeneration.s,Degeneration.u,Degeneration.F,Degeneration.J]
lemma red_surjective : Function.Surjective red := by
  intro r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ r
  exact ⟨up p,DFunLike.congr_fun red_up p⟩
lemma primitive_reduction (E : Derivation ℂ B B) (hE : LND.LocallyNilpotent E)
    (hEn : E ≠ 0) (hEq : E q=0) (s : B) (hEs : E s=0) :
    ∃ D : Derivation ℂ Degeneration.G Degeneration.G,
      LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D (red s)=0 := by
  obtain ⟨b,hb⟩ : ∃ b, E b ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hEn
    ext b
    exact hn b
  obtain ⟨n,t,ht,he⟩ := maximum_q_factor hb
  obtain ⟨E',hE',hEq',hEs',r,hr⟩ := LND.primitive_of_order q q_nonzero s b t
    (mt (red_zero_iff t).mpr ht) n E hE hEq hEs he
  have hk (b : B) (hb : red b=0) : red (E' b)=0 := by
    obtain ⟨t,rfl⟩ := (red_zero_iff b).mp hb
    simp only [Derivation.leibniz,hEq',smul_eq_mul,mul_zero,add_zero,
      map_mul,red_q,zero_mul]
  let D := Derivation.liftOfSurjective red_surjective hk
  have hspec (b : B) : D (red b)=red (E' b) := Derivation.liftOfSurjective_apply red_surjective hk b
  have hiter (b : B) (n : ℕ) : (D : Degeneration.G → Degeneration.G)^[n] (red b)=red ((E' : B → B)^[n] b) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih,hspec,Function.iterate_succ_apply']
  refine ⟨D,?_,?_,?_⟩
  · intro b
    obtain ⟨b,rfl⟩ := red_surjective b
    obtain ⟨n,hn⟩ := hE' b
    exact ⟨n,by rw [hiter,hn,map_zero]⟩
  · intro hz
    apply hr
    apply (red_zero_iff (E' r)).mp
    rw [← hspec,hz,Derivation.zero_apply]
  · rw [hspec,hEs',map_zero]
end ComplexCancellation.Rees

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Rees.primitive_reduction := @_root_.OAI.ComplexCancellation.Rees.primitive_reduction
