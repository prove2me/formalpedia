-- Prove2me | solution 1 for OAI.ComplexCancellation.AffineModification.piece_even
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:10:58.487362+00:00
-- url     : https://prove2.me/submissions/9b8589aa-248b-4e3a-9efd-00d47468602b

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ModificationGrading.lean:L68-L86
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.AffineModification.piece_even. The node keeps its source
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
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading

-- ---- from OAI.Algebra.AffineCancellation.ModificationGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma monomial_image (d : Fin 2 →₀ ℕ) (r : R) :
    π R v (monomial d r)=τ R v^(d 0)*V R v^(d 1)*algebraMap R (T R v) r := by
  rw [monomial_eq]
  simp only [map_mul,AlgHom.commutes,MvPolynomial.C_eq_algebraMap]
  rw [Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two,map_mul,map_pow,τ,V]
    ring
  · intro i
    simp
lemma weight_eq (d : Fin 2 →₀ ℕ) :
    Finsupp.weight weight d = 2*(d 1 : ℤ)-(d 0 : ℤ) := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two,weight]
    ring
  · intro i
    simp
lemma monomial_reduction (i h m : ℕ) :
    τ R v^(i+2*m)*V R v^(h+m)=τ R v^i*V R v^h*algebraMap R (T R v) (v^m) := by
  rw [map_pow,← equation R v,pow_add,pow_add,pow_mul,mul_pow]
  ring
lemma piece_even (n : ℕ) {r : T R v} (hr : r ∈ pieces R v (2*(n:ℤ))) :
    ∃ s : R, r=V R v^n*algebraMap R (T R v) s := by
  obtain ⟨p,hp,rfl⟩ := hr
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0,by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨a,ha⟩ := ihp
    obtain ⟨b,hb⟩ := ihq
    exact ⟨a+b,by rw [map_add,map_add,ha,hb,mul_add]⟩
  | monomial d a hd =>
    rw [weight_eq] at hd
    have hi : d 0=2*(d 1-n) := by omega
    have hh : d 1=n+(d 1-n) := by omega
    refine ⟨v^(d 1-n)*a,?_⟩
    change π R v (monomial d a)=_
    rw [monomial_image,hi]
    conv_lhs => arg 1; arg 2; rw [hh]
    have he := monomial_reduction R v 0 n (d 1-n)
    simpa only [zero_add,pow_zero,one_mul,map_mul,mul_assoc] using congrArg (fun x => x*algebraMap R (T R v) a) he
end ComplexCancellation.AffineModification

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.AffineModification
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra


theorem solution : type_of% @_root_.OAI.ComplexCancellation.AffineModification.piece_even := @_root_.OAI.ComplexCancellation.AffineModification.piece_even
