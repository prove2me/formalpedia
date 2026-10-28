-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.homogeneous_angleScalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:16:17.714477+00:00
-- url     : https://prove2.me/submissions/34fdb8e9-0a09-45f1-99f3-139208f7211d

import Mathlib
import Definitions.Def_OAIQ042S015
import Theorems.Thm_OAI_CriticalStrip_Diagram_scalarValue_homogeneous_ne_zero

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma polynomialVacuumVector_eval (n:ℕ) (p:Pairing n) :
    evalLaurent (polynomialVacuumVector n p)=rationalVacuum n p := by
  cases n with
  | zero =>rw [rationalVacuum_zero]; exact map_one _
  | succ n =>exact (vacuumData n).eval_P p

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram




noncomputable section
open scoped Classical BigOperators



lemma map_scalarValue {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarValue f a) = scalarValue (g.comp f) (g ∘ a) := by
  exact MvPolynomial.map_eval₂Hom _ _ _ _

lemma rowCosineL_map {n : ℕ} (i : Fin n) : evalLaurent (rowCosineL i)=spectralA i := by
  rw [rowCosineL,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]

lemma rowCosineL_algebraMap {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowCosineL i)=spectralA i := rowCosineL_map i

lemma evalLaurent_constant_comp (n : ℕ) :
    (algebraMap (SpectralRing n) (SpectralField n)).comp (constantL n) =
      algebraMap ℂ (SpectralField n) := by
  ext z
  exact map_constantL n z

lemma scalarValue_rowCosine (n : ℕ) :
    scalarValue (constantL n) rowCosineL = polynomialVacuumVector n (empty n) := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  rw [show algebraMap (SpectralRing n) (SpectralField n) _ = _ from
    map_scalarValue _ (constantL n) rowCosineL]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap]
  change scalarValue _ spectralA = evalLaurent (polynomialVacuumVector n (empty n))
  rw [polynomialVacuumVector_eval,rationalVacuum_empty]
  exact scalarPolynomial_eval_spectral n

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RealEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset

lemma anglePhase_add (u v : ℝ) : anglePhase (u+v)=anglePhase u*anglePhase v := by
  simp only [anglePhase,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma anglePhase_neg (u : ℝ) : anglePhase (-u)=(anglePhase u)⁻¹ := by
  simp [anglePhase,Complex.exp_neg]
lemma anglePhase_sub (u v : ℝ) : anglePhase (u-v)=anglePhase u/anglePhase v := by
  simp only [sub_eq_add_neg,anglePhase_add,anglePhase_neg,div_eq_mul_inv]
lemma anglePhase_nat_mul (k : ℕ) (u : ℝ) : anglePhase ((k:ℝ)*u)=anglePhase u^k := by
  simp only [anglePhase,Complex.ofReal_mul,Complex.ofReal_natCast,←Complex.exp_nat_mul,mul_assoc]
lemma anglePhase_cosine (u : ℝ) : (anglePhase u+(anglePhase u)⁻¹)/2=(Real.cos u:ℂ) := by
  rw [anglePhase,Complex.ofReal_cos,Complex.cos,←Complex.exp_neg]
  simp only [neg_mul]

lemma rationalAt_const_complex {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) (z : ℂ) :
    RationalAt φ.toRingHom (constF n z) z := by
  have hh:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField n) (constantL n z)
  rw [map_constantL] at hh
  have he : φ (constantL n z)=z := φ.commutes z
  simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,he] using hh

lemma rationalAt_angle_variable {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (variableF i) (anglePhase (u i)) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n)
    (monomialL (variableExponent i) 1)
  change RationalAt (angleEvaluation u).toRingHom (variableF i)
    (angleEvaluation u (monomialL (variableExponent i) 1)) at hh
  simpa only [angleEvaluation_variable] using hh

lemma rationalAt_angle_cos {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusCos x) (Real.cos u:ℂ) := by
  rw [←anglePhase_cosine]
  exact (h.add (h.inv (anglePhase_ne_zero _))).div (RationalAt.natCast 2) (by norm_num)

lemma rationalAt_angle_spectralA {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (spectralA i) (Real.cos (2*u i-3*lambda):ℂ) := by
  apply rationalAt_angle_cos
  rw [anglePhase_sub,show anglePhase (2*u i)=anglePhase (u i)^2 from anglePhase_nat_mul 2 _,
    show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact
    ((rationalAt_angle_variable u i).pow 2).div
      ((rationalAt_const_complex (angleEvaluation u) phase).pow 3) (pow_ne_zero _ phase_ne_zero)

lemma angleEvaluation_rowCosine {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    angleEvaluation u (rowCosineL i)=(Real.cos (2*u i-3*lambda):ℂ) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n) (rowCosineL i)
  rw [rowCosineL_algebraMap] at hh
  exact hh.unique (rationalAt_angle_spectralA u i)

lemma angleEvaluation_scalar {n : ℕ} (u : Fin n → ℝ) :
    angleEvaluation u (polynomialVacuumVector n (empty n))=
      scalarValue (RingHom.id ℂ) (fun i=>(Real.cos (2*u i-3*lambda):ℂ)) := by
  rw [←scalarValue_rowCosine]
  have hh:=map_scalarValue (angleEvaluation u).toRingHom (constantL n) rowCosineL
  have hc : (angleEvaluation u).toRingHom.comp (constantL n)=RingHom.id ℂ := by ext z; simp
  rw [hc] at hh
  have hf : (angleEvaluation u).toRingHom ∘ rowCosineL=fun i=>(Real.cos (2*u i-3*lambda):ℂ) := by
    funext i
    exact angleEvaluation_rowCosine u i
  rw [hf] at hh
  exact hh

end
end CriticalStrip.Diagram







end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeformationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix
open scoped BigOperators Classical

lemma homogeneous_angleScalar_ne_zero_oai (n : ℕ) : angleScalar (fun _ : Fin n=>lambda)≠0 := by
  rw [angleScalar,angleEvaluation_scalar]
  simpa only [show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg,C] using
    scalarValue_homogeneous_ne_zero n

end
end CriticalStrip.Diagram

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.homogeneous_angleScalar_ne_zero_oai := @OAI.CriticalStrip.Diagram.homogeneous_angleScalar_ne_zero_oai
