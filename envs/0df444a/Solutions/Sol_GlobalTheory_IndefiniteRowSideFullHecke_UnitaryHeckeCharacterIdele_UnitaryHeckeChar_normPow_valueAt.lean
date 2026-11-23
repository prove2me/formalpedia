-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_valueAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:06.750549+00:00
-- url     : https://prove2.me/submissions/78c970b5-3d03-43ef-9bce-86966872af87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_valueAt_eq
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_ideleNorm_localIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_normPow_isUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
section CM
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end CM
section Extension
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
end Extension
example : IsCMExtension (maximalRealSubfield (CyclotomicField 4 ℚ)) (CyclotomicField 4 ℚ) :=
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  haveI : IsCMField (CyclotomicField 4 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField _ (S := {4}) ⟨4, rfl, by norm_num⟩
  inferInstance
variable {E : Type} [Field E] [NumberField E]
namespace UnitaryHeckeChar
end UnitaryHeckeChar
namespace UnitaryHeckeChar
example (P : HeightOneSpectrum (𝓞 E)) : (trivial E).valueAt P = 1 := by
  have h : (trivial E).IsUnramifiedAt P := fun _ _ => rfl
  rw [valueAt, if_pos h]
  rfl
end UnitaryHeckeChar
namespace UnitaryHeckeChar
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
private theorem norm_uniformiser_eq_absNorm_inv {P : HeightOneSpectrum (𝓞 E)}
    {ϖ : (P.adicCompletion E)ˣ} (hϖ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsUniformiser P ϖ) :
    ‖(ϖ : P.adicCompletion E)‖ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  rw [FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [show ∀ hx, Multiplicative.toAdd (WithZero.unzero (x := WithZero.exp (-1 : ℤ)) hx) = -1
    from fun _ => rfl]
  simp
end UnitaryHeckeChar
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable {E : Type} [Field E] [NumberField E]
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
theorem _root_.solution (t : ℝ) (P : HeightOneSpectrum (𝓞 E)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow E t).valueAt P =
      Complex.exp ((-(t * Real.log (Ideal.absNorm P.asIdeal)) : ℝ) * Complex.I) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser P
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_eq _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_isUnramifiedAt t P) hϖ]
  show ((Circle.exp (t * Real.log (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P ϖ))) : ℂ)) = _
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele, norm_uniformiser_eq_absNorm_inv hϖ,
    Real.log_inv, mul_neg, Circle.coe_exp]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
