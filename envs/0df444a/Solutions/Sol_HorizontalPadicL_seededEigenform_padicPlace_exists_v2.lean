-- Prove2me | solution 1 for HorizontalPadicL.seededEigenform_padicPlace_exists_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:23:16.049782+00:00
-- url     : https://prove2.me/submissions/f84d543b-d3e9-4a19-b199-8f69aec1bade

import Theorems.Thm_MTT_Eigenform_coeff_isIntegral
import Definitions.Def_KN_SeededPrimeGaloisDataV2
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.Valuation.Integral

set_option autoImplicit false
noncomputable section

attribute [local instance] AlgebraicClosure.isAlgebraic

theorem _root_.solution
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : HorizontalPadicL.IsNewEigenform f)
    (η : HorizontalPadicL.DirichletCharacterWithLevel) :
    Nonempty (HorizontalPadicL.SeededEigenformPadicPlaceData (p := p) f η) := by
  letI : Algebra.IsAlgebraic ℚ MTT.Qbar := AlgebraicClosure.isAlgebraic ℚ
  let ιp : MTT.Qbar →+* ℂ_[p] :=
    (IsAlgClosed.lift (R := ℚ) (S := MTT.Qbar) (M := ℂ_[p])).toRingHom
  have norm_le_one_of_integral (x : MTT.Qbar) (hx : IsIntegral ℤ x) :
      ‖ιp x‖ ≤ 1 := by
    have hx' : IsIntegral ℤ (ιp x) := by
      change (algebraMap ℤ ℂ_[p]).IsIntegralElem (ιp x)
      rw [← show ιp.comp (algebraMap ℤ MTT.Qbar) = algebraMap ℤ ℂ_[p] by
        ext z
        simp]
      exact RingHom.IsIntegralElem.map hx ιp
    have hxO : IsIntegral 𝓞_ℂ_[p] (ιp x) := hx'.tower_top
    have hv : Valued.v (ιp x) ≤ 1 :=
      (PadicComplexInt.integers (p := p)).isIntegral_iff_v_le_one.mp hxO
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff (x := ιp x)).2 hv
  refine ⟨{
    embedding := ιp
    coeff_integral := fun n => norm_le_one_of_integral (f.coeff n)
      (MTT.Eigenform.coeff_isIntegral hN hk ι f n)
    character_integral := ?_ }⟩
  intro a
  exact DirichletCharacter.norm_le_one (η.2.ringHomComp ιp) (a : ZMod η.1.1)
