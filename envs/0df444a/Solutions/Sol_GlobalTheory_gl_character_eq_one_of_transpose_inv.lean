-- Prove2me | solution 1 for GlobalTheory.gl_character_eq_one_of_transpose_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:37.652152+00:00
-- url     : https://prove2.me/submissions/4bef14c6-0277-4a9d-be19-49f6125830e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] [Infinite k] (n : Type)
    [Fintype n] [DecidableEq n] (χ : GL n k →* NNReal)
    (h : ∀ g g' : GL n k, g'.val = (g⁻¹ : GL n k).valᵀ → χ g' = χ g) (g : GL n k) :
    χ g = 1 := by
  classical
  have hne : ∀ g : GL n k, χ g ≠ 0 := by
    intro g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  have hdiag : ∀ (D : n → k) (g : GL n k), g.val = diagonal D → χ g = 1 := by
    intro D g hg
    have h1 : χ g⁻¹ = χ g := by
      apply h
      rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hg, diagonal_transpose]
    have h2 : χ g * χ g = 1 := by
      calc χ g * χ g = χ g * χ g⁻¹ := by rw [h1]
        _ = 1 := by rw [← map_mul]; simp
    have h3 : χ g ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg (zero_le) two_ne_zero).1 h3
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := by intro h0; apply ha; simp [h0]
  have ha1 : 1 - a ≠ 0 := by
    intro h0; apply ha; have : a = 1 := by linear_combination -h0
    simp [this]
  have htr : ∀ (t : TransvectionStruct n k) (g : GL n k), g.val = t.toMatrix → χ g = 1 := by
    rintro ⟨i, j, hij, x⟩ g hg
    let T : k → GL n k := fun y => GeneralLinearGroup.mkOfDetNeZero (transvection i j y)
      (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)
    have hT : ∀ y, (T y).val = transvection i j y := fun y => rfl
    have hgT : g = T x := Units.ext (by rw [hg, hT]; rfl)
    have hconj : ∀ b : k, b ≠ 0 → χ (T (b * x)) = χ (T x) := by
      intro b hb
      let D : GL n k := GeneralLinearGroup.mkOfDetNeZero (diagonal (Function.update 1 i b))
        (by
          rw [det_diagonal]
          refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
          by_cases hl : l = i
          · subst hl; simpa using hb
          · simp [Function.update_of_ne hl])
      have hD : D.val = diagonal (Function.update 1 i b) := rfl
      have e : D * T x = T (b * x) * D := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hD, hT, hT]
        ext p q
        rw [diagonal_mul, mul_diagonal]
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        by_cases hp : i = p
        · subst hp
          by_cases hq : j = q
          · subst hq
            simp [hij, Function.update_of_ne hij.symm]
          · by_cases hpq : i = q
            · subst hpq; simp [hq]
            · simp [hq, hpq]
        · by_cases hpq : p = q
          · subst hpq; simp [hp]
          · simp [hp, hpq]
      have := congrArg χ e
      rw [map_mul, map_mul, hdiag _ D hD, one_mul, mul_one] at this
      exact this.symm
    have e : T x = T (a * x) * T ((1 - a) * x) := by
      apply Units.ext
      rw [Units.val_mul, hT, hT, hT, transvection_mul_transvection_same i j hij]
      congr 1
      ring
    have e2 := congrArg χ e
    rw [map_mul, hconj a ha0, hconj _ ha1] at e2
    rw [hgT]
    exact (mul_eq_left₀ (hne _)).1 e2.symm
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → χ g = 1) g.val g.det_ne_zero
    (fun D _ => hdiag D) htr ?_ g rfl
  intro A B hA hB pA pB u hu
  have : u = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB :=
    Units.ext hu
  rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]
end GlobalTheory
