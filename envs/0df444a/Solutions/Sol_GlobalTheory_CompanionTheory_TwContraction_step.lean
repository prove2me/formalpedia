-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:39:40.707618+00:00
-- url     : https://prove2.me/submissions/77dad5b0-5a6c-4541-b8f8-d07e7bf9daf5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_Dp_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_Dp_add
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_Dp_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_det_sub_prod_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_mem_unitGL_entries
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_mem_unitGL_of
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_diag_of_mem_iwahori

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = iwahori (m := n) F)
    (τ : F ≃+* F) (hτ : ∀ a, valuation F (τ a) = valuation F a)
    (hτU : ∀ g ∈ U, Matrix.GeneralLinearGroup.map (τ : F →+* F) g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (j : ℕ) (c : GL (Fin n) F) (hcU : c ∈ U)
    (hcD : ∀ i l, i ≠ l → valuation F ((c : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j) :
    ∃ p ∈ U, x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p ∈ U ∧
      ∀ i l, i ≠ l → valuation F (((x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ (j + 1) := by
  have hI : c ∈ iwahori (m := n) F := by rw [← hU]; exact hcU
  have hρ1' : ρ ≤ 1 := hρ1.le
  set C : Matrix (Fin n) (Fin n) F := (c : Matrix (Fin n) (Fin n) F) with hCdef
  let d : Fin n → F := fun i => C i i
  have hd : ∀ i, valuation F (d i) = 1 := fun i => val_diag_of_mem_iwahori hI i
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hτs : ∀ a, valuation F (τ.symm a) = valuation F a := fun a => by
    have := hτ (τ.symm a)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hev : ∀ i, valuation F (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).2 (he i)
  have hq : ∀ i l, i < l → valuation F (e i / e l) ≤ ρ := fun i l h => by
    rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 (hev l))]
    exact hc i l h
  set s : ℕ := max j 1 with hs
  have hs1 : 1 ≤ s := le_max_right _ _
  have hjs : j ≤ s := le_max_left _ _
  have hsj : s ≤ j + 1 := max_le (Nat.le_succ j) (Nat.le_add_left 1 j)
  have hlow : ∀ i l, l < i → valuation F (C i l) ≤ ρ ^ s := fun i l h => by
    rcases max_choice j 1 with h' | h'
    · rw [hs, h']; exact hcD i l h.ne'
    · rw [hs, h', pow_one]; exact hunif _ (hI.2 i l h)
  let T : Matrix (Fin n) (Fin n) F := fun i l =>
    if l < i then - τ.symm (C i l / d i) else if i < l then (e i / e l) * (C i l / d l) else 0
  have hTlo : ∀ i l, l < i → T i l = - τ.symm (C i l / d i) := fun i l h => if_pos h
  have hTup : ∀ i l, i < l → T i l = (e i / e l) * (C i l / d l) := fun i l h => by
    show (if l < i then _ else _) = _
    rw [if_neg (not_lt.2 h.le), if_pos h]
  have hTd : ∀ i, T i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hTlov : ∀ i l, l < i → valuation F (T i l) ≤ ρ ^ s := fun i l h => by
    rw [hTlo i l h, Valuation.map_neg, hτs, map_div₀, hd, div_one]
    exact hlow i l h
  have hTupv : ∀ i l, i < l → valuation F (T i l) ≤ ρ ^ (j + 1) := fun i l h => by
    rw [hTup i l h, map_mul, map_div₀ _ (C i l), hd, div_one, pow_succ']
    exact mul_le_mul' (hq i l h) (hcD i l h.ne)
  have hT : Dp ρ s T := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · exact (hTupv i l h).trans (pow_le_pow_right_of_le_one' hρ1' hsj)
    · subst h; rw [hTd, map_zero]; exact zero_le'
    · exact hTlov i l h
  have hρs : ρ ^ s ≤ ρ := by
    calc ρ ^ s ≤ ρ ^ 1 := pow_le_pow_right_of_le_one' hρ1' hs1
      _ = ρ := pow_one ρ
  set P : Matrix (Fin n) (Fin n) F := 1 + T with hP
  have hPd : ∀ i, P i i = 1 := fun i => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_eq, hTd, add_zero]
  have hPo : ∀ i l, i ≠ l → P i l = T i l := fun i l h => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_ne h, zero_add]
  have hPint : ∀ i l, valuation F (P i l) ≤ 1 := fun i l => by
    by_cases h : i = l
    · subst h; rw [hPd, map_one]
    · rw [hPo i l h]; exact (hT i l).trans (hρs.trans hρ1')
  have hPlow : ∀ i l, l < i → valuation F (P i l) < 1 := fun i l h => by
    rw [hPo i l h.ne']
    exact lt_of_le_of_lt ((hT i l).trans hρs) hρ1
  have hPdet : valuation F P.det = 1 := by
    have h1 := val_det_sub_prod_lt P hPint hPlow
    rw [Finset.prod_congr rfl fun i _ => hPd i, Finset.prod_const_one] at h1
    have := Valuation.map_eq_of_sub_lt (valuation F) (x := (1 : F)) (y := P.det) (by rwa [map_one])
    rwa [map_one] at this
  have hPne : P.det ≠ 0 := fun h => by
    rw [h, map_zero] at hPdet
    exact zero_ne_one hPdet
  let p : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPne
  have hpv : (p : Matrix (Fin n) (Fin n) F) = P := rfl
  have hpU : p ∈ U := by
    have : p ∈ iwahori (m := n) F := ⟨mem_unitGL_of p hPint hPdet, hPlow⟩
    rw [← hU] at this
    exact this
  have hxinv : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (e i)⁻¹ := by
    rw [Matrix.coe_units_inv, hx]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he i)
  let q : GL (Fin n) F := x⁻¹ * p * x
  set Q : Matrix (Fin n) (Fin n) F := (q : Matrix (Fin n) (Fin n) F) with hQdef
  have hQ : ∀ i l, Q i l = (e i)⁻¹ * P i l * e l := fun i l => by
    show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l = _
    rw [Units.val_mul, Units.val_mul, hxinv, hx, hpv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hQd : ∀ i, Q i i = 1 := fun i => by
    rw [hQ, hPd, mul_one, inv_mul_cancel₀ (he i)]
  have hQup : ∀ i l, i < l → Q i l = C i l / d l := fun i l h => by
    rw [hQ, hPo i l h.ne, hTup i l h]
    have h1 := he i
    have h2 := he l
    field_simp
  have hQlow : ∀ i l, l < i → valuation F (Q i l) ≤ ρ * ρ ^ s := fun i l h => by
    rw [hQ, hPo i l h.ne', show (e i)⁻¹ * T i l * e l = (e l / e i) * T i l by
      rw [div_eq_mul_inv]; ring, map_mul]
    exact mul_le_mul' (hq l i h) (hTlov i l h)
  have hQint : ∀ i l, valuation F (Q i l) ≤ 1 := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, map_div₀, hd, div_one]
      exact mem_unitGL_entries hI.1 i l
    · subst h; rw [hQd, map_one]
    · refine (hQlow i l h).trans ?_
      calc ρ * ρ ^ s ≤ 1 * 1 := mul_le_mul' hρ1' (hρs.trans hρ1')
        _ = 1 := one_mul 1
  have hQdet : valuation F Q.det = 1 := by
    have : Q.det = P.det := by
      show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = _
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hpv]
      have h3 : (x : Matrix (Fin n) (Fin n) F).det * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
        simp
      calc _ = P.det * ((x : Matrix (Fin n) (Fin n) F).det *
            ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) := by ring
        _ = P.det := by rw [h3, mul_one]
    rw [this]; exact hPdet
  have hqU : q ∈ U := by
    have : q ∈ iwahori (m := n) F := ⟨mem_unitGL_of q hQint hQdet, fun i l h =>
      lt_of_le_of_lt (hQlow i l h) (lt_of_le_of_lt (mul_le_mul' le_rfl hρs) (by
        calc ρ * ρ ≤ ρ * 1 := mul_le_mul' le_rfl hρ1'
          _ = ρ := mul_one ρ
          _ < 1 := hρ1 |>.trans_le le_rfl))⟩
    rw [← hU] at this
    exact this
  let T' : Matrix (Fin n) (Fin n) F := T.map τ
  have hT' : Dp ρ s T' := fun i l => by
    show valuation F (τ (T i l)) ≤ _
    rw [hτ]; exact hT i l
  let Dg : Matrix (Fin n) (Fin n) F := Matrix.diagonal d
  let Co : Matrix (Fin n) (Fin n) F := C - Dg
  have hCo : Dp ρ j Co := fun i l => by
    by_cases h : i = l
    · subst h
      show valuation F (C i i - Dg i i) ≤ _
      rw [show Dg i i = C i i from Matrix.diagonal_apply_eq _ _, sub_self, map_zero]
      exact zero_le'
    · show valuation F (C i l - Dg i l) ≤ _
      rw [show Dg i l = 0 from Matrix.diagonal_apply_ne _ h, sub_zero]
      exact hcD i l h
  let B : Matrix (Fin n) (Fin n) F := C + Dg * T' - Q * Dg
  have hBe : ∀ i l, B i l = C i l + d i * τ (T i l) - Q i l * d l := fun i l => by
    show (C + Dg * T' - Q * Dg) i l = _
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rfl
  have hB : Dp ρ (j + 1) B := fun i l => by
    rw [hBe]
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, div_mul_cancel₀ _ (hd0 l), add_sub_cancel_left, map_mul, hd, one_mul, hτ]
      exact hTupv i l h
    · subst h
      rw [hTd, hQd, map_zero, mul_zero, add_zero, one_mul]
      show valuation F (C i i - C i i) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    · rw [hTlo i l h, map_neg, RingEquiv.apply_symm_apply, mul_neg, mul_div_cancel₀ _ (hd0 i),
        add_neg_cancel, zero_sub, Valuation.map_neg, map_mul, hd, mul_one]
      refine (hQlow i l h).trans ?_
      rw [← pow_succ']
      exact pow_le_pow_right_of_le_one' hρ1' (Nat.succ_le_succ hjs)
  let R : Matrix (Fin n) (Fin n) F := B + Co * T'
  have hR : Dp ρ (j + 1) R :=
    hB.add ((hCo.mul hT').mono hρ1' (Nat.add_le_add_left hs1 j))
  have hPτ : P.map τ = 1 + T' := by
    rw [hP, Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hid : C * P.map τ = Q * Dg + R := by
    rw [hPτ]
    show C * (1 + T') = Q * Dg + (C + Dg * T' - Q * Dg + (C - Dg) * T')
    noncomm_ring
  have hw : x⁻¹ * p⁻¹ * x * c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p =
      q⁻¹ * (c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p) := by
    show _ = (x⁻¹ * p * x)⁻¹ * _
    group
  refine ⟨p, hpU, ?_, ?_⟩
  · rw [hw]
    exact U.mul_mem (U.inv_mem hqU) (U.mul_mem hcU (hτU p hpU))
  · intro i l hil
    rw [hw]
    have hval : ((q⁻¹ * (c * Matrix.GeneralLinearGroup.map (τ : F →+* F) p) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = Dg + ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * R := by
      rw [Units.val_mul, Units.val_mul]
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (C * P.map τ) = _
      rw [hid, mul_add, ← mul_assoc]
      congr 1
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (q : Matrix (Fin n) (Fin n) F) * Dg = Dg
      rw [← Units.val_mul, inv_mul_cancel]
      simp
    rw [hval, Matrix.add_apply, show Dg i l = 0 from Matrix.diagonal_apply_ne _ hil, zero_add]
    have hq0 : Dp ρ 0 ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [pow_zero]
      have : q⁻¹ ∈ iwahori (m := n) F := by
        rw [← hU]; exact U.inv_mem hqU
      exact mem_unitGL_entries this.1 a b
    have := (hq0.mul hR) i l
    rwa [zero_add] at this
end GlobalTheory.CompanionTheory.TwContraction
