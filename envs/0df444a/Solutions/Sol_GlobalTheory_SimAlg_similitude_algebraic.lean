-- Prove2me | solution 1 for GlobalTheory.SimAlg.similitude_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:14:59.84411+00:00
-- url     : https://prove2.me/submissions/a20a5515-08d6-4897-b76a-b7b6019c4b4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_exists_polar
import Theorems.Thm_GlobalTheory_SimAlg_complex_pos
import Theorems.Thm_GlobalTheory_SimAlg_gram_pos
import Theorems.Thm_GlobalTheory_SimAlg_exists_ann
import Theorems.Thm_GlobalTheory_SimAlg_form_sum
import Theorems.Thm_GlobalTheory_SimAlg_form_shift
import Theorems.Thm_GlobalTheory_SimAlg_form_symm
import Theorems.Thm_GlobalTheory_SimAlg_form_ann

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution : ∀ (Λ : Type) [AddCommGroup Λ] (Q : Λ → ℤ) (φ : Module.End ℤ Λ) (e : Λ) (q l r : ℕ), 2 ≤ l → (∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) → (∀ x, 0 ≤ Q x) → (∀ x, Q x = 0 → x = 0) → (∀ x, Q (φ x) = q * Q x) → (∀ n : ℕ, ∃ (χ : Polynomial ℤ) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ Polynomial.aeval φ χ e = l ^ n • y) → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval φ P e = 0 ∧ ∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q := by
  classical
  intro Λ _ Q φ e q l r hl hpar h0 hdef hφ hχ
  obtain ⟨b, hb, hbb⟩ := exists_polar Q hpar
  have hpos : ∀ x, x ≠ 0 → 0 < b x x := by
    intro x hx
    have := h0 x
    have h' : Q x ≠ 0 := fun h => hx (hdef x h)
    rw [hbb]; omega
  obtain ⟨P₀, hP₀, hP₀'⟩ := exists_ann b hpos φ e l r hl hχ
  have hex : ∃ d : ℕ, ∃ P : ℤ[X], P ≠ 0 ∧ aeval φ P e = 0 ∧ P.natDegree = d := ⟨_, P₀, hP₀, hP₀', rfl⟩
  obtain ⟨P, hP, hPe, hPd⟩ := Nat.find_spec hex
  set d := Nat.find hex with hd
  have hmin : ∀ R : ℤ[X], R ≠ 0 → R.degree < d → aeval φ R e ≠ 0 := by
    intro R hR hRd hRe
    exact Nat.find_min hex ((natDegree_lt_iff_degree_lt hR).2 hRd) ⟨R, hR, hRe, rfl⟩
  refine ⟨P, hP, hPe, fun β hβ => ?_⟩
  set g : ℕ → ℕ → ℤ := fun i j => b ((φ ^ i) e) ((φ ^ j) e) with hg
  have hsymm : ∀ i j, g i j = g j i := by
    intro i j; simp only [hg, hb]; rw [add_comm]; ring
  have hshift : ∀ i j, g (i + 1) (j + 1) = (q : ℤ) * g i j := by
    intro i j
    simp only [hg, hb, pow_succ', Module.End.mul_apply, ← map_add, hφ]; ring
  set Pc := P.map (Int.castRingHom ℂ) with hPc
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hPc0 : Pc ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hP
  have hPcd : Pc.natDegree = d := by rw [hPc, natDegree_map_eq_of_injective hinj, hPd]
  have hroot : Pc.IsRoot β := by
    rw [IsRoot, hPc, eval_map]; exact hβ
  obtain ⟨f, hf⟩ := dvd_iff_isRoot.2 hroot
  have hf0 : f ≠ 0 := by rintro rfl; simp [hf] at hPc0
  have hfd : f.natDegree < d := by
    rw [← hPcd, hf, natDegree_mul (X_sub_C_ne_zero β) hf0, natDegree_X_sub_C]; omega
  set f' := f.map (starRingEnd ℂ) with hf'
  have hf'd : f'.natDegree < d := lt_of_le_of_lt natDegree_map_le hfd
  have hconj : Pc = (X - C ((starRingEnd ℂ) β)) * f' := by
    have : Pc.map (starRingEnd ℂ) = Pc := by
      rw [hPc, Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
    rw [← this, hf]; simp [hf']
  have e1 : X * f = β • f + Pc := by rw [hf, smul_eq_C_mul]; ring
  have e2 : X * f' = (starRingEnd ℂ) β • f' + Pc := by rw [hconj, smul_eq_C_mul]; ring
  have a1 : ∀ h, form g Pc h = 0 := form_ann b φ e P hPe
  have a2 : ∀ h, form g h Pc = 0 := fun h => by rw [form_symm g hsymm, a1]
  have main := form_shift g q hshift f f'
  rw [e1, e2] at main
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, a1, a2, add_zero,
    smul_eq_mul, mul_zero] at main
  have hne : form g f f' ≠ 0 := by
    intro hz
    rw [form_sum g d f f' hfd hf'd] at hz
    have := complex_pos (Matrix.of fun i j : Fin d => g i j) (fun i j => hsymm i j)
      (gram_pos b hpos φ e d hmin) (fun i => f.coeff i) (by simpa [hf'] using hz)
    exact hf0 (leadingCoeff_eq_zero.1 (congrFun this ⟨f.natDegree, hfd⟩))
  have : ((Complex.normSq β : ℝ) : ℂ) = (q : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    apply mul_right_cancel₀ hne
    push_cast at main
    linear_combination main
  exact_mod_cast this
end GlobalTheory.SimAlg
