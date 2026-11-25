-- Prove2me | solution 1 for GlobalTheory.FrameDet.det_dvd_of_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:08.663901+00:00
-- url     : https://prove2.me/submissions/53931640-9b13-4c03-b026-6f3b75dd0c43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DetDvdEquivariantFramePolynomial
import Theorems.Thm_GlobalTheory_FrameDet_exists_lower
import Theorems.Thm_GlobalTheory_BorelAlg_gen_det_ne_zero
import Theorems.Thm_GlobalTheory_BorelAlg_inj_block
import Theorems.Thm_P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPolynomial Formalism.L2.LamCM
open GlobalTheory GlobalTheory.FrameDet
open GlobalTheory.BorelAlg
namespace GlobalTheory.FrameDet
theorem _root_.solution : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by
  intro K _ _ B _ _ m P a hP τ₀ ha
  have hT : (Matrix.of fun i k : Fin (m τ₀) => (MvPolynomial.X ⟨τ₀, (k, i)⟩ : MvPolynomial (FrVar m) K)).det =
      (gen m K τ₀).det := by
    rw [← Matrix.det_transpose]; rfl
  rw [hT]
  change (gen m K τ₀).det ∣ P
  by_cases h0 : m τ₀ = 0
  · haveI : IsEmpty (Fin (m τ₀)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty]; exact one_dvd _
  let l : Fin (m τ₀) := ⟨m τ₀ - 1, by omega⟩
  have hl : ∀ i, i ≤ l := fun i => by
    have := i.2
    simp only [Fin.le_def, l]; omega
  obtain ⟨hM0, hrel⟩ := minor_isRelPrime' (R := K) _ (inj_block m τ₀) l hl
  change ((gen m K τ₀).updateRow l (Pi.single l 1)).det ≠ 0 at hM0
  change IsRelPrime ((gen m K τ₀).updateRow l (Pi.single l 1)).det (gen m K τ₀).det at hrel
  set M := (gen m K τ₀).updateRow l (Pi.single l 1) with hM
  let x₀ : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) K) :=
    Function.update (gen m K) τ₀ M
  let P₀ : MvPolynomial (Lt m) K := eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2) P
  let D : MvPolynomial (Lt m) K := (∏ τ, (gen m K τ).det) * M.det
  have hD : D ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => gen_det_ne_zero m K τ) hM0
  have k3 : P * M.det ^ a τ₀ l = (gen m K τ₀).det ^ a τ₀ l * P₀ := by
    apply mul_left_cancel₀ hD
    apply MvPolynomial.funext
    intro z
    by_cases hz : eval z D = 0
    · rw [map_mul, map_mul (eval z) D, hz, zero_mul, zero_mul]
    rw [map_mul, map_mul (eval z) D]
    congr 1
    let g : MvPolynomial (Lt m) K →+* K := eval z
    let x := fun τ => g.mapMatrix (x₀ τ)
    let y := fun τ => g.mapMatrix (gen m K τ)
    have hxd : ∀ τ, (x τ).det = g (x₀ τ).det := fun τ => (RingHom.map_det _ _).symm
    have hyd : ∀ τ, (y τ).det = g (gen m K τ).det := fun τ => (RingHom.map_det _ _).symm
    have hxM : (x τ₀).det = g M.det := by rw [hxd]; simp [x₀]
    have hz' : (∏ τ, g (gen m K τ).det) * g M.det ≠ 0 := by
      rw [← map_prod, ← map_mul]; exact hz
    have hy : ∀ τ, (y τ).det ≠ 0 := fun τ =>
      hyd τ ▸ Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hz') τ (Finset.mem_univ _)
    have hne : ∀ τ, τ ≠ τ₀ → y τ = x τ := fun τ h => by simp [x, y, x₀, h]
    have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => by
      by_cases h : τ = τ₀
      · subst h; rw [hxM]; exact right_ne_zero_of_mul hz'
      · rw [← hne τ h]; exact hy τ
    have hl' : ∀ i, i ≠ l → y τ₀ i = x τ₀ i := fun i h => by
      ext j; simp [x, y, x₀, M, Matrix.updateRow_ne h]
    obtain ⟨b, hxy, hb, hb1, hdet⟩ := exists_lower (x τ₀) (y τ₀) l hl (hx τ₀) hl'
    have hs : (y τ₀).det = b l l * (x τ₀).det := by rw [← hdet, ← Matrix.det_mul, ← hxy]
    have key := hP (fun τ => (x τ).transpose) τ₀ b.transpose
      (fun τ => by rw [Matrix.det_transpose]; exact hx τ)
      (by rw [Matrix.det_transpose, hdet]; exact left_ne_zero_of_mul (hs ▸ hy τ₀))
      (fun i j hij => hb j i hij)
    have e0 : Function.update (fun τ => (x τ).transpose) τ₀ ((x τ₀).transpose * b.transpose) =
        fun τ => (y τ).transpose := by
      funext τ
      by_cases h : τ = τ₀
      · subst h; rw [Function.update_self, ← Matrix.transpose_mul, ← hxy]
      · rw [Function.update_of_ne h, hne τ h]
    have e1 : evalFr P (fun τ => (y τ).transpose) = g P := by
      unfold evalFr
      congr 2
      funext v
      simp [y, g, gen]
    have e2 : evalFr P (fun τ => (x τ).transpose) = g P₀ := by
      have : (eval (fun v : FrVar m => (x v.1).transpose v.2.2 v.2.1) : MvPolynomial (Lt m) K →+* K) =
          g.comp (eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2)) := by
        ext <;> simp [x, g]
      unfold evalFr
      rw [this]; rfl
    have hc : (∏ i, b.transpose i i ^ a τ₀ i) = b l l ^ a τ₀ l := by
      rw [Finset.prod_eq_single l]
      · rfl
      · intro i _ hi; rw [Matrix.transpose_apply, hb1 i hi, one_pow]
      · simp
    rw [e0, e1, e2, hc] at key
    change g _ = g _
    rw [map_mul, map_mul, map_pow, map_pow, ← hxM, ← hyd, key, hs]
    ring
  have hd : (gen m K τ₀).det ^ a τ₀ l ∣ P :=
    (hrel.symm.pow (m := a τ₀ l) (n := a τ₀ l)).dvd_of_dvd_mul_right ⟨_, k3⟩
  exact (dvd_pow_self _ (by have := ha l; omega)).trans hd
end GlobalTheory.FrameDet
