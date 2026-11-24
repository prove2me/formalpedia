-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.witt_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:52:08.862373+00:00
-- url     : https://prove2.me/submissions/8c59c0ae-7c2d-4465-baf3-28c8824bbc11

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_core
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_cT_mul
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_cT_add
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_cT_smul
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_cT_one
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_cT_cT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {E : Type} [CommRing E] (σ : E →+* E)
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution {F : Type} [Field F] (hσ : ∀ x, σ (σ x) = x) (e : E) (he2 : e * e = e)
    (he1 : e + σ e = 1) (π : E →+* F) (s : F → E) (hs1 : ∀ f, π (s f) = f)
    (hs2 : ∀ x, s (π x) = e * x) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J)
    (X X' : Matrix (Fin n) (Fin a) E) (hX : Free X) (hX' : Free X')
    (hG : pairM σ J X X = pairM σ J X' X') : ∃ g, IsUn σ J g ∧ g * X = X' := by
  have hee' : e * σ e = 0 := by linear_combination e * he1 - he2
  have he'e : σ e * e = 0 := by rw [mul_comm]; exact hee'

  have K1 : ∀ {p q : Type} (P : Matrix p q E), (P.map π).map s = e • P := by
    intro p q P; ext i j; simp [hs2]
  have K2 : ∀ {p q : Type} (P : Matrix p q F), (P.map s).map π = P := by
    intro p q P; ext i j; simp [hs1]
  have K3 : ∀ {p q : Type} (P : Matrix p q F), e • P.map s = P.map s := by
    intro p q P; ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have := hs2 (s (P i j)); rw [hs1] at this; exact this.symm
  have T : ∀ {p q : Type} (P Q : Matrix p q E), P.map π = Q.map π → e • P = e • Q := by
    intro p q P Q h; rw [← K1, ← K1, h]

  obtain ⟨L, hL⟩ := hX
  obtain ⟨L', hL'⟩ := hX'
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ.2
  set M := J.map π with hMdef
  have hM : IsUnit M.det := by
    have h := hJ.2.map π; rw [RingHom.map_det] at h; exact h
  have hright : ∀ (Y : Matrix (Fin n) (Fin a) E) (LY : Matrix (Fin a) (Fin n) E), LY * Y = 1 →
      (cT σ Y * J) * (J⁻¹ * cT σ LY) = 1 := by
    intro Y LY h
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJJ, Matrix.one_mul, ← cT_mul, h, cT_one]
  obtain ⟨A, hA, hAu, hφA⟩ := core (X.map π) (X'.map π) ((cT σ X * J).map π) ((cT σ X' * J).map π)
    ⟨L.map π, by rw [← Matrix.map_mul, hL, Matrix.map_one π (map_zero π) (map_one π)]⟩
    ⟨L'.map π, by rw [← Matrix.map_mul, hL', Matrix.map_one π (map_zero π) (map_one π)]⟩
    ⟨(J⁻¹ * cT σ L).map π, by rw [← Matrix.map_mul, hright X L hL, Matrix.map_one π (map_zero π) (map_one π)]⟩
    ⟨(J⁻¹ * cT σ L').map π, by rw [← Matrix.map_mul, hright X' L' hL', Matrix.map_one π (map_zero π) (map_one π)]⟩
    (by rw [← Matrix.map_mul, ← Matrix.map_mul]; unfold pairM at hG; rw [hG])
  have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hMM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hMM' : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  set C : Matrix (Fin n) (Fin n) F := M * A⁻¹ * M⁻¹ with hCdef
  set Ah := A.map s
  set Ch := C.map s
  have hAh : e • Ah = Ah := K3 A
  have hCh : e • Ch = Ch := K3 C

  have F1 : Ch * J * Ah = e • J := by
    have : e • (Ch * J * Ah) = e • J := T _ _ (by
      rw [Matrix.map_mul, Matrix.map_mul, K2, K2, ← hMdef, hCdef]
      rw [show M * A⁻¹ * M⁻¹ * M * A = M * A⁻¹ * (M⁻¹ * M) * A by simp only [Matrix.mul_assoc],
        hMM, Matrix.mul_one, Matrix.mul_assoc, hAA, Matrix.mul_one])
    rw [← this, ← hCh, Matrix.smul_mul, Matrix.smul_mul, smul_smul, he2]

  have F2 : cT σ X * Ch = e • cT σ X' := by
    have : e • (cT σ X * Ch) = e • cT σ X' := T _ _ (by
      rw [Matrix.map_mul, K2, hCdef]
      have h3 : (cT σ X).map π * M = ((cT σ X' * J).map π) * A := by
        rw [hφA, Matrix.map_mul]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.map_mul, ← hMdef,
        show (cT σ X').map π * M * A * A⁻¹ * M⁻¹ = (cT σ X').map π * (M * (A * A⁻¹) * M⁻¹) by
          simp only [Matrix.mul_assoc],
        Matrix.mul_nonsing_inv A hA, Matrix.mul_one, hMM', Matrix.mul_one])
    calc cT σ X * Ch = e • (cT σ X * Ch) := by rw [← Matrix.mul_smul, hCh]
      _ = e • cT σ X' := this
  have F3 : Ah * X = e • X' := by
    rw [← T (Ah * X) X' (by rw [Matrix.map_mul, K2, hAu]), ← Matrix.smul_mul, hAh]
  refine ⟨Ah + cT σ Ch, ?_, ?_⟩
  · unfold IsUn
    have hJc : cT σ J = J := hJ.1
    rw [cT_add, cT_cT σ hσ, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have z1 : cT σ Ah * J * Ah = 0 := by
      rw [← hAh, cT_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he'e, zero_smul]
    have z2 : Ch * J * cT σ Ch = 0 := by
      rw [← hCh, cT_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee', zero_smul]
    have z3 : cT σ Ah * J * cT σ Ch = σ e • J := by
      have h4 : cT σ (Ch * J * Ah) = cT σ Ah * J * cT σ Ch := by
        rw [cT_mul, cT_mul, hJc, ← Matrix.mul_assoc]
      rw [← h4, F1, cT_smul, hJc]
    rw [z1, z2, z3, F1, zero_add, add_zero, ← add_smul, add_comm, he1, one_smul]
  · rw [Matrix.add_mul, F3]
    have : cT σ Ch * X = σ e • X' := by
      rw [← cT_cT σ hσ X, ← cT_mul, F2, cT_smul, cT_cT σ hσ]
    rw [this, ← add_smul, he1, one_smul]
end GlobalTheory.SgAlg.WittSplit
