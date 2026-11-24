-- Prove2me | solution 1 for GlobalTheory.DetInv.datum_scalar_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:41:03.18036+00:00
-- url     : https://prove2.me/submissions/a0701d3d-74d4-463c-9782-8859b127c55a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MuCoeffZeroNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SandwichDatumScalarAction
import Theorems.Thm_GlobalTheory_AinfXi_isDomain_ainf
import Theorems.Thm_GlobalTheory_AinfXi_xi_nzd
import Theorems.Thm_GlobalTheory_DetInv_mu_coeff_zero_ne_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_xi_nzd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
namespace GlobalTheory.DetInv.Intertwine
variable {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
end GlobalTheory.DetInv.Intertwine
namespace GlobalTheory.DetInv
open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_right_cancel_lemma {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B X : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hX : X * B = 0) : X = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hB : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : X * B * B.adjugate = B.det • X := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [hX, Matrix.zero_mul] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hB
open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_left_cancel_lemma_2 {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B Y : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hY : A * Y = 0) : Y = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : A.adjugate * (A * Y) = A.det • Y := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hY, Matrix.mul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hA
end GlobalTheory.DetInv
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv
open Matrix TensorProduct
namespace GlobalTheory.DetInv
namespace _root_.GlobalTheory.DetInv
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ), (∀ c : ℤ_[p], D.ρM (algebraMap ℤ_[p] Λ c) = _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O))) ∧ D.F * D.G = _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧ (∀ l, D.G * D.ρM l = _root_.GlobalTheory.DetInv.rhoTA D l * D.G) ∧ (∀ l, D.Ψ * (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) = D.ρM l * D.Ψ) ∧ ∀ l, D.Ψ' * D.ρM l = (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) * D.Ψ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  set F := D.F with hF
  set G := D.G with hG
  set Ψ := D.Ψ with hΨ
  set Ψ' := D.Ψ' with hΨ'
  set M := D.ρM with hM
  set φ := _root_.GlobalTheory.Sandwich.phiInv p O with hφ
  have hμ : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 :=
    (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.1
  have hμ' : φ (_root_.GlobalTheory.Sandwich.mu ε) ≠ 0 := by
    rw [hφ, _root_.GlobalTheory.Sandwich.phiInv_mu]
    exact (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.2
  have hξ : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    have h1 := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε 1 (by rw [h0, mul_zero])
    exact one_ne_zero h1
  have hGF : G * F = _root_.GlobalTheory.Sandwich.mu ε • 1 := D.G_mul_F
  have hFΨ : F = Ψ * F.map φ := D.F_eq
  have hΨΨ' : Ψ * Ψ' = _root_.GlobalTheory.Sandwich.xi ε • 1 := D.Ψ_mul
  have hFT : ∀ l, F * _root_.GlobalTheory.DetInv.rhoTA D l = M l * F := fun l =>
    D.F_act l

  have hFG : F * G = _root_.GlobalTheory.Sandwich.mu ε • 1 := by
    have h0 : (F * G - _root_.GlobalTheory.Sandwich.mu ε • 1) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)

  have hTφ : ∀ l, (_root_.GlobalTheory.DetInv.rhoTA D l).map φ = _root_.GlobalTheory.DetInv.rhoTA D l := by
    intro l
    unfold _root_.GlobalTheory.DetInv.rhoTA
    rw [Matrix.map_map]
    congr 1
    funext x
    exact _root_.GlobalTheory.DetInv.PsiPhi.phiInv_ofPadic x

  have hFTφ : ∀ l, F.map φ * _root_.GlobalTheory.DetInv.rhoTA D l = (M l).map φ * F.map φ := by
    intro l
    have := congrArg (fun X => X.map φ) (hFT l)
    simp only [Matrix.map_mul] at this
    rwa [hTφ] at this
  have hGFφ : G.map φ * F.map φ = φ (_root_.GlobalTheory.Sandwich.mu ε) • 1 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hΨM : ∀ l, Ψ * (M l).map φ = M l * Ψ := by
    intro l
    have h0 : (Ψ * (M l).map φ - M l * Ψ) * F.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFTφ, ← Matrix.mul_assoc, ← hFΨ, hFT,
        Matrix.mul_assoc, ← hFΨ, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGFφ hμ' h0)
  refine ⟨?_, hFG, ?_, hΨM, ?_⟩
  · intro c
    have hT : _root_.GlobalTheory.DetInv.rhoTA D (algebraMap ℤ_[p] Λ c) =
        _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) := by
      unfold _root_.GlobalTheory.DetInv.rhoTA
      rw [AlgHom.commutes]
      ext i j
      simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 := hFT (algebraMap ℤ_[p] Λ c)
    rw [hT] at h1
    have h0 : (M (algebraMap ℤ_[p] Λ c) - _root_.GlobalTheory.Sandwich.ofPadic p O c • 1) * F = 0 := by
      rw [Matrix.sub_mul, ← h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : (G * M l - _root_.GlobalTheory.DetInv.rhoTA D l * G) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hGF, Matrix.mul_assoc,
        hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : Ψ * (Ψ' * M l - (M l).map φ * Ψ') = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hΨΨ', ← Matrix.mul_assoc, hΨM, Matrix.mul_assoc,
        hΨΨ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_left_cancel_lemma_2 hΨΨ' hξ h0)
end _root_.GlobalTheory.DetInv
end GlobalTheory.DetInv
