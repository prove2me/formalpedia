-- Prove2me | solution 1 for GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:20.562185+00:00
-- url     : https://prove2.me/submissions/23c62190-4276-4429-a91c-46fb6c90ee73

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_cT_map
import Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_cT_cT
import Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_exists_poly_norm
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cT_map
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitaryDoubleCoset
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
open IsDedekindDomain NumberField
open scoped TensorProduct Matrix
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.UnitaryDoubleCoset
namespace _root_.GlobalTheory.UnitaryDoubleCoset
theorem _root_.solution (ι : O →+* L) {c : O →+* O} {σ : L →+* L}
    (hι : ∀ x, σ (ι x) = ι (c x))
    (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {g g' : GL n L} (hg : g ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L)) (hg' : g' ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L))
    (h k : GL n O) (e : g' = _root_.Formalism.UG.bc ι h * g * _root_.Formalism.UG.bc ι k) :
    ∃ k₁ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L) ⊓ (_root_.Formalism.UG.bc ι).range, ∃ k₂ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L),
      (∃ M : Matrix n n O, (k₂ : Matrix n n L) = M.map ι) ∧ g' = k₁ * g * k₂ := by
  have hmul : ∀ {R : Type} [CommRing R] (τ : R →+* R) (A B : Matrix n n R),
      _root_.Formalism.UG.cT τ (A * B) = _root_.Formalism.UG.cT τ B * _root_.Formalism.UG.cT τ A := by
    intro R _ τ A B
    simp [_root_.Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hone : ∀ {R : Type} [CommRing R] (τ : R →+* R), _root_.Formalism.UG.cT τ (1 : Matrix n n R) = 1 := by
    intro R _ τ
    simp [_root_.Formalism.UG.cT]

  have hinv : ∀ u : GL n L, _root_.Formalism.UG.cT σ (u : Matrix n n L) * u = 1 →
      _root_.Formalism.UG.cT σ (u : Matrix n n L) = ((u⁻¹ : GL n L) : Matrix n n L) ∧
        _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) = u := by
    intro u hu
    have h1 : _root_.Formalism.UG.cT σ (u : Matrix n n L) = ((u⁻¹ : GL n L) : Matrix n n L) := by
      calc _root_.Formalism.UG.cT σ (u : Matrix n n L) = _root_.Formalism.UG.cT σ (u : Matrix n n L) * (u * ↑u⁻¹) := by
            rw [Units.mul_inv, mul_one]
        _ = ((u⁻¹ : GL n L) : Matrix n n L) := by rw [← mul_assoc, hu, one_mul]
    refine ⟨h1, ?_⟩
    have h2 : _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) * ((u⁻¹ : GL n L) : Matrix n n L) = 1 := by
      have h3 := hmul σ (u : Matrix n n L) ((u⁻¹ : GL n L) : Matrix n n L)
      rw [Units.mul_inv, hone, h1] at h3
      exact h3.symm
    calc _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L)
        = _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) * (((u⁻¹ : GL n L) : Matrix n n L) * u) := by
          rw [Units.inv_mul, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hg1 : _root_.Formalism.UG.cT σ (g : Matrix n n L) * g = 1 := by simpa [_root_.Formalism.UG.UJ] using hg
  have hg'1 : _root_.Formalism.UG.cT σ (g' : Matrix n n L) * g' = 1 := by simpa [_root_.Formalism.UG.UJ] using hg'
  have hbc : ∀ u : GL n O, ((_root_.Formalism.UG.bc ι u : GL n L) : Matrix n n L) = (u : Matrix n n O).map ι := by
    intro u
    simp [_root_.Formalism.UG.bc]

  set H := _root_.Formalism.UG.cT c (h : Matrix n n O) * h with hHdef
  have hH : _root_.Formalism.UG.cT c H = H := by
    rw [hHdef, hmul, _root_.GlobalTheory.UnitaryDoubleCoset.cT_cT hc]
  have hHu : IsUnit H := by
    refine IsUnit.mul (IsUnit.of_mul_eq_one (_root_.Formalism.UG.cT c ((h⁻¹ : GL n O) : Matrix n n O)) ?_) h.isUnit
    rw [← hmul, Units.inv_mul, hone]
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc hN hH hHu
  set P := Polynomial.aeval H p with hPdef
  have hPu : IsUnit P := isUnit_of_mul_isUnit_right (hp.symm ▸ hHu)
  set k₁ : GL n L := _root_.Formalism.UG.bc ι (h * hPu.unit⁻¹) with hk₁def
  have hk₁ : k₁ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L) := by
    have hO : _root_.Formalism.UG.cT c ((h * hPu.unit⁻¹ : GL n O) : Matrix n n O) *
        ((h * hPu.unit⁻¹ : GL n O) : Matrix n n O) = 1 := by
      rw [Units.val_mul, hmul]
      calc _root_.Formalism.UG.cT c ((hPu.unit⁻¹ : GL n O) : Matrix n n O) * _root_.Formalism.UG.cT c (h : Matrix n n O) *
            ((h : Matrix n n O) * ((hPu.unit⁻¹ : GL n O) : Matrix n n O))
          = _root_.Formalism.UG.cT c ((hPu.unit⁻¹ : GL n O) : Matrix n n O) * (_root_.Formalism.UG.cT c P * P) *
            ((hPu.unit⁻¹ : GL n O) : Matrix n n O) := by
            rw [hp, hHdef]; simp only [mul_assoc]
        _ = _root_.Formalism.UG.cT c (P * ((hPu.unit⁻¹ : GL n O) : Matrix n n O)) *
            (P * ((hPu.unit⁻¹ : GL n O) : Matrix n n O)) := by
            rw [hmul]; simp only [mul_assoc]
        _ = 1 := by rw [hPu.mul_val_inv, hone, one_mul]
    show _root_.Formalism.UG.cT σ (k₁ : Matrix n n L) * 1 * k₁ = 1
    rw [mul_one, hk₁def, hbc, _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι, ← Matrix.map_mul, hO,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  refine ⟨k₁, ⟨hk₁, ⟨_, rfl⟩⟩, g⁻¹ * k₁⁻¹ * g',
    mul_mem (mul_mem (inv_mem hg) (inv_mem hk₁)) hg', ?_, by group⟩

  obtain ⟨hGc, hGic⟩ := hinv g hg1
  obtain ⟨hG'c, -⟩ := hinv g' hg'1
  have eM : (g' : Matrix n n L) = (h : Matrix n n O).map ι * g * (k : Matrix n n O).map ι := by
    rw [e, Units.val_mul, Units.val_mul, hbc, hbc]
  have hkk : (k : Matrix n n O).map ι * (↑k⁻¹ : Matrix n n O).map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hhh : (↑h⁻¹ : Matrix n n O).map ι * (h : Matrix n n O).map ι = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]

  have hHg : (h : Matrix n n O).map ι * g = g' * (↑k⁻¹ : Matrix n n O).map ι := by
    rw [eM, mul_assoc _ _ ((↑k⁻¹ : Matrix n n O).map ι), hkk, mul_one]
  have hhm : (h : Matrix n n O).map ι =
      g' * (↑k⁻¹ : Matrix n n O).map ι * ((g⁻¹ : GL n L) : Matrix n n L) := by
    rw [← hHg, mul_assoc, Units.mul_inv, mul_one]
  set Hk := _root_.Formalism.UG.cT c ((k⁻¹ : GL n O) : Matrix n n O) * ((k⁻¹ : GL n O) : Matrix n n O)
    with hHkdef
  have hconj : H.map ι * g = g * Hk.map ι := by
    rw [hHdef, hHkdef, Matrix.map_mul, Matrix.map_mul, ← _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι,
      ← _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι, mul_assoc, hHg, ← mul_assoc]
    conv_lhs => rw [hhm, hmul, hmul, hG'c, hGic]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  clear_value Hk P H
  have hsemi : ∀ q : Polynomial O, (Polynomial.aeval H q).map ι * g =
      g * (Polynomial.aeval Hk q).map ι := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      simp only [Polynomial.aeval_C, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero ι)]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
    | add p q hp hq =>
      rw [map_add, map_add, Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), add_mul,
        mul_add, hp, hq]
    | monomial m a hm =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval H) _ Polynomial.X,
        map_mul (Polynomial.aeval Hk) _ Polynomial.X, Polynomial.aeval_X, Polynomial.aeval_X,
        Matrix.map_mul, Matrix.map_mul, mul_assoc, hconj, ← mul_assoc, hm, mul_assoc]
  refine ⟨Polynomial.aeval Hk p * k, ?_⟩
  rw [Units.val_mul, Units.val_mul, hk₁def, ← map_inv, hbc, mul_inv_rev, inv_inv, Units.val_mul,
    hPu.unit_spec, Matrix.map_mul, eM, Matrix.map_mul]
  have hcancel : ((g⁻¹ : GL n L) : Matrix n n L) * (P.map ι * (↑h⁻¹ : Matrix n n O).map ι) *
      ((h : Matrix n n O).map ι * g * (k : Matrix n n O).map ι) =
      ((g⁻¹ : GL n L) : Matrix n n L) * (P.map ι * g) * (k : Matrix n n O).map ι := by
    simp only [mul_assoc]
    rw [← mul_assoc ((↑h⁻¹ : Matrix n n O).map ι), hhh, one_mul]
  rw [hcancel, hPdef, hsemi p, ← mul_assoc, Units.inv_mul, one_mul]
end _root_.GlobalTheory.UnitaryDoubleCoset
end GlobalTheory.UnitaryDoubleCoset
