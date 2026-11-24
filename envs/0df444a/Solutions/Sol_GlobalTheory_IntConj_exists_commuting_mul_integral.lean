-- Prove2me | solution 1 for GlobalTheory.IntConj.exists_commuting_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:00:06.840901+00:00
-- url     : https://prove2.me/submissions/7d678f8d-ccf9-4acf-bbd9-378999be9209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
import Theorems.Thm_GlobalTheory_IntConj_mul_krylov_of_semiconj
import Theorems.Thm_GlobalTheory_IntConj_mem_unitBall
import Theorems.Thm_GlobalTheory_IntConj_norm_eq_one_of_isUnit
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_cyclicAlgebra
import Theorems.Thm_GlobalTheory_RegSS_Semilocal_cyclicSemilocal_of_cyclicField
import Theorems.Thm_GlobalTheory_RegSS_Semilocal_krylov_map_ringHom
import Theorems.Thm_GlobalTheory_RegSS_commute_of_mem_genAlg
import Theorems.Thm_GlobalTheory_RegSS_cyclicField
import Theorems.Thm_GlobalTheory_RegSS_isUnit_det_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IntConj
namespace GlobalTheory.IntConj
theorem _root_.solution (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N x : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hsep : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (hx : IsUnit x) (hN' : ∀ i j, ‖(x⁻¹ * N * x) i j‖ ≤ 1) :
    ∃ c : Matrix (Fin n) (Fin n) E, IsUnit c ∧ c * N = N * c ∧ (∀ i j, ‖(c⁻¹ * x) i j‖ ≤ 1) ∧
      ‖(c⁻¹ * x).det‖ = 1 := by
  classical
  let O := (NormedField.valuation (K := E)).valuationSubring
  let φ : O →+* E := O.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have lift : ∀ M : Matrix (Fin n) (Fin n) E, (∀ i j, ‖M i j‖ ≤ 1) →
      ∃ M₀ : Matrix (Fin n) (Fin n) O, M₀.map φ = M := fun M hM =>
    ⟨Matrix.of fun i j => ⟨M i j, (mem_unitBall _).2 (hM i j)⟩, by ext i j; rfl⟩
  have liftP : ∀ p : E[X], (∀ i, ‖p.coeff i‖ ≤ 1) → ∃ p₀ : O[X], p₀.map φ = p := by
    intro p hp
    have : p ∈ Polynomial.lifts φ :=
      (lifts_iff_coeff_lifts p).2 fun k => ⟨⟨_, (mem_unitBall _).2 (hp k)⟩, rfl⟩
    exact (mem_lifts p).1 this
  obtain ⟨u, v, hu, hv, huv⟩ := hsep
  obtain ⟨u₀, rfl⟩ := liftP u hu
  obtain ⟨v₀, rfl⟩ := liftP v hv
  have sep : ∀ M₀ : Matrix (Fin n) (Fin n) O, (M₀.map φ).charpoly = N.charpoly →
      M₀.charpoly.Separable := by
    intro M₀ hM
    refine ⟨u₀, v₀, ?_⟩
    apply Polynomial.map_injective φ hφ
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM, Polynomial.map_one]
    exact huv
  obtain ⟨X, rfl⟩ := hx
  have hXd : IsUnit (X : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 X.isUnit
  have hcp : ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)).charpoly = N.charpoly := by
    exact Matrix.charpoly_units_conj' X N
  obtain ⟨N₀, hN₀⟩ := lift N hN
  obtain ⟨N₀', hN₀'⟩ := lift _ hN'
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀ (sep N₀ (by rw [hN₀]))
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀' (sep N₀' (by rw [hN₀', hcp]))
  have hK : (GlobalTheory.RegSS.krylov N₀ v₁).map φ = GlobalTheory.RegSS.krylov N (φ ∘ v₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀]
  have hK' : (GlobalTheory.RegSS.krylov N₀' w₁).map φ =
      GlobalTheory.RegSS.krylov ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) (φ ∘ w₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀']
  have hKu := GlobalTheory.RegSS.isUnit_det_map φ hv₁
  have hKu' := GlobalTheory.RegSS.isUnit_det_map φ hw₁
  obtain ⟨-, -, hbij⟩ := GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N (φ ∘ v₁) (by rw [← hK]; exact hKu)
  obtain ⟨l, hl⟩ := hbij.2 ((X : Matrix (Fin n) (Fin n) E) *ᵥ (φ ∘ w₁))
  simp only at hl
  have hcN : N * (l : Matrix (Fin n) (Fin n) E) = l * N := GlobalTheory.RegSS.commute_of_mem_genAlg rfl l.2
  have hXN : (X : Matrix (Fin n) (Fin n) E) * ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) = N * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXd, Matrix.one_mul]
  have key : (l : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀ v₁).map φ =
      (X : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀' w₁).map φ := by
    rw [hK, hK', mul_krylov_of_semiconj hcN.symm, mul_krylov_of_semiconj hXN, hl]
  set Kv := (GlobalTheory.RegSS.krylov N₀ v₁).map φ with hKv
  set Kw := (GlobalTheory.RegSS.krylov N₀' w₁).map φ with hKw
  generalize (l : Matrix (Fin n) (Fin n) E) = c at key hcN
  have hcu : IsUnit c := by
    have : c = (X : Matrix (Fin n) (Fin n) E) * Kw * Kv⁻¹ := by
      rw [← key, Matrix.mul_nonsing_inv_cancel_right _ _ hKu]
    rw [this]
    exact (X.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hKu')).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hKu))
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det _).1 hcu
  have e2 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = Kv * Kw⁻¹ := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (c⁻¹ * (X : Matrix (Fin n) (Fin n) E)) hKu',
      Matrix.mul_assoc c⁻¹, ← key, Matrix.nonsing_inv_mul_cancel_left _ _ hcd]
  have hinv : Kw⁻¹ = ((GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hKw, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ hw₁, map_one]
  have e3 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) =
      (GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    rw [e2, hinv, hKv, Matrix.map_mul]
  refine ⟨c, hcu, hcN.symm, fun i j => ?_, ?_⟩
  · rw [e3]; exact (mem_unitBall _).1 ((GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹) i j).2
  · rw [e3, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact norm_eq_one_of_isUnit (by
      rw [Matrix.det_mul]; exact hv₁.mul (Matrix.isUnit_nonsing_inv_det _ hw₁))
end GlobalTheory.IntConj
