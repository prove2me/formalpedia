-- Prove2me | solution 1 for GlobalTheory.SW.Parab.isSB_chiH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:24.460971+00:00
-- url     : https://prove2.me/submissions/7d8a71f7-71e2-4d17-97e6-97e127c953c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Theorems.Thm_GlobalTheory_SW_Parab_exists_den
import Theorems.Thm_GlobalTheory_SW_Base_isIntegral_cc
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den
import Theorems.Thm_GlobalTheory_SW_Dict_intM_nsmul
import Theorems.Thm_GlobalTheory_SW_Dict_sum_type
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_den
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_nsmul
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.Parab
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma isIntegral_int_natCast {E : Type} [Field E] (k : ℕ) : IsIntegral ℤ (k : E) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma isIntegral_trace_mul_mul_ccT_of_intM {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    {M P : Matrix (Fin n) (Fin N) E} {β : Matrix (Fin N) (Fin N) E} (hM : _root_.GlobalTheory.SW.IntM M)
    (hβ : _root_.GlobalTheory.SW.IntM β) (hP : _root_.GlobalTheory.SW.IntM P) :
    IsIntegral ℤ (M * β * _root_.GlobalTheory.SW.ccT P).trace := by
  unfold _root_.GlobalTheory.SW.IntM at hM hβ hP
  unfold Matrix.trace _root_.GlobalTheory.SW.ccT
  refine IsIntegral.sum _ fun i _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  exact IsIntegral.sum _ fun j _ =>
    (IsIntegral.sum _ fun k _ => (hM i k).mul (hβ k j)).mul (_root_.GlobalTheory.SW.Base.isIntegral_cc (hP i j))
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma exists_int_sum_embeddings_eq_of_isIntegral {E : Type} [Field E] [NumberField E] (t : E) (ht : IsIntegral ℤ t) :
    ∃ m : ℤ, ∑ σ : E →+* ℂ, σ t = m := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E t) := Algebra.isIntegral_trace ht
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  refine ⟨m, ?_⟩
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := t)
  rw [← hm] at h2
  rw [← (RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp] at h2
  simpa using h2.symm
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma map_trace_mul_mul_ccT_eq_trace_conjTranspose {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (τ : E →+* ℂ) (M P : Matrix (Fin n) (Fin N) E) (β : Matrix (Fin N) (Fin N) E) :
    τ (M * β * _root_.GlobalTheory.SW.ccT P).trace = (M.map τ * β.map τ * (P.map τ)ᴴ).trace := by
  rw [← _root_.GlobalTheory.SW.HAct.map_ccT, ← Matrix.map_mul, ← Matrix.map_mul]
  simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma matrix_map_natCast_smul {E : Type} [Field E] {a b : Type} (τ : E →+* ℂ) (k : ℕ) (M : Matrix a b E) :
    ((k : E) • M).map τ = (k : ℂ) • M.map τ := by
  ext i j
  simp
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ} in
private lemma trace_quadratic_form_shift_expand {n N : ℕ} (X Y : Matrix (Fin n) (Fin N) ℂ) (Bh : Matrix (Fin N) (Fin N) ℂ)
    (hB : Bhᴴ = Bh) (r d : ℕ) :
    ((X + ((2 * r * d : ℕ) : ℂ) • Y) * Bh * (X + ((2 * r * d : ℕ) : ℂ) • Y)ᴴ).trace =
      (X * Bh * Xᴴ).trace + ((2 * (Y * ((d : ℂ) • Bh) * ((r : ℂ) • X)ᴴ).trace +
        2 * ((r : ℂ) ^ 2 * d) * (Y * ((d : ℂ) • Bh) * Yᴴ).trace) +
        star (2 * (Y * ((d : ℂ) • Bh) * ((r : ℂ) • X)ᴴ).trace +
        2 * ((r : ℂ) ^ 2 * d) * (Y * ((d : ℂ) • Bh) * Yᴴ).trace)) := by
  have ha : (X * Bh * Yᴴ).trace = star (Y * Bh * Xᴴ).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hB,
      Matrix.mul_assoc]
  have hb : star (Y * Bh * Yᴴ).trace = (Y * Bh * Yᴴ).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hB,
      Matrix.mul_assoc]
  simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul, star_add, star_mul', star_natCast, star_ofNat,
    star_pow, Nat.cast_mul, Nat.cast_ofNat, ha, hb, star_star]
  ring
end
end GlobalTheory.SW.Parab
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Parab
namespace _root_.GlobalTheory.SW.Parab
theorem _root_.solution (hΨ : _root_.GlobalTheory.SW.IsType Ψ)
    {β : Matrix (Fin N) (Fin N) E} (hβ : _root_.GlobalTheory.SW.ccT β = β) (c : ℂ)
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB fun x => c * _root_.GlobalTheory.SW.chiH Ψ β x * φ x := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨d, hd, hdβ⟩ := _root_.GlobalTheory.SW.Dict.exists_den (fun p : Fin N × Fin N => β p.1 p.2)
  have hdβ' : _root_.GlobalTheory.SW.IntM ((d : E) • β) := by
    unfold _root_.GlobalTheory.SW.IntM
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
    exact hdβ (i, j)
  have hcast : ∀ y : Matrix (Fin n) (Fin N) E,
      ((2 * R * d : ℕ) : E) • y = (R : E) • ((2 * d : ℕ) : E) • y := by
    intro y
    rw [smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨2 * R * d, by positivity, ?_, ?_⟩
  · intro x hx
    have hφx : φ x ≠ 0 := fun h0 => hx (by simp [h0])
    have := _root_.GlobalTheory.SW.Dict.intM_nsmul (2 * d) (h1 x hφx)
    convert this using 1
    rw [hcast, smul_comm, Nat.cast_smul_eq_nsmul E]
  · intro x y hy
    have hy' : _root_.GlobalTheory.SW.IntM (((2 * d : ℕ) : E) • y) := by
      rw [Nat.cast_smul_eq_nsmul E]
      exact _root_.GlobalTheory.SW.Dict.intM_nsmul _ hy
    have hper : φ (x + ((2 * R * d : ℕ) : E) • y) = φ x := by
      rw [hcast]
      exact h2 x _ hy'
    simp only [hper]
    by_cases hφx : φ x = 0
    · simp [hφx]
    congr 2
    have hRx := h1 x hφx
    set t : E := 2 * (y * ((d : E) • β) * _root_.GlobalTheory.SW.ccT ((R : E) • x)).trace +
      2 * ((R : E) ^ 2 * d) * (y * ((d : E) • β) * _root_.GlobalTheory.SW.ccT y).trace with ht
    have htI : IsIntegral ℤ t := by
      refine IsIntegral.add ?_ ?_
      · exact (by simpa using isIntegral_int_natCast (E := E) 2 : IsIntegral ℤ (2 : E)).mul
          (isIntegral_trace_mul_mul_ccT_of_intM hy hdβ' hRx)
      · exact ((by simpa using isIntegral_int_natCast (E := E) 2 : IsIntegral ℤ (2 : E)).mul
          (((isIntegral_int_natCast R).pow 2).mul (isIntegral_int_natCast d))).mul
          (isIntegral_trace_mul_mul_ccT_of_intM hy hdβ' hy)
    obtain ⟨m, hm⟩ := exists_int_sum_embeddings_eq_of_isIntegral t htI
    have hsum : ∑ τ : Ψ, τ.1 ((x + ((2 * R * d : ℕ) : E) • y) * β *
        _root_.GlobalTheory.SW.ccT (x + ((2 * R * d : ℕ) : E) • y)).trace =
        ∑ τ : Ψ, τ.1 (x * β * _root_.GlobalTheory.SW.ccT x).trace + m := by
      rw [← hm, _root_.GlobalTheory.SW.Dict.sum_type hΨ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have hBh : (β.map τ.1)ᴴ = β.map τ.1 := by
        rw [← _root_.GlobalTheory.SW.HAct.map_ccT, hβ]
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, map_trace_mul_mul_ccT_eq_trace_conjTranspose, map_trace_mul_mul_ccT_eq_trace_conjTranspose,
        Matrix.map_add _ (map_add τ.1), matrix_map_natCast_smul, trace_quadratic_form_shift_expand _ _ _ hBh R d, ht]
      simp only [map_add, map_mul, map_pow, map_natCast, map_ofNat, map_trace_mul_mul_ccT_eq_trace_conjTranspose,
        matrix_map_natCast_smul]
      simp only [Complex.star_def, map_add, map_mul, map_pow, map_natCast, map_ofNat]
    unfold _root_.GlobalTheory.SW.chiH
    rw [hsum, mul_add, Complex.exp_add]
    have hm1 : Complex.exp (2 * Real.pi * Complex.I * m) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * m = m * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [hm1, mul_one]
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
