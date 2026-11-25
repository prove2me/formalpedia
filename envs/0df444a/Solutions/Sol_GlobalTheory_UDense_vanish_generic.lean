-- Prove2me | solution 1 for GlobalTheory.UDense.vanish_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:42.397797+00:00
-- url     : https://prove2.me/submissions/2f4cbc7e-f4f2-4eb2-ab1c-320616b071fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints
import Theorems.Thm_GlobalTheory_UDense_map_inv_field_hom
import Theorems.Thm_GlobalTheory_T_cayleyTransform_mem_rational_unitaryGroup
import Theorems.Thm_GlobalTheory_T_mvPolynomial_clear_denominators_eval
import Theorems.Thm_GlobalTheory_T_mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian
import Theorems.Thm_GlobalTheory_T_unitary_family_eq_cayley_of_skew_family


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.UDense
namespace GlobalTheory.UDense
theorem _root_.solution (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hX : IsUPt X) (hd : ∀ σ, (1 + X σ).det ≠ 0) :
    MvPolynomial.eval (upt X) F = 0 := by
  classical
  let V : (L →+* ℂ) → Matrix (Fin n) (Fin n) (MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :=
    fun σ => Matrix.of fun i j => MvPolynomial.X (σ, i, j)
  let P : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => ((1 + V p.1) * (1 - V p.1).adjugate) p.2.1 p.2.2
  let D : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => (1 - V p.1).det
  obtain ⟨G, M, hGM⟩ := GlobalTheory.T.mvPolynomial_clear_denominators_eval F P D
  have evV : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      (V σ).map (MvPolynomial.eval (upt y)) = y σ := by
    intro y σ; ext i j; simp [V, upt]
  have evDet : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      MvPolynomial.eval (upt y) ((1 - V σ).det) = (1 - y σ).det := by
    intro y σ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), evV]
  have evP : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, (1 - y σ).det ≠ 0) →
      (fun p => MvPolynomial.eval (upt y) (P p) / MvPolynomial.eval (upt y) (D p)) =
        upt (fun σ => (1 + y σ) * (1 - y σ)⁻¹) := by
    intro y hy
    funext p
    have hm : ((1 + V p.1) * (1 - V p.1).adjugate).map (MvPolynomial.eval (upt y)) =
        (1 + y p.1) * (1 - y p.1).adjugate := by
      rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _), evV]
    have hP : MvPolynomial.eval (upt y) (P p) = ((1 + y p.1) * (1 - y p.1).adjugate) p.2.1 p.2.2 := by
      rw [← hm]; rfl
    rw [hP, show MvPolynomial.eval (upt y) (D p) = (1 - y p.1).det from evDet y p.1]
    simp only [upt, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [div_eq_inv_mul]
  let Q := G * ∏ σ, (1 - V σ).det
  have hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0 := by
    intro S hS
    have hdS : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det = σ (1 - S).det := by
      intro σ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    simp only [Q, map_mul, map_prod, evDet, hdS]
    by_cases h0 : (1 - S).det = 0
    · have σ0 : L →+* ℂ := Classical.arbitrary _
      rw [Finset.prod_eq_zero (Finset.mem_univ σ0) (by rw [h0, map_zero]), mul_zero]
    · obtain ⟨γ₀, hγ, hγv⟩ := GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup L n S hS h0
      have hne : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det ≠ 0 := fun σ => by
        rw [hdS]; exact (map_ne_zero σ).2 h0
      have hDy : ∀ p, MvPolynomial.eval (upt (ratPt S)) (D p) ≠ 0 := fun p => by
        rw [show MvPolynomial.eval (upt (ratPt S)) (D p) = _ from evDet _ p.1]; exact hne p.1
      obtain ⟨-, hG⟩ := hGM _ hDy
      rw [hG, evP _ hne]
      have hc : (fun σ => (1 + ratPt S σ) * (1 - ratPt S σ)⁻¹) = ratPt (γ₀ : Matrix (Fin n) (Fin n) L) := by
        funext σ
        rw [hγv]
        simp only [ratPt, Matrix.map_mul, map_inv_field_hom, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [hc, hF γ₀ hγ, mul_zero, zero_mul]
  obtain ⟨Y, hYs, hYd, hYX⟩ := GlobalTheory.T.unitary_family_eq_cayley_of_skew_family L n X hX hd
  have hQY := GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian L n Q hQ Y hYs
  have hDY : ∀ p, MvPolynomial.eval (upt Y) (D p) ≠ 0 := fun p => by
    rw [show MvPolynomial.eval (upt Y) (D p) = _ from evDet _ p.1]; exact hYd p.1
  obtain ⟨hM, hG⟩ := hGM _ hDY
  simp only [Q, map_mul, map_prod, evDet] at hQY
  have hprod : ∏ σ, (1 - Y σ).det ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hYd σ
  have hG0 : MvPolynomial.eval (upt Y) G = 0 := (mul_eq_zero.1 hQY).resolve_right hprod
  rw [hG, evP _ hYd, show (fun σ => (1 + Y σ) * (1 - Y σ)⁻¹) = X from funext hYX] at hG0
  exact (mul_eq_zero.1 hG0).resolve_left hM
end GlobalTheory.UDense
