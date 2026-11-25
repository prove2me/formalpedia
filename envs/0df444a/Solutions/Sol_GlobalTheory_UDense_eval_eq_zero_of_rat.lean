-- Prove2me | solution 1 for GlobalTheory.UDense.eval_eq_zero_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:39.993352+00:00
-- url     : https://prove2.me/submissions/b8e34b95-4427-4661-b6ad-5376a743bc58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints
import Theorems.Thm_P2M_GlobalTheory_UDense_eval_bind__scale_519962e1393f
import Theorems.Thm_GlobalTheory_UDense_vanish_generic
import Theorems.Thm_GlobalTheory_T_exists_normOne_cmField_det_one_add_ne_zero


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
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) →
    ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  intro L _ _ _ n F hF X hX
  obtain ⟨a, ha, hdet⟩ := GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero L n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := complexConj_invol L
  have ha' : c a * a = 1 := by rw [mul_comm]; exact ha
  have hca0 : c a ≠ 0 := left_ne_zero_of_mul_eq_one ha'
  have hemb : ∀ (σ : L →+* ℂ) x, ComplexEmbedding.conjugate σ x = σ (c x) := fun σ x =>
    (IsCMField.complexEmbedding_complexConj L σ x).symm
  let F' := MvPolynomial.bind₁ (fun p : (L →+* ℂ) × Fin n × Fin n => MvPolynomial.C (p.1 (c a)) * MvPolynomial.X p) F
  have hF'ev : ∀ z, MvPolynomial.eval z F' = MvPolynomial.eval (fun p => p.1 (c a) * z p) F :=
    fun z => eval_bind₁_scale _ z F
  have hF' : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F' = 0 := by
    intro γ₀ hγ
    let s : GL (Fin n) L := Units.map (algebraMap L (Matrix (Fin n) (Fin n) L) : L →* Matrix (Fin n) (Fin n) L)
      (Units.mk0 (c a) hca0)
    have hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.scalar (Fin n) (c a) := rfl
    have hmem : s * γ₀ ∈ GQ0 L n := by
      refine (GQ0 L n).mul_mem ?_ hγ
      show (s : Matrix (Fin n) (Fin n) L) * conjT c s = 1
      rw [hs, conjT]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, hcc, ha']
      · simp [Matrix.scalar_apply, Matrix.one_apply, hij]
    have := hF _ hmem
    rw [hF'ev, ← this]
    refine congrArg (fun z => MvPolynomial.eval z F) ?_
    funext p
    simp [upt, ratPt, hs, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  let X' : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ => σ a • X σ
  have hX' : IsUPt X' := by
    intro σ
    simp only [X', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX σ, hemb, ← map_mul, ha, ha',
      map_one, one_smul]
  have h := vanish_generic L n F' hF' X' hX' hdet
  rw [hF'ev] at h
  rw [← h]
  refine congrArg (fun z => MvPolynomial.eval z F) ?_
  funext p
  simp only [upt, X', Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, ha', map_one, one_mul]
end GlobalTheory.UDense
