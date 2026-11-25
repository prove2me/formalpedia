-- Prove2me | solution 1 for GlobalTheory.HilbFam.JetModular.jet_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:54.45951+00:00
-- url     : https://prove2.me/submissions/b2587b4b-7cba-473c-b0d5-2b871a37071b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSl2IntSmul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HilbFam_gval_linear_change
import Theorems.Thm_GlobalTheory_HilbFam_iterD_const_mul_reindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HilbFam.JetModular
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma iterD_const_mul {I : Type} [Fintype I] [DecidableEq I] (u : List I)
    (h : (I → ℂ) → ℂ) (A : ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z ↦ A * h z) z =
      A * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u h z := by
  simpa using _root_.GlobalTheory.HilbFam.iterD_const_mul_reindex I I (Equiv.refl I) u h A z
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma mem_iff_sl2_equiv_mem_mulMat (F : Type) [Field F] [NumberField F] (L : _root_.GlobalTheory.HilbFam.Lat F)
    (γ : SL(2, ℤ)) (x : Fin 2 → F) :
    x ∈ L ↔ _root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x ∈ _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rw [Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [(_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ).injective (a₁ := y) (a₂ := x) hxy] at hy
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma embeddingCoord_sl2_smul_lemma_3 (F : Type) [Field F] [NumberField F] (γ : SL(2, ℤ)) (τ : ℍ)
    (c t : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Fin 2 → F) (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord (fun i ↦ ((γ • τ : ℍ) : ℂ) + z i * (c * ((γ • τ : ℍ) : ℂ) + t)) (fun i ↦ 1 + z i * c) x i =
      (fun _ ↦ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1))⁻¹) i *
      _root_.GlobalTheory.HilbFam.coord
        (fun i ↦ (τ : ℂ) + z i * ((c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) * τ + t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2))
        (fun i ↦ 1 + z i * (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)))
        (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ x) i := by
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  simp only [_root_.GlobalTheory.HilbFam.coord, _root_.GlobalTheory.HilbFam.JetModular.rowEquiv, LinearEquiv.ofLinear_apply,
    Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, map_add,
    map_mul, map_intCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
    specialLinearGroup_apply, coe_mk, eq_intCast]
  set j := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj_def
  have hji : j * j⁻¹ = 1 := mul_inv_cancel₀ hj
  rw [div_eq_mul_inv]
  linear_combination (-(((i (x 0) : ℝ) : ℂ) * z i * t + ((i (x 1) : ℝ) : ℂ) * (1 + z i * c))) * hji -
    ((i (x 0) : ℝ) : ℂ) * z i * t * j * j⁻¹ * hdet
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
set_option autoImplicit false in
private lemma card_realEmbeddings_eq_finrank (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun φ : F →+* ℝ ↦ Complex.ofRealHom.comp φ) ⟨?_, ?_⟩
  · intro φ ψ h
    ext x
    simpa using congrArg (fun f : F →+* ℂ ↦ f x) h
  · intro ψ
    have hψ : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    exact ⟨hψ.embedding, by ext x; simp [hψ.coe_embedding_apply]⟩
end GlobalTheory.HilbFam.JetModular
end
end

set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.JetModular
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
set_option autoImplicit false
namespace GlobalTheory.HilbFam.JetModular
namespace _root_.GlobalTheory.HilbFam.JetModular
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (τ : ℍ) (c t : ℂ), Even k → _root_.GlobalTheory.HilbFam.jet k L κ ((γ • τ : ℍ) : ℂ) c t = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ (k * Module.finrank ℚ F) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ τ (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) (t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2) := by
  intro F _ _ _ k L κ γ τ c t hk
  have hj : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ≠ 0 := by
    have h := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    rw [denom] at h
    simpa using h
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← iterD_const_mul]
  congr 1
  funext z
  rw [_root_.GlobalTheory.HilbFam.gval_linear_change F k L (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ))
    (_root_.GlobalTheory.HilbFam.JetModular.rowEquiv F γ) _ _ _ _ (fun _ ↦ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)⁻¹) hk
    (mem_iff_sl2_equiv_mem_mulMat F L γ) (fun _ ↦ inv_ne_zero hj)
    (fun x i ↦ embeddingCoord_sl2_smul_lemma_3 F γ τ c t z x i)]
  rw [Finset.prod_const, Finset.card_univ, card_realEmbeddings_eq_finrank]
  simp only [inv_pow, inv_inv, ← pow_mul, mul_comm (Module.finrank ℚ F) k]
  ring
end _root_.GlobalTheory.HilbFam.JetModular
end GlobalTheory.HilbFam.JetModular
