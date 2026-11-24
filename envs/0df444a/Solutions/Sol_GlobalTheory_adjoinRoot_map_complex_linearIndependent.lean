-- Prove2me | solution 1 for GlobalTheory.adjoinRoot_map_complex_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:26.793802+00:00
-- url     : https://prove2.me/submissions/5a964b22-e824-4b89-90f4-767a9237a350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic →
      ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))),
        (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧
        (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧
        ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e →
          LinearIndependent ℂ (fun j => τ (e j)) := by
  intro D P hP
  set f : MvPolynomial (Fin D) ℚ →+* MvPolynomial (Fin D) ℂ := MvPolynomial.map (algebraMap ℚ ℂ)
  set Q := P.map f
  have hQ : Q.Monic := hP.map f
  have h0 : P.eval₂ ((AdjoinRoot.of Q).comp f) (AdjoinRoot.root Q) = 0 := by
    rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root]
  let τ := AdjoinRoot.lift ((AdjoinRoot.of Q).comp f) (AdjoinRoot.root Q) h0
  have hof : ∀ r, τ (AdjoinRoot.of P r) = AdjoinRoot.of Q (f r) := fun r => by
    simp [τ, AdjoinRoot.lift_of]
  have hroot : τ (AdjoinRoot.root P) = AdjoinRoot.root Q := AdjoinRoot.lift_root _
  have hsmul : ∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u := by
    intro q u
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin D) ℚ),
      AdjoinRoot.algebraMap_eq, hof, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin D) ℂ),
      AdjoinRoot.algebraMap_eq]
    simp [f, MvPolynomial.algebraMap_eq]
  refine ⟨τ, fun i => by rw [hof]; simp [f], hsmul, ?_⟩
  intro J e he
  let τL : AdjoinRoot P →ₗ[ℚ] AdjoinRoot Q :=
    { toFun := τ
      map_add' := map_add τ
      map_smul' := fun q u => by
        rw [hsmul]
        exact algebraMap_smul ℂ q (τ u) }
  let bA := (MvPolynomial.basisMonomials (Fin D) ℚ).smulTower (AdjoinRoot.powerBasis' hP).basis
  let bB := (MvPolynomial.basisMonomials (Fin D) ℂ).smulTower (AdjoinRoot.powerBasis' hQ).basis
  have hdim : (AdjoinRoot.powerBasis' hP).dim = (AdjoinRoot.powerBasis' hQ).dim := by
    simp [AdjoinRoot.powerBasis', Q, hP.natDegree_map]
  let σ := Equiv.prodCongr (Equiv.refl (Fin D →₀ ℕ)) (finCongr hdim)
  let E := (Algebra.TensorProduct.basis ℂ bA).equiv bB σ
  have hbas : ∀ k, τ (bA k) = bB (σ k) := by
    rintro ⟨a, i⟩
    simp only [bA, bB, σ, Module.Basis.smulTower_apply, MvPolynomial.coe_basisMonomials,
      PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, Equiv.prodCongr_apply, Equiv.coe_refl,
      Prod.map, id, finCongr_apply, Fin.val_cast]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, hroot, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.algebraMap_eq, hof]
    simp [f, MvPolynomial.map_monomial]
  have hkey : ∀ v, E (1 ⊗ₜ[ℚ] v) = τ v := by
    intro v
    have := bA.ext (f₁ := (E.toLinearMap.restrictScalars ℚ).comp (TensorProduct.mk ℚ ℂ _ 1))
      (f₂ := τL) (fun k => by
        simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
          LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
        rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply]
        exact (hbas k).symm)
    exact congrArg (fun g => g v) this
  have hli : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] e j) :=
    Module.Flat.linearIndependent_one_tmul he
  have := hli.map' E.toLinearMap E.ker
  have h2 : (fun j => τ (e j)) = E.toLinearMap ∘ (fun j => (1 : ℂ) ⊗ₜ[ℚ] e j) := by
    funext j
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    exact (hkey (e j)).symm
  rw [h2]
  exact this
end GlobalTheory
