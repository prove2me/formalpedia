-- Prove2me | solution 1 for JacPoisson.jacobianConjectureProp_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:51:03.648231+00:00
-- url     : https://prove2.me/submissions/1a060c5e-f8f1-4254-964b-c9bb0917ba39

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main

set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {k : Type*} [CommRing k] {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [DecidableEq τ]
namespace JacPoisson
theorem _root_.solution (e : σ ≃ τ) (h : JacobianConjectureProp k σ) :
    JacobianConjectureProp k τ := by
  intro F hF
  -- `F` in the variables `σ`.
  set F' : RegularFunction k σ σ := fun s => rename e.symm (F (e s)) with hF'
  have hJ : F'.Jacobian =
      (reindex e.symm e.symm F.Jacobian).map (rename e.symm : MvPolynomial τ k →ₐ[k] _) := by
    ext a b
    have := pderiv_rename (R := k) e.symm.injective (e a) (F (e b))
    simp only [Equiv.symm_apply_apply] at this
    simp [RegularFunction.Jacobian, hF', this]
  have hF'det : IsUnit F'.Jacobian.det := by
    rw [hJ, ← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_reindex_self]
    exact hF.map _
  obtain ⟨G', hGF, hFG⟩ := h F' hF'det
  refine ⟨fun t => rename e (G' (e.symm t)), ?_, ?_⟩
  · funext t
    have := congrFun hGF (e.symm t)
    simp only [RegularFunction.comp, RegularFunction.id, hF', bind₁_rename,
      Equiv.apply_symm_apply] at this
    simp only [RegularFunction.comp, RegularFunction.id]
    have h2 := congrArg (rename e) this
    rw [rename_bind₁, rename_X, Equiv.apply_symm_apply] at h2
    simpa [Function.comp_def] using h2
  · funext t
    have := congrFun hFG (e.symm t)
    simp only [RegularFunction.comp, RegularFunction.id, hF'] at this
    simp only [RegularFunction.comp, RegularFunction.id, bind₁_rename]
    have h2 := congrArg (rename e) this
    rw [rename_X, Equiv.apply_symm_apply, rename_bind₁] at h2
    simp only [rename_rename, Equiv.self_comp_symm, rename_id_apply] at h2
    simpa [Function.comp_def] using h2
end JacPoisson
