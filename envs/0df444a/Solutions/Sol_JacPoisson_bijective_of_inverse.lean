-- Prove2me | solution 1 for JacPoisson.bijective_of_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:50:51.187807+00:00
-- url     : https://prove2.me/submissions/eb2b6511-2b23-4c2d-85e9-cb94d2e36f20

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main

set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {k : Type*} [CommRing k] {σ : Type*}
namespace JacPoisson
theorem _root_.solution (φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (G : RegularFunction k σ σ)
    (hGF : G.comp (fun v => φ (X v)) = RegularFunction.id k σ)
    (hFG : RegularFunction.comp (fun v => φ (X v)) G = RegularFunction.id k σ) :
    Function.Bijective φ := by
  generalize hF : (fun v => φ (X v)) = F at hGF hFG
  have hφ : φ = bind₁ F := by
    ext v
    simp [← hF]
  rw [hφ]
  refine Function.bijective_iff_has_inverse.mpr ⟨bind₁ G, fun p => ?_, fun p => ?_⟩
  · have h : (fun i => bind₁ G (F i)) = X := hGF
    rw [bind₁_bind₁, h, bind₁_X_left, AlgHom.id_apply]
  · have h : (fun i => bind₁ F (G i)) = X := hFG
    rw [bind₁_bind₁, h, bind₁_X_left, AlgHom.id_apply]
end JacPoisson
