-- Prove2me | solution 1 for JacPoisson.jacobian_implication
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:14:03.572104+00:00
-- url     : https://prove2.me/submissions/799a90ed-59a9-4867-a9af-f9163636dd14

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
public import Theorems.Thm_JacPoisson_isUnit_det_jacobian
public import Theorems.Thm_JacPoisson_jacobianConjectureProp_congr
public import Theorems.Thm_JacPoisson_bijective_of_inverse

set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
open Arxiv.«math.0608009»
namespace JacPoisson
theorem _root_.solution {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n := by
  intro φ hφ
  have hJ := jacobianConjectureProp_congr ((finCongr (two_mul n)).trans finSumFinEquiv.symm) h
  obtain ⟨G, hGF, hFG⟩ := hJ (fun v => φ (X v)) (isUnit_det_jacobian _ hφ)
  exact bijective_of_inverse φ G hGF hFG
end JacPoisson
