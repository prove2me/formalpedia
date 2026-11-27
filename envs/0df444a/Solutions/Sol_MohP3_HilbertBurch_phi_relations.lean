-- Prove2me | solution 1 for MohP3.HilbertBurch.phi_relations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:36:41.458777+00:00
-- url     : https://prove2.me/submissions/d2a2deb1-9c66-499c-b953-99605e77bc13

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
namespace MohP3.HilbertBurch
theorem _root_.solution {A : Type*} [CommRing A] (x y z : A) :
    ![Gen.f1 x y z,Gen.f2 x y z,Gen.f3 x y z,Gen.f4 x y z] ᵥ* phi x y z = 0 := by
  funext j
  fin_cases j <;>
    simp [phi,Matrix.vecMul,dotProduct,Fin.sum_univ_succ,Gen.f1,Gen.f2,Gen.f3,Gen.f4] <;> ring
end MohP3.HilbertBurch
