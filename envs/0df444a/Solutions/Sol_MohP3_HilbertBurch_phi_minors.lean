-- Prove2me | solution 1 for MohP3.HilbertBurch.phi_minors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:46.83103+00:00
-- url     : https://prove2.me/submissions/cc2755d0-90f7-4c40-af33-2da8c50e41dc

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
    maximalMinor (phi x y z) =
      ![6*Gen.f1 x y z,-6*Gen.f2 x y z,6*Gen.f3 x y z,-6*Gen.f4 x y z] := by
  funext i
  fin_cases i <;>
    simp [maximalMinor, phi, Matrix.det_fin_three, Matrix.submatrix,
      Fin.succAbove, Fin.lt_def, Gen.f1,Gen.f2,Gen.f3,Gen.f4] <;> ring
end MohP3.HilbertBurch
