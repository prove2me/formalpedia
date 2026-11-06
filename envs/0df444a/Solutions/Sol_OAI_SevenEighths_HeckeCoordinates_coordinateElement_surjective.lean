-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCoordinates.coordinateElement_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:00.142741+00:00
-- url     : https://prove2.me/submissions/13f154be-afee-4b56-acd8-65a2f78d45e8

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Mathlib.Data.ZMod.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


section
namespace OAI
noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily
private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]
private theorem pb_gen : pb.gen = HeckeFamily.omega := hζ.integralPowerBasis_gen
end SevenEighths.HeckeCoordinates
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeCoordinates
open HeckeFamily
namespace OAI.SevenEighths.HeckeCoordinates
theorem _root_.solution :
    Function.Surjective (fun n : ℤ × ℤ => coordinateElement n.1 n.2) := by
  intro x
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨(a,b), ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  simpa [a, b, i0, i1, pb_gen, coordinateElement, smul_eq_mul, mul_comm] using hsum
end OAI.SevenEighths.HeckeCoordinates
