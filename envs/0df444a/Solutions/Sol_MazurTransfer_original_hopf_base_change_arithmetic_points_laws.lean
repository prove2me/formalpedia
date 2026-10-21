-- Prove2me | solution 1 for MazurTransfer.original_hopf_base_change_arithmetic_points_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:47:44.046509+00:00
-- url     : https://prove2.me/submissions/54195bd3-f9f6-4cf6-ab17-235e85ab7425

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: arithmetic points of the same Hopf algebra under scalar base change, retaining convolution and every coefficient map.
Named downstream consumer: transport of the actual selected nineteen character quotient to the equivalent rational-subring base.
-/
import Definitions.Def_MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
noncomputable section
open scoped TensorProduct
open MazurTransfer.HopfBaseChangeArithmeticPoints
namespace MazurTransfer.OriginalHopfBaseChangeArithmeticPointsBoundary20261020
end MazurTransfer.OriginalHopfBaseChangeArithmeticPointsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: arithmetic points of the SAME Hopf algebra under scalar
base change, preserving convolution and every coefficient map.
Named downstream consumer: transport of the actual selected nineteen
character quotient to the proved equivalent rational-subring base.
-/

noncomputable section
namespace MazurTransfer.OriginalHopfBaseChangeArithmeticPointsProof20261020
open scoped TensorProduct
variable {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing H] [HopfAlgebra R H]
variable [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]





theorem restrictPoint_apply (f : WithConv (S ⊗[R] H →ₐ[S] K)) (h : H) :
    restrictPoint f h = f (1 ⊗ₜ[R] h) := rfl



theorem restrictPoint_mul (f g : WithConv (S ⊗[R] H →ₐ[S] K)) :
    restrictPoint (f * g) = restrictPoint f * restrictPoint g := by
  classical
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  let d := Coalgebra.Repr.arbitrary R h
  have h1 := Coalgebra.Repr.convMul_apply (baseChangeRepr (S := S) h d)
    (.toConv f.ofConv.toLinearMap) (.toConv g.ofConv.toLinearMap)
  have h2 := Coalgebra.Repr.convMul_apply d
    (.toConv (restrictPoint f).ofConv.toLinearMap) (.toConv (restrictPoint g).ofConv.toLinearMap)
  rw [LinearMap.convMul_apply] at h1 h2
  exact h1.trans h2.symm

theorem restrictPoint_natural {K' : Type} [CommRing K'] [Algebra R K']
    [Algebra S K'] [IsScalarTower R S K'] (a : K →ₐ[S] K')
    (f : WithConv (S ⊗[R] H →ₐ[S] K)) :
    restrictPoint (.toConv (a.comp f.ofConv)) =
      WithConv.toConv ((a.restrictScalars R).comp (restrictPoint f).ofConv) := rfl

end MazurTransfer.OriginalHopfBaseChangeArithmeticPointsProof20261020

theorem solution : (∀ {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ (f : WithConv (S ⊗[R] H →ₐ[S] K)) (h : H),
restrictPoint f h = f (1 ⊗ₜ[R] h)) ∧ (∀ {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ (f g : WithConv (S ⊗[R] H →ₐ[S] K)),
restrictPoint (f * g) = restrictPoint f * restrictPoint g) ∧ (∀ {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ {K' : Type} [CommRing K'] [Algebra R K']
    [Algebra S K'] [IsScalarTower R S K'] (a : K →ₐ[S] K')
    (f : WithConv (S ⊗[R] H →ₐ[S] K)),
restrictPoint (.toConv (a.comp f.ofConv)) =
      WithConv.toConv ((a.restrictScalars R).comp (restrictPoint f).ofConv)) := by
  exact ⟨MazurTransfer.OriginalHopfBaseChangeArithmeticPointsProof20261020.restrictPoint_apply, MazurTransfer.OriginalHopfBaseChangeArithmeticPointsProof20261020.restrictPoint_mul, MazurTransfer.OriginalHopfBaseChangeArithmeticPointsProof20261020.restrictPoint_natural⟩
#print axioms solution
