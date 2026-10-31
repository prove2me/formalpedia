-- Prove2me | solution 1 for OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap_row
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:42:21.189233+00:00
-- url     : https://prove2.me/submissions/f2690627-71f0-4415-b63b-fcda659d94da

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg017

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem coordinateGroupRing_single {A : Type*} (v : A → unitary (Sequences M))
    (g : FreeGroup A) : coordinateGroupRing v (MonoidAlgebra.single g 1)=(FreeGroup.lift v g : Sequences M) := by
  simp [coordinateGroupRing]

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.coordinateLabels_pair
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) {ell : ℕ} (k j : Fin ell) :
    F.coordinateLabels τ ω u ell (pairLabel k j)=
      F.coordinatePrefix τ ω u (k.val+1)*(F.coordinatePrefix τ ω u (j.val+1))⁻¹ := by
  change FreeGroup.lift _ (freePrefix _*(freePrefix _)⁻¹)=_
  rw [(FreeGroup.lift (F.coordinateVariables τ ω u)).map_mul,
    (FreeGroup.lift (F.coordinateVariables τ ω u)).map_inv]
  rfl

theorem SuccessiveCoordinateHaar.perturbationMap_row_oai
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) {ell : ℕ} (α : ℝ) (k : Fin ell) :
    F.perturbationMap τ ω u z ell (finitePerturbationRow α k)=
      (F.coordinatePrefix τ ω u (k.val+1) : Sequences M)*
        F.commonPerturbation τ ω u z ell α*
        star (F.coordinatePrefix τ ω u (k.val+1) : Sequences M) := by
  let Φ := F.perturbationMap τ ω u z ell
  have hs (r : ℝ) (a : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) : Φ (r • a)=r • Φ a :=
    map_smul (Φ.restrictScalars ℝ).toLinearMap r a
  have hgen (p : PrefixLabel ell) : Φ (MonoidAlgebra.single (FreeGroup.of p) 1)=
      (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,FreeGroup.lift_apply_of]
  have hinv (p : PrefixLabel ell) : Φ (MonoidAlgebra.single ((FreeGroup.of p)⁻¹) 1)=
      star (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,map_inv,FreeGroup.lift_apply_of]
    rfl
  change Φ (finitePerturbationRow α k)=_
  rw [finitePerturbationRow,hs,commonPerturbation]
  simp only [map_sum,map_sub,hgen,hinv,mul_smul_comm,smul_mul_assoc,
    Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateConjugates,coordinateLabels_pair]
  simp only [← Unitary.star_eq_inv,Submonoid.coe_mul,Unitary.coe_star]
  simp only [star_mul,star_star,mul_sub,sub_mul,mul_assoc]

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap_row_oai.{u_1} := @OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap_row_oai.{u_1}
