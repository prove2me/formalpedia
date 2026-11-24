-- Prove2me | solution 1 for GlobalTheory.SharpWeil.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:46:57.420163+00:00
-- url     : https://prove2.me/submissions/427fdea0-27d5-46ac-947c-a965528613be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CommutatorPairingE8SharpLevelPoints
import Theorems.Thm_GlobalTheory_SharpWeil_eq_sum_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpWeil
namespace GlobalTheory.SharpWeil
theorem _root_.solution {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hb : IsSharpBasis W bas)
    (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v) =
      ∑ i, ∑ j, bas.symm X i * bas.symm Y j * Out.stdSymp g i j := by
  have hω : ∀ a b : Fin h ⊕ Fin h → ℤ, omegaStd a b = omegaLin h a b := fun a b => by simp [omegaLin]
  have hX : ∀ u, X u = ∑ i, bas.symm X i • bas (Pi.single i 1) u := fun u => by
    conv_lhs => rw [eq_sum_basis bas X]
    simp [Finset.sum_apply]
  have hY : ∀ v, Y v = ∑ j, bas.symm Y j • bas (Pi.single j 1) v := fun v => by
    conv_lhs => rw [eq_sum_basis bas Y]
    simp [Finset.sum_apply]
  have hs : ∀ i j, Out.stdSymp g i j = ∑ u, ∑ v, (W + W.transpose) u v *
      omegaLin h (bas (Pi.single i 1) u) (bas (Pi.single j 1) v) := fun i j => by
    rw [← hb i j]; simp only [hω]
  simp only [hs, hω, hX, hY, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun i _ =>
    (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring
end GlobalTheory.SharpWeil
