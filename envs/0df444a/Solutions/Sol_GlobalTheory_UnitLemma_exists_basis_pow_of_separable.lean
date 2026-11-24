-- Prove2me | solution 1 for GlobalTheory.UnitLemma.exists_basis_pow_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:42.108804+00:00
-- url     : https://prove2.me/submissions/01f104b2-89a1-40fb-8e74-e36653c56fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Theorems.Thm_GlobalTheory_UnitLemma_charpoly_dvd_minpoly_of_separable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
open Matrix MeasureTheory
open Polynomial
namespace GlobalTheory.UnitLemma
namespace _root_.GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K), B.P.Separable →
    ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E
      B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  intro K B hsep
  set g := B.g
  have hmin : minpoly K.E (LinearMap.mulLeft K.E g) = minpoly K.E g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A)
      (fun x y hxy => by simpa using congrArg (fun φ => φ 1) hxy) g
  have hdvd := _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable _ hsep
  rw [hmin] at hdvd
  have hdeg : (minpoly K.E g).natDegree =
      Module.finrank K.E B.A := by
    apply le_antisymm (minpoly.natDegree_le g)
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E g)]
    exact natDegree_le_of_dvd hdvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral g))
  have hli : LinearIndependent K.E
      (fun i : Fin (Module.finrank K.E B.A) => g ^ (i : ℕ)) :=
    (linearIndependent_pow g).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _),
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩
end _root_.GlobalTheory.UnitLemma
end GlobalTheory.UnitLemma
