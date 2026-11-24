-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:40.228485+00:00
-- url     : https://prove2.me/submissions/89ec18aa-311e-45f2-af3e-72489dd0f3c9

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualReal_exists_selfDual
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
namespace GlobalTheory.CompanionTheory.SelfDualInf
namespace HasCoord
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] (h : HasCoord V) (β : V → V → ℝ)
    (ha : ∀ x y y', β x (y + y') = β x y + β x y') (hc : ∀ x, Continuous (β x))
    (hs : ∀ x y, β x y = β y x) (hn : ∀ x, (∀ y, β x y = 0) → x = 0) (χ : V → V → ℂ)
    (hχ : ∀ x y, χ x y = Complex.exp ((β x y : ℂ) * Complex.I)) :
    ∃ μ : Measure V, SelfDual μ χ := by
  obtain ⟨N, e, g1, g2⟩ := h
  let l : V → (Fin N → ℝ) →L[ℝ] ℝ := fun x =>
    ((AddMonoidHom.mk' (β x) (ha x)).comp e.symm.toAddMonoidHom).toRealLinearMap ((hc x).comp g2)
  have hl : ∀ x u, l x u = β x (e.symm u) := fun x u => rfl
  have hexp : ∀ x y, β x y = ∑ j, e y j * β x (e.symm (Pi.single j 1)) := by
    intro x y
    have h1 : e y = ∑ j, e y j • (Pi.single j 1 : Fin N → ℝ) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : β x y = l x (e y) := by rw [hl, e.symm_apply_apply]
    rw [h2]
    conv_lhs => rw [h1]
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j =>
    β (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1))
  have hA : ∀ x y, β x y = dotProduct (e x) (A.mulVec (e y)) := by
    intro x y
    rw [hs, hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hs, hexp]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine GlobalTheory.CompanionTheory.SelfDualReal.exists_selfDual V N e A χ g1 g2 ?_ ?_ fun x y => by rw [hχ, hA]
  · ext i j; exact hs _ _
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have : e.symm v = 0 := hn _ fun y => by
      rw [hs, hA, e.apply_symm_apply, hv, dotProduct_zero]
    simpa using congrArg e this
end HasCoord
end GlobalTheory.CompanionTheory.SelfDualInf
