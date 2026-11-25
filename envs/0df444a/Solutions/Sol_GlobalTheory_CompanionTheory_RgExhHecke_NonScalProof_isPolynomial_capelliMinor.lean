-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.isPolynomial_capelliMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:25:34.835165+00:00
-- url     : https://prove2.me/submissions/6c087db2-ee47-4186-8e77-ebaceb51c919

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_const
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_listProd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_isPolynomial_capelliEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
theorem _root_.solution {n p : ℕ} (E : Fin n → Fin n → A) (R S : Fin p → Fin n) (x₀ : ℂ) :
    IsP (fun t : ℂ => cminor E R S (x₀ + t)) := by
  unfold cminor
  refine IsP.sum _ fun σ => ?_
  have h := (IsP.const ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A))).mul
    (IsP.listProd (List.ofFn fun j : Fin p => fun t : ℂ =>
      capEntry E (x₀ - ((j : ℕ) : ℂ) + t) (R (σ j)) (S j)) (fun f hf => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hf
        exact isPolynomial_capelliEntry E _ _ _))
  convert h using 2 with t
  rw [zsmul_eq_mul, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [Function.comp]
  congr 1
  ring
end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
