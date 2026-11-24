-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HIsom.conj_inv_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:09.751399+00:00
-- url     : https://prove2.me/submissions/f045a37a-0d21-4120-9248-dcb60bf95aae

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_conj_mem_UJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HIsom
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.SW.HIsom
theorem _root_.solution (s : A →+* A) (J : Matrix n n A) (G u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) := by
  have hGi : (G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv G
  have key : cT s ((G⁻¹ : GL n A) : Matrix n n A)
      * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A) = J := by
    calc cT s ((G⁻¹ : GL n A) : Matrix n n A)
          * (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) * ((G⁻¹ : GL n A) : Matrix n n A)
        = cT s ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) * J
            * ((G : Matrix n n A) * ((G⁻¹ : GL n A) : Matrix n n A)) := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = J := by rw [hGi, cT_one, Matrix.one_mul, Matrix.mul_one]
  have := conj_mem_UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A)) G⁻¹ u
    (by rw [key]; exact hu)
  simpa using this
end GlobalTheory.CompanionTheory.SW.HIsom
