-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.dualLattice_euclidLatticePi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:58.52268+00:00
-- url     : https://prove2.me/submissions/635f57af-8759-4f00-9446-09d13e589bab

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mem_euclidLatticePi
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mem_euclidConjLatticePi
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_single_left
import Theorems.Thm_GroundTheory_Global_mem_dualLattice
import Theorems.Thm_GroundTheory_Global_mem_idealLattice_traceDualIdeal_iff
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclidLatticePi I) = euclidConjLatticePi (fun i ↦ traceDualIdeal K (I i)) := by
  ext μ
  rw [mem_dualLattice, mem_euclidConjLatticePi, mem_idealLatticePi]
  set y := (toEuclidPiConj K).symm μ with hy
  have hμ : μ = toEuclidPiConj K y := by rw [hy, ContinuousLinearEquiv.apply_symm_apply]
  constructor
  · intro h i
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    have hmem : toEuclidPi K (Pi.single i x) ∈ euclidLatticePi I := by
      rw [mem_euclidLatticePi, ContinuousLinearEquiv.symm_apply_apply, mem_idealLatticePi]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simp [Pi.single_eq_of_ne hj]
    obtain ⟨k, hk⟩ := h _ hmem
    refine ⟨k, ?_⟩
    rw [hμ, real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi_single_left] at hk
    rw [mixedTraceForm_comm]
    exact hk
  · intro h ℓ hℓ
    rw [mem_euclidLatticePi, mem_idealLatticePi] at hℓ
    have hk : ∀ i, ∃ n : ℤ, mixedTraceForm K (y i) (((toEuclidPi K).symm ℓ) i) = n := fun i ↦
      (mem_idealLattice_traceDualIdeal_iff K (I i) (y i)).mp (h i) _ (hℓ i)
    choose n hn using hk
    refine ⟨∑ i, n i, ?_⟩
    have hℓ' : ℓ = toEuclidPi K ((toEuclidPi K).symm ℓ) := by
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [hμ, hℓ', real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mixedTraceForm_comm, hn i]
end GroundTheory.Automorphic.GJMatrix
