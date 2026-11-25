-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.dualLattice_euclidLattice2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:36.500808+00:00
-- url     : https://prove2.me/submissions/b2d16746-a863-456e-8b94-12438f153fb2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mem_euclidLattice2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mem_euclidConjLattice2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_single_left
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
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclidLattice2 I) = euclidConjLattice2 (fun i => traceDualIdeal K (I i)) := by
  ext μ
  rw [mem_dualLattice, mem_euclidConjLattice2, mem_idealLattice2]
  set y := (toEuclid2Conj K).symm μ with hy
  have hμ : μ = toEuclid2Conj K y := by rw [hy, ContinuousLinearEquiv.apply_symm_apply]
  constructor
  · intro h i
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    have hmem : toEuclid2 K (Pi.single i x) ∈ euclidLattice2 I := by
      rw [mem_euclidLattice2, ContinuousLinearEquiv.symm_apply_apply, mem_idealLattice2]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simp [Pi.single_eq_of_ne hj]
    obtain ⟨k, hk⟩ := h _ hmem
    refine ⟨k, ?_⟩
    rw [hμ, real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2_single_left] at hk
    rw [mixedTraceForm_comm]
    exact hk
  · intro h ℓ hℓ
    rw [mem_euclidLattice2, mem_idealLattice2] at hℓ
    have hk : ∀ i, ∃ n : ℤ, mixedTraceForm K (y i) (((toEuclid2 K).symm ℓ) i) = n := fun i =>
      (mem_idealLattice_traceDualIdeal_iff K (I i) (y i)).mp (h i) _ (hℓ i)
    choose n hn using hk
    refine ⟨∑ i, n i, ?_⟩
    have hℓ' : ℓ = toEuclid2 K ((toEuclid2 K).symm ℓ) := by
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [hμ, hℓ', real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mixedTraceForm_comm, hn i]
end GroundTheory.Automorphic.Adele2
