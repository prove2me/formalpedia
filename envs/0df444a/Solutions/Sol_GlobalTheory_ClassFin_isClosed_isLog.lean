-- Prove2me | solution 1 for GlobalTheory.ClassFin.isClosed_isLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:15.854606+00:00
-- url     : https://prove2.me/submissions/b30bd288-a17b-4087-b458-0a75431fd5ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  intro ι _ _
  let K : Set (Matrix ι ι ℂ) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : K × (Matrix ι ι ℂ × Matrix ι ι ℂ) → ι → ℝ :=
    fun q i => (((q.1 : Matrix ι ι ℂ)ᴴ * q.2.1 * (q.1 : Matrix ι ι ℂ)) i i).re
  have hU : Continuous (fun q : K × (Matrix ι ι ℂ × Matrix ι ι ℂ) => (q.1 : Matrix ι ι ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hD : ∀ i, Continuous (fun q => D q i) := by
    intro i
    refine Complex.continuous_re.comp ?_
    exact ((hU.matrix_conjTranspose.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      hU).matrix_elem i i
  let S : Set (K × (Matrix ι ι ℂ × Matrix ι ι ℂ)) :=
    {q | (q.1 : Matrix ι ι ℂ) * (q.1 : Matrix ι ι ℂ)ᴴ = 1 ∧
      q.2.1 = (q.1 : Matrix ι ι ℂ) * diagonal (fun i => (D q i : ℂ)) * (q.1 : Matrix ι ι ℂ)ᴴ ∧
      q.2.2 = (q.1 : Matrix ι ι ℂ) * diagonal (fun i => (Real.exp (D q i) : ℂ)) *
        (q.1 : Matrix ι ι ℂ)ᴴ}
  have hS : IsClosed S := by
    refine IsClosed.inter (isClosed_eq (hU.matrix_mul hU.matrix_conjTranspose) continuous_const)
      (IsClosed.inter (isClosed_eq (continuous_fst.comp continuous_snd) ?_)
        (isClosed_eq (continuous_snd.comp continuous_snd) ?_))
    · refine (hU.matrix_mul (Continuous.matrix_diagonal ?_)).matrix_mul hU.matrix_conjTranspose
      exact continuous_pi fun i => Complex.continuous_ofReal.comp (hD i)
    · refine (hU.matrix_mul (Continuous.matrix_diagonal ?_)).matrix_mul hU.matrix_conjTranspose
      exact continuous_pi fun i =>
        Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hD i))
  have key : {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} = Prod.snd '' S := by
    ext p
    constructor
    · rintro ⟨U, d, h1, h2, h3⟩
      have hUK : U ∈ K := by
        intro i _ j _
        have hu : U ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff.mpr h1
        simpa using entry_norm_bound_of_unitary hu i j
      have h1' : Uᴴ * U = 1 := mul_eq_one_comm.mp h1
      have hd : D (⟨U, hUK⟩, p) = d := by
        funext i
        show ((Uᴴ * p.1 * U) i i).re = d i
        have : Uᴴ * p.1 * U = diagonal (fun i => (d i : ℂ)) := by
          rw [h2]
          calc Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) * U
              = (Uᴴ * U) * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [h1']; simp
        rw [this]; simp
      refine ⟨(⟨U, hUK⟩, p), ⟨h1, ?_, ?_⟩, rfl⟩
      · rw [hd]; exact h2
      · rw [hd]; exact h3
    · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨q.1, D q, h1, h2, h3⟩
  rw [key]
  exact isClosedMap_snd_of_compactSpace S hS
end GlobalTheory.ClassFin
