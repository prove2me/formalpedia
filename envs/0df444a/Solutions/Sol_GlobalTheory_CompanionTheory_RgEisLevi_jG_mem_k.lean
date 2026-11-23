-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.jG_mem_k
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:31.049031+00:00
-- url     : https://prove2.me/submissions/28b5f12d-c2f0-4cff-9588-6ac9c955fe8d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (hO : ∀ x ∈ A.O, A.σ x ∈ A.O)
    (hφ : ∀ w x, A.φ w (A.σ x) = (starRingEnd ℂ) (A.φ w x)) (m : GL ι R) (hm : m ∈ A.kGL ι) :
    jG A.σ m ∈ A.kGL (ι ⊕ ι) := by
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · rw [jG_val]
    rcases r with r | r <;> rcases c with c | c
    · exact (hm.1 r c).1
    · exact A.O.zero_mem
    · exact A.O.zero_mem
    · exact hO _ (hm.1 c r).2
  · rw [jG_inv_val]
    rcases r with r | r <;> rcases c with c | c
    · exact (hm.1 r c).2
    · exact A.O.zero_mem
    · exact A.O.zero_mem
    · exact hO _ (hm.1 c r).1
  · set M := (m : Matrix ι ι R).map (A.φ w) with hM
    have hMu := hm.2 w
    have h1 : M * ((m⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w) = 1 := by
      rw [hM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hMu
    have h3 : ((m⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w) = star M := by
      rw [← Matrix.one_mul (((m⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w)), ← h2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have h4 : ((((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ).map (A.φ w)) = M := by
      ext r c
      have := congrFun (congrFun h3 c) r
      simp only [Matrix.map_apply, Matrix.star_apply] at this
      simp only [Matrix.map_apply, Matrix.transpose_apply, hφ, this]
      simp [hM]
    have h5 : ((jG A.σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map (A.φ w) = fromBlocks M 0 0 M := by
      rw [jG_val, Matrix.fromBlocks_map, h4]
      simp [hM]
    rw [h5, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    have h6 : M * Mᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hMu
    simp [h6]
end GlobalTheory.CompanionTheory.RgEisLevi
