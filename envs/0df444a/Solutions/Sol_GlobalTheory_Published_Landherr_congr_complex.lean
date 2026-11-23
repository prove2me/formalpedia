-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.congr_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:00.204594+00:00
-- url     : https://prove2.me/submissions/30986fdd-d4a9-4676-8a85-0e62a5625d31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_embedding_cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc)
    (τ : E →+* ℂ) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.map τ, ?_, ?_⟩
  · have : (P.map τ).det = τ P.det := (RingHom.map_det τ P).symm
    rw [this]
    exact (map_ne_zero τ).mpr hP
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext a b
    exact embedding_cc τ _
end GlobalTheory.Published.Landherr
