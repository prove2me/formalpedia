-- Prove2me | solution 1 for GlobalTheory.TorusCoord.sum_emb_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:02.374482+00:00
-- url     : https://prove2.me/submissions/c220072b-cbdf-43c4-a15c-d90f39511774

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_conj_conj_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.TorusCoord
namespace _root_.GlobalTheory.TorusCoord
theorem _root_.solution {M : Type} [AddCommMonoid M] (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (F : (E →+* ℂ) → M) :
    ∑ σ, F σ = ∑ τ : X.Ψ, (F τ.1 + F (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort X.Ψ F,
    Finset.sum_coe_sort X.Ψ (fun τ => F (ComplexEmbedding.conjugate τ)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ X.Ψ)]
  congr 1
  · congr 1
    ext σ
    simp
  · refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact (X.cmType _).mpr (by rwa [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X])
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (X.cmType τ).mp hτ
    · intro σ _
      exact _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X σ
    · intro τ _
      exact _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X τ
    · intro σ _
      rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X]
end _root_.GlobalTheory.TorusCoord
end GlobalTheory.TorusCoord
