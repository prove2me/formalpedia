-- Prove2me | solution 1 for GlobalTheory.TrivLocus.exists_ker_iff_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:57.717282+00:00
-- url     : https://prove2.me/submissions/3d00a5f7-fb6b-4348-9008-d6a55ce1c620

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus
namespace GlobalTheory.TrivLocus
theorem _root_.solution {K : Type} [Field K] {a b : ℕ} (D : Matrix (Fin b) (Fin a) K) :
    (∃ v : Fin a → K, v ≠ 0 ∧ D.mulVec v = 0) ↔ ∀ σ : Fin a → Fin b, (D.submatrix σ id).det = 0 := by
  classical
  constructor
  · rintro ⟨v, hv, h⟩ σ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    funext i
    exact congrFun h (σ i)
  · intro h
    by_contra hn
    have hinj : Function.Injective D.mulVec := by
      intro v w e
      by_contra hvw
      exact hn ⟨v - w, sub_ne_zero.2 hvw, by rw [Matrix.mulVec_sub, e, sub_self]⟩
    have hcol : LinearIndependent K D.col := Matrix.mulVec_injective_iff.1 hinj
    have hrank : D.rank = a := by
      rw [← Matrix.rank_transpose]
      have := LinearIndependent.rank_matrix (M := D.transpose) hcol
      simpa using this
    obtain ⟨κ, e, -, hspan, hli⟩ := exists_linearIndependent' K D.row
    have : Finite κ := hli.finite
    let _ : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hrank]
    let ε : Fin a ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent K (D.submatrix (e ∘ ε) id).row := hli.comp ε ε.injective
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')
    exact hu.ne_zero (h _)
end GlobalTheory.TrivLocus
