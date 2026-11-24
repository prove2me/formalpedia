-- Prove2me | solution 1 for GlobalTheory.TrivLocus.nontrivial_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:47.051023+00:00
-- url     : https://prove2.me/submissions/2d2a43ec-7fe9-4dbb-98e4-725b4a1e52df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
import Theorems.Thm_GlobalTheory_TrivLocus_exists_ker_iff_minors

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
theorem _root_.solution {R K : Type} [CommRing R] [Field K] (g : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) :
    Nontrivial {v : Fin a → K // (D.map g).mulVec v = 0} ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det ∈ RingHom.ker g := by
  have h := exists_ker_iff_minors (D.map g)
  have h' : ∀ σ : Fin a → Fin b, ((D.map g).submatrix σ id).det = g (D.submatrix σ id).det := fun σ => by
    rw [RingHom.map_det]; rfl
  simp only [h'] at h
  simp only [RingHom.mem_ker]
  rw [← h, nontrivial_iff_exists_ne ⟨0, Matrix.mulVec_zero _⟩]
  exact ⟨fun ⟨v, hv⟩ => ⟨v.1, fun e => hv (Subtype.ext e), v.2⟩,
    fun ⟨v, hv, e⟩ => ⟨⟨v, e⟩, fun e' => hv (congrArg Subtype.val e')⟩⟩
end GlobalTheory.TrivLocus
