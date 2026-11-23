-- Prove2me | solution 1 for GlobalTheory.TorusCoord.coordMap_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.007811+00:00
-- url     : https://prove2.me/submissions/a69c474d-593b-49ce-8912-c20e28c65f75

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
namespace GlobalTheory.TorusCoord
theorem _root_.solution (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (a : Fin (dimOf X (ComplexEmbedding.conjugate τ.1))) :
    coordMap X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ =
      - conj (pr X e y τ ⟨X.p0 + a.1, lt_neg X ((X.cmType _).mp τ.2) a⟩) := by
  show coord X e y ⟨ComplexEmbedding.conjugate τ.1, a⟩ = _
  unfold coord
  rw [dif_neg ((X.cmType _).mp τ.2)]
  have : (⟨ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1),
      conj_mem X ((X.cmType _).mp τ.2)⟩ : X.Ψ) = τ := Subtype.ext (conj_conj_X _)
  simp only [this]
end GlobalTheory.TorusCoord
