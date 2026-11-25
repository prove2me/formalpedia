-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnitaryExp.map_exp_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:44.698667+00:00
-- url     : https://prove2.me/submissions/de1a00b1-a0ab-4d15-a80d-b243a1a2f14b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_GlobalTheory_ExistsExpUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitaryExp
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.CompanionTheory.UnitaryExp
theorem _root_.solution {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f : Matrix m m ℂ ≃ₐ[ℂ] Matrix n n ℂ) (hf : Continuous f) (S : Matrix m m ℂ) :
    f (NormedSpace.exp S) = NormedSpace.exp (f S) := by
  let _ : NormedRing (Matrix m m ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix m m ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp f hf S
end GlobalTheory.CompanionTheory.UnitaryExp
