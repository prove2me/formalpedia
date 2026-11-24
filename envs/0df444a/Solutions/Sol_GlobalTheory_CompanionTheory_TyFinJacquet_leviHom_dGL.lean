-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.leviHom_dGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:37.729967+00:00
-- url     : https://prove2.me/submissions/798a4677-419d-4918-8e15-313ec53f2da7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFinJacquet
theorem _root_.solution (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    leviHom b ⟨dGL b g, dGL_mem b g⟩ = g := by
  funext c
  apply Units.ext
  ext ⟨i, hi⟩ ⟨j, hj⟩
  subst hi
  show ((dGL b g : GL ι K) : Matrix ι ι K) i j = _
  rw [dGL_val, blockHom_apply, dif_pos hj]
end GlobalTheory.CompanionTheory.TyFinJacquet
