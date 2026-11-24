-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.unip_of_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:15.146057+00:00
-- url     : https://prove2.me/submissions/4868afde-f7c4-483a-83c8-07373c872ff4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_leviHom_dGL

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
theorem _root_.solution (b : ι → Fin s) (p : parab K b) : (dGL b (leviHom b p))⁻¹ * p.1 ∈ unip K b := by
  have hd := dGL_mem b (leviHom b p)
  have := (mem_unip_iff b ((⟨dGL b (leviHom b p), hd⟩ : parab K b)⁻¹ * p)).2
    (by rw [map_mul, map_inv, leviHom_dGL, inv_mul_cancel])
  exact this
end GlobalTheory.CompanionTheory.TyFinJacquet
