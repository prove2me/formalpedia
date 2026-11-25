-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:53.01253+00:00
-- url     : https://prove2.me/submissions/361e2033-8ac1-4c0e-9a81-bcf577243841

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_maschkeFacts_of_simpleIffIrr
import Theorems.Thm_GlobalTheory_T_simple_iff_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Maschke
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.MaschkeFacts :=
  maschkeFacts_of_simpleIffIrr GlobalTheory.T.simple_iff_irreducible
end GlobalTheory.CompanionTheory.TyFin.Maschke
