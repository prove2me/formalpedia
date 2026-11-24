-- Prove2me | solution 1 for GlobalTheory.CotUniv.smul_sqKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:11.638986+00:00
-- url     : https://prove2.me/submissions/10189d7a-99e0-4485-8208-f71ce8d272a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_fst
import Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
attribute [local simp] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_snd



set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
variable {O M}
variable (O M)
variable {O M}
namespace GlobalTheory.CotUniv
theorem _root_.solution (r : R₀) (m : M) :
    r • (sqKer m : (sqProj O M).ker) = sqKer (algebraMap R₀ (O : Type) r • m) := by
  refine Subtype.ext ?_
  refine (Algebra.smul_def (A := (sqAlg O M : Type)) r _).trans ?_
  refine SqExt.ext (O := (O : Type)) (M := M) (mul_zero _) ?_
  refine (SqExt.snd_mul _ _).trans ?_
  change algebraMap R₀ (O : Type) r • m + (0 : (O : Type)) • (0 : M) = algebraMap R₀ (O : Type) r • m
  simp
end GlobalTheory.CotUniv
