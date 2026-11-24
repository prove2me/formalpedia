-- Prove2me | solution 1 for GlobalTheory.CotUniv.lie_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:09.015108+00:00
-- url     : https://prove2.me/submissions/99981149-6215-4a24-8ea8-f5e82e6a7e58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
import Theorems.Thm_GlobalTheory_CotUniv_sum_lieBasis
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
variable {O : Type} [CommRing O] {p g : ℕ} {M : Type} [AddCommGroup M] [Module O M]
namespace GlobalTheory.CotUniv
theorem _root_.solution {u u' : LieDualModP p O g →ₗ[O] M}
    (h : ∀ k, u (lieBasis O p g k) = u' (lieBasis O p g k)) : u = u' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← sum_lieBasis, map_sum, map_sum]
  simp only [map_smul, h]
end GlobalTheory.CotUniv
