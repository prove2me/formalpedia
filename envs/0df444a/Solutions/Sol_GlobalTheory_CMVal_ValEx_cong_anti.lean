-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.cong_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:55.270259+00:00
-- url     : https://prove2.me/submissions/9ec76fdf-fbeb-4a0e-a96b-36759c61a059

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : cong v n ≤ cong v m := fun _ hx =>
  ⟨hx.1, hx.2.trans (WithZero.exp_le_exp.2 (by omega))⟩
end GlobalTheory.CMVal.ValEx
