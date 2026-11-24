-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.expAt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:53.844809+00:00
-- url     : https://prove2.me/submissions/165b8179-3d28-484d-a05e-cdef632b9265

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
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h2 : LevelLe χ P 2) (h1 : ¬ LevelLe χ P 1) : ExpAt χ P 2 :=
  fun m => ⟨fun h => by
    by_contra hm
    exact h1 fun y a b => h y a (b.trans (WithZero.exp_le_exp.2 (by omega))),
    fun hm y a b => h2 y a (b.trans (WithZero.exp_le_exp.2 (by omega)))⟩
end GlobalTheory.CMVal.ValEx
