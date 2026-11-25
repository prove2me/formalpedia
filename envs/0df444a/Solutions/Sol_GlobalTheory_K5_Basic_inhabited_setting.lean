-- Prove2me | solution 1 for GlobalTheory.K5.Basic.inhabited_setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:52.945624+00:00
-- url     : https://prove2.me/submissions/d08cadb6-03c5-4697-b7ce-ab78ee23160a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_isClo_algebraicClosure
import Theorems.Thm_GlobalTheory_K5_Basic_nonempty_tower
import Theorems.Thm_GlobalTheory_K5_Basic_exists_isEmb
import Theorems.Thm_GlobalTheory_K5_Basic_exists_isKum_qq
import Theorems.Thm_GlobalTheory_K5_Basic_exists_isCyc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
namespace GlobalTheory.K5.Basic
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (O0 p) Ω), IsClo p Ω ∧ ∃ T : Tower p Ω,
      ∀ n, (∃ ι, IsEmb T n ι) ∧
        (∃ χ : Gal p Ω → ZMod (p ^ n), ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val) ∧
        ∃ a, IsKum T n ⊤ (T.qq n) a :=
  ⟨_, inferInstance, inferInstance, isClo_algebraicClosure p,
    (nonempty_tower (isClo_algebraicClosure p)).some,
    fun n => ⟨exists_isEmb _ n, exists_isCyc _ n, exists_isKum_qq _ n⟩⟩
end GlobalTheory.K5.Basic
