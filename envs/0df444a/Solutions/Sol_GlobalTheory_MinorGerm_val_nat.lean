-- Prove2me | solution 1 for GlobalTheory.MinorGerm.val_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:44.082169+00:00
-- url     : https://prove2.me/submissions/c0c0c231-b38e-47ce-901e-87bec9bce98c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_mul
import Theorems.Thm_GlobalTheory_MinorGerm_Lead_mul
import Theorems.Thm_GlobalTheory_MinorGerm_val_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
namespace GlobalTheory.MinorGerm
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) {n : ℕ} (hn : n ≠ 0) :
    v (n : C) = (((padicValNat l n : ℕ) : ℝ) : WithTop ℝ) := by
  classical
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  have hfact := Fact.mk hl
  rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, AddValuation.map_mul,
    AddValuation.map_pow, hv, val_coprime v hl hv hm, add_zero, ← WithTop.coe_one, ← WithTop.coe_nsmul,
    nsmul_eq_mul, mul_one]
end GlobalTheory.MinorGerm
