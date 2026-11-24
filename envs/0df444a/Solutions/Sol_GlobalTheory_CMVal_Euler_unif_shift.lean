-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.unif_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:02.750064+00:00
-- url     : https://prove2.me/submissions/1bf9a56d-7ffb-480a-8a87-5167155dfae5

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_shift_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_forall_locIn_shift
import Theorems.Thm_GlobalTheory_CMVal_Euler_forall_locIn_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_zero_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_over_under
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_coord_ne
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_unifAt_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
open Classical
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)}
    (hm : m (w.under (OF E)) = 0) (hw : w ∉ T) (y : (Af E)ˣ) :
    (unifAt w)⁻¹ * y ∈ MS m T ↔ y ∈ MS m T ∧ y ∉ MS m (insert w T) := by
  obtain ⟨h1, h2⟩ := unifAt_spec w
  have hT : (∀ w' ∈ T, Valued.v ((((unifAt w)⁻¹ * y : (Af E)ˣ) : Af E) w') = 1) ↔ ∀ w' ∈ T, Valued.v ((y : Af E) w') = 1 :=
    forall₂_congr fun w' hw' => by rw [shift_coord y (h1 w' fun h => hw (h ▸ hw'))]
  have hw1 : Valued.v ((((unifAt w)⁻¹ * y : (Af E)ˣ) : Af E) w) ≤ 1 ↔
      Valued.v ((y : Af E) w) ≤ 1 ∧ Valued.v ((y : Af E) w) ≠ 1 := by
    rw [Units.val_mul, mul_coord, inv_coord, map_mul, map_inv₀, h2,
      ← WithZero.exp_log (IdeleModule.coord_ne y w), ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, Ne,
      WithZero.exp_le_exp, WithZero.exp_le_exp, WithZero.exp_inj]
    omega
  have hL : LocIn 0 (w.under (OF E)) (((unifAt w)⁻¹ * y : (Af E)ˣ) : Af E) ↔
      LocIn 0 (w.under (OF E)) (y : Af E) ∧ Valued.v ((y : Af E) w) ≠ 1 := by
    rw [locIn_zero_iff, locIn_zero_iff]
    constructor
    · intro h
      refine ⟨fun P hP => ?_, (hw1.1 (h w (over_under w))).2⟩
      by_cases hPw : P = w
      · subst hPw; exact (hw1.1 (h P hP)).1
      · rw [← shift_coord y (h1 P hPw)]; exact h P hP
    · rintro ⟨h, h'⟩ P hP
      by_cases hPw : P = w
      · subst hPw; exact hw1.2 ⟨h P hP, h'⟩
      · rw [shift_coord y (h1 P hPw)]; exact h P hP
  simp only [MS, Set.mem_setOf_eq, Finset.forall_mem_insert]
  rw [hT, forall_locIn_shift (m := m) (v := w.under (OF E)) (fun _ _ => rfl)
    (fun w' hw' => h1 w' fun h => hw' (h ▸ over_under w)), forall_locIn_iff m (w.under (OF E)), hm, hL]
  tauto
end GlobalTheory.CMVal.Euler
