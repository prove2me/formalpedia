-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.tendsto_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:27.438934+00:00
-- url     : https://prove2.me/submissions/58ab4d1c-bf04-4b9e-b0d5-c64e1a25cc0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_conj_levDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.LevelUnimod
theorem _root_.solution (l : ℕ) (L : Fin c → ℕ) (g : GL (n ⊕ Fin c) k)
    (hg : ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => l) L s ≤ Sum.elim (fun _ => l) L r →
      g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) :
    Filter.Tendsto (fun t : kˣ => ((levDiag (Sum.elim (fun _ => l) L) t)⁻¹ * g *
      levDiag (Sum.elim (fun _ => l) L) t).val) (Filter.comap (Units.val : kˣ → k) (𝓝 0))
      (𝓝 (fromBlocks g.val.toBlocks₁₁ 0 0 1)) := by
  set lev : n ⊕ Fin c → ℕ := Sum.elim (fun _ => l) L with hlev
  refine tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun s => ?_
  simp only [conj_levDiag]
  have hcan : ∀ (t : kˣ) (a : ℕ) (x : k), ((t⁻¹ : kˣ) : k) ^ a * x * (t : k) ^ a = x := fun t a x => by
    rw [mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  by_cases hR : r.isRight ∨ s.isRight
  · have hlim : fromBlocks g.val.toBlocks₁₁ 0 0 1 r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
      rcases r with r | r <;> rcases s with s | s <;> simp_all [one_apply]
    rw [hlim]
    by_cases hle : lev s ≤ lev r
    · rw [hg r s hR hle]
      by_cases e : r = s
      · subst e
        simp only [hcan]
        exact tendsto_const_nhds
      · simp only [one_apply_ne e, mul_zero, zero_mul]
        exact tendsto_const_nhds
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (not_le.1 hle)
      have e : r ≠ s := fun e => hle (e ▸ le_rfl)
      have h2 : ∀ t : kˣ, ((t⁻¹ : kˣ) : k) ^ lev r * g.val r s * (t : k) ^ lev s =
          g.val r s * (t : k) ^ (d + 1) := fun t => by
        rw [hd, add_assoc, pow_add, ← mul_assoc, hcan]
      simp only [h2, one_apply_ne e]
      have h3 : Continuous fun x : k => g.val r s * x ^ (d + 1) := by fun_prop
      have h4 := (h3.tendsto 0).comp (Filter.tendsto_comap (f := (Units.val : kˣ → k)) (x := 𝓝 0))
      simpa [Function.comp_def] using h4
  · rcases r with r | r <;> rcases s with s | s <;> simp only [Sum.isRight_inl, Sum.isRight_inr, or_true,
      true_or, not_true] at hR
    simp only [hlev, Sum.elim_inl, hcan]
    exact tendsto_const_nhds
end GlobalTheory.LevelUnimod
