-- Prove2me | solution 1 for GlobalTheory.QFam.eis_hasQ_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:30.728422+00:00
-- url     : https://prove2.me/submissions/e202bfe5-532d-4fac-b2b7-4a312e9e5a6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegrality
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_hasSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_hasSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_dC_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_DD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_eisensteinFourInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_eisensteinSixInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
namespace GlobalTheory.QFam
private theorem eis_spread (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ) (a : ℕ → ℂ) (h : HasQ 1 f a) :
    HasQ N f (spread N a) := by
  unfold HasQ at h ⊢
  intro τ
  have hg : Function.Injective (fun n : ℕ => N * n) := fun x y hxy => Nat.eq_of_mul_eq_mul_left hN hxy
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hg.hasSum_iff]
  · convert h τ using 1
    funext n
    simp only [Function.comp_apply, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hN]
    congr 2
    push_cast
    field_simp
  · intro m hm
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩
private theorem eis_one {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (p : PowerSeries ℤ)
    (hp : p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 f) :
    HasQ 1 f fun n => ((PowerSeries.coeff n p : ℤ) : ℂ) := by
  unfold HasQ
  intro τ
  have hs := hf.hasSum τ
  rw [← hp] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_map, eq_intCast, ReciprocityTheory.ChartRestriction.L1.qm, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring
end GlobalTheory.QFam
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) :
    ∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ) := by
  obtain ⟨k, hk, p, hp⟩ : ∃ k : ℤ, IsMF k F ∧ ∃ p : PowerSeries ℤ,
      p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 F := by
    rcases hF with rfl | rfl | rfl
    · exact ⟨4, ⟨E₄, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt⟩
    · exact ⟨6, ⟨E₆, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinSixInt⟩
    · exact ⟨12, ReciprocityTheory.ChartRestriction.L1.isMF_DD, _, ReciprocityTheory.ChartRestriction.L1.dC_eq⟩
  refine ⟨fun n => if N ∣ n then PowerSeries.coeff (n / N) p else 0, ?_⟩
  convert eis_spread N hN F _ (eis_one hk p hp) using 1
  funext n
  simp only [spread]
  split_ifs <;> simp
end GlobalTheory.QFam
