-- Prove2me | solution 1 for GlobalTheory.TateTower.LevelIso.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:22.283986+00:00
-- url     : https://prove2.me/submissions/9c4980b4-3cf7-4b80-bfcf-e5320e79ab6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries
import Theorems.Thm_GlobalTheory_TateTower_map_nsmul_of_add
import Theorems.Thm_GlobalTheory_TateTower_nsmul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TateTower
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}
namespace GlobalTheory.TateTower
namespace LevelIso
theorem _root_.solution
    (he : ∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c →
      e n (x ^ m) (x' ^ m) (c ^ m))
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) {p : Kˣ × (D.La → Q)} (h : LevelIso D act e (N * r) p) :
    LevelIso D act e N (p ^ r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hp : ∀ a, (p ^ r).2 a = p.2 (r • a) := fun a => (map_nsmul_of_add h2 r a).symm
  refine ⟨h1.pow (Nat.mul_pos hN hr) (mul_comm _ _), fun a c => ?_, fun c a => ?_, fun a => ?_, fun x => ?_,
    fun a c => ?_⟩
  · rw [hp, hp, hp, smul_add, h2]
  · rw [hp, hp, smul_comm, h3]
  · rw [hp, h4]
    refine exists_congr fun c => ⟨fun h => nsmul_cancel D hr ?_, fun h => ?_⟩
    · rw [h, mul_comm, mul_smul]
    · rw [h, mul_comm, mul_smul]
  · constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (h5 x).1 (by rw [pow_mul, hx, one_pow])
      rw [← map_nsmul_of_add h2, h4] at hx
      obtain ⟨c, hc⟩ := hx
      rw [mul_smul] at hc
      exact ⟨c, by rw [hp, nsmul_cancel D hN hc]⟩
    · rintro ⟨a, rfl⟩
      rw [hp, ← map_nsmul_of_add h2, h4]
      exact ⟨a, by rw [mul_smul]⟩
  · have := he N r _ _ _ hN hr ((h5 _).2 ⟨a, rfl⟩) ((h5 _).2 ⟨c, rfl⟩) (h6 a c)
    have e1 : (p.1 ^ D.EF a c) ^ r = (p.1 ^ r) ^ D.EF a c := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e1] at this
    exact this
end LevelIso
end GlobalTheory.TateTower
