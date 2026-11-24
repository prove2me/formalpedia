-- Prove2me | solution 1 for GlobalTheory.ZM.CycBase.snd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:08.537114+00:00
-- url     : https://prove2.me/submissions/ab37ebf4-c8db-4aef-a534-a5302d035f15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrime
import Theorems.Thm_GlobalTheory_ZM_CycBase_zeta_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.CycBase
namespace GlobalTheory.ZM.CycBase
theorem _root_.solution {p k : ℕ} (hk : k ≠ 0) (hkp : k.Coprime p) (hp : p.Prime) {K : Type} [Field K]
    (f : ZP p k →+* DualNumber K) (x : ZP p k) : (f x).snd = 0 := by
  have hinv : ∀ m : ℕ, m.Coprime p → ∀ h : (m : ℂ)⁻¹ ∈ ZP p k,
      (f ⟨_, h⟩).snd = 0 ∧ (m : K) ≠ 0 := by
    intro m hm h
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp.ne_one (by simpa using hm)
    have h1 : (m : ZP p k) * ⟨_, h⟩ = 1 := by
      apply Subtype.ext
      simp [hm0]
    have h2 := congrArg f h1
    rw [map_mul, map_natCast, map_one] at h2
    have h3 := congrArg TrivSqZeroExt.fst h2
    have h4 := congrArg TrivSqZeroExt.snd h2
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.fst_one] at h3
    have hmK : (m : K) ≠ 0 := left_ne_zero_of_mul_eq_one h3
    simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_natCast, TrivSqZeroExt.snd_natCast, zero_mul, add_zero,
      TrivSqZeroExt.snd_one] at h4
    exact ⟨(mul_eq_zero.mp h4).resolve_left hmK, hmK⟩
  have hkK : (k : K) ≠ 0 := (hinv k hkp (Subring.subset_closure (Or.inr ⟨k, hkp, rfl⟩))).2
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨m, hm, rfl⟩
    · have h1 : zetaZP p k ^ k = 1 := Subtype.ext (zeta_prim hk).pow_eq_one
      have h2 := congrArg f h1
      rw [map_pow, map_one] at h2
      have h3 := congrArg TrivSqZeroExt.fst h2
      have h4 := congrArg TrivSqZeroExt.snd h2
      rw [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h3
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one] at h4
      have h5 : (f (zetaZP p k)).fst ≠ 0 := by
        intro h0
        rw [h0, zero_pow hk] at h3
        exact zero_ne_one h3
      change (f (zetaZP p k)).snd = 0
      simpa [hkK, h5] using h4
    · exact (hinv m hm _).1
  | zero => change (f 0).snd = 0; simp
  | one => change (f 1).snd = 0; simp
  | add x y hx hy ihx ihy =>
    change (f (⟨x, hx⟩ + ⟨y, hy⟩)).snd = 0
    simp only [map_add, TrivSqZeroExt.snd_add, ihx, ihy, add_zero]
  | neg x hx ihx =>
    change (f (-⟨x, hx⟩)).snd = 0
    simp only [map_neg, TrivSqZeroExt.snd_neg, ihx, neg_zero]
  | mul x y hx hy ihx ihy =>
    change (f (⟨x, hx⟩ * ⟨y, hy⟩)).snd = 0
    simp only [map_mul, DualNumber.snd_mul, ihx, ihy, mul_zero, zero_mul, add_zero]
end GlobalTheory.ZM.CycBase
