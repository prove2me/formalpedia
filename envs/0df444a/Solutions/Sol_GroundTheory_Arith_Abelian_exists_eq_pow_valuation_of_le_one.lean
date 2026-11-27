-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.exists_eq_pow_valuation_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:44.058734+00:00
-- url     : https://prove2.me/submissions/fcbc9347-16ad-408b-a434-6e303dc38377

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_exists_eq_pow_of_le_one_iff
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_coordinateRing_le_one
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable {W} [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (hnt : ∃ f, f ≠ 0 ∧ w f ≠ 1) :
    ∃ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      (∀ a, a ∈ v.asIdeal ↔ w (algebraMap _ W.toAffine.FunctionField a) < 1) ∧
      ∃ e : ℕ, 0 < e ∧ ∀ f, w f = v.valuation W.toAffine.FunctionField f ^ e := by
  have hA := valuation_coordinateRing_le_one w hF hx
  let P : Ideal W.toAffine.CoordinateRing :=
    { carrier := {a | w (algebraMap _ W.toAffine.FunctionField a) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at ha ⊢
        calc _ ≤ 1 * w (algebraMap _ W.toAffine.FunctionField a) := mul_le_mul_left (hA c) _
          _ < 1 := by rwa [one_mul] }
  have hmem : ∀ a, a ∈ P ↔ w (algebraMap _ W.toAffine.FunctionField a) < 1 := fun a => Iff.rfl
  have hone : ∀ a, a ∉ P → w (algebraMap _ W.toAffine.FunctionField a) = 1 :=
    fun a ha => le_antisymm (hA a) (not_lt.mp ha)
  have hPprime : P.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : W.toAffine.CoordinateRing) ∈ P := htop ▸ Submodule.mem_top
      rw [hmem, map_one, map_one] at h1
      exact lt_irrefl _ h1
    · by_contra hn
      push Not at hn
      rw [hmem, map_mul, Valuation.map_mul, hone a hn.1, hone b hn.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hP0 : P ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hwf⟩ := hnt
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
    apply hwf
    dsimp only at hf ⊢
    have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have ha : a ≠ 0 := by rintro rfl; exact hf (IsLocalization.mk'_zero _)
    have hnot : ∀ b : W.toAffine.CoordinateRing, b ≠ 0 → b ∉ P := fun b hb hbP =>
      hb ((Submodule.mem_bot _).mp (hbot ▸ hbP))
    have h1 := congrArg w (IsLocalization.mk'_spec W.toAffine.FunctionField a s)
    rw [Valuation.map_mul, hone _ (hnot _ hs), hone _ (hnot _ ha), mul_one] at h1
    exact h1
  let v : HeightOneSpectrum W.toAffine.CoordinateRing := ⟨P, hPprime, hP0⟩
  refine ⟨v, hmem, ?_⟩
  have hval_one : ∀ d : W.toAffine.CoordinateRing, d ∉ v.asIdeal →
      v.valuation W.toAffine.FunctionField (algebraMap _ _ d) = 1 := fun d hd => by
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hd
  have hle : ∀ f, w f ≤ 1 ↔ v.valuation W.toAffine.FunctionField f ≤ 1 := by
    intro f
    constructor
    · intro hwf
      by_contra hvf
      rw [not_le] at hvf
      have hf : f ≠ 0 := by rintro rfl; simp at hvf
      have hvf' : v.valuation W.toAffine.FunctionField f⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_lt_one_of_one_lt₀ hvf).le
      obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (K := W.toAffine.FunctionField) v f⁻¹ hvf'
      have hd : (d : W.toAffine.CoordinateRing) ∉ v.asIdeal := d.2
      have hvn : v.valuation W.toAffine.FunctionField (algebraMap _ _ n) < 1 := by
        rw [← hnd, Valuation.map_mul, hval_one _ hd, mul_one, map_inv₀]
        exact inv_lt_one_of_one_lt₀ hvf
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hvn
      have hwn := (hmem n).mp hvn
      rw [← hnd, Valuation.map_mul, hone _ hd, mul_one, map_inv₀] at hwn
      have : 1 < w f := by
        rwa [inv_lt_one₀ ((Valuation.pos_iff _).mpr hf)] at hwn
      exact absurd hwf (not_le.mpr this)
    · intro hvf
      obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (K := W.toAffine.FunctionField) v f hvf
      have h1 := congrArg w hnd
      rw [Valuation.map_mul, hone _ d.2, mul_one] at h1
      exact h1 ▸ hA n
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer W.toAffine.FunctionField
  exact exists_eq_pow_of_le_one_iff w _ hle hπ
end GroundTheory.Arith.Abelian
