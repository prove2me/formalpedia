-- Prove2me | solution 1 for GlobalTheory.two_dvd_of_entire_sign_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:21:57.891968+00:00
-- url     : https://prove2.me/submissions/4c4a41d5-ade6-4aa0-ac9c-41abd57a869b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
import Theorems.Thm_GlobalTheory_entire_eq_zero_of_mul_continuous_eq_zero
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory
open Complex Matrix NumberField Filter Topology in
private theorem span_real_period_lattice_full {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) :
    Submodule.span ℝ (Set.range fun p : (Fin g → ℤ) × (Fin g → ℤ) =>
      τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec p.1 + _root_.ReciprocityTheory.PTheta.ofIntVec p.2) = ⊤ := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ
  obtain ⟨-, hY⟩ := hτ
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hYdef
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY.det_pos.ne'
  rw [eq_top_iff]
  intro v _
  set a : Fin g → ℝ := Y⁻¹ *ᵥ fun i => (v i).im
  set u : Fin g → ℝ := (fun i => (v i).re) - (τ.map Complex.re) *ᵥ a
  have hYa : Y *ᵥ a = fun i => (v i).im := by
    simp only [a, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hYu, Matrix.one_mulVec]
  have hv : v = ∑ j, a j • (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec (Pi.single j 1) + _root_.ReciprocityTheory.PTheta.ofIntVec 0)
      + ∑ j, u j • (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec 0 + _root_.ReciprocityTheory.PTheta.ofIntVec (Pi.single j 1)) := by
    funext i
    have hi := congrFun hYa i
    simp only [Matrix.mulVec, dotProduct, Y, Matrix.map_apply] at hi
    apply Complex.ext
    · simp [Finset.sum_apply, Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.PTheta.ofIntVec, Pi.single_apply, u]
      rw [Finset.sum_congr rfl fun x _ => mul_comm (a x) _]
      ring
    · simp [Finset.sum_apply, Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.PTheta.ofIntVec, Pi.single_apply, u]
      rw [← hi]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hv]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨(Pi.single j 1, 0), rfl⟩
  · exact Submodule.subset_span ⟨(0, Pi.single j 1), rfl⟩
section Transform
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {τ : Matrix (Fin g) (Fin g) ℂ}
end Transform
end GlobalTheory
end
end

set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open Complex Matrix NumberField Filter Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) {σ : (Fin g → ℂ) → ℂ} (hσ : Differentiable ℂ σ) (h0 : σ 0 ≠ 0)
    {N : (Fin g → ℤ) → (Fin g → ℤ) → ℤ}
    (h : ∀ m m' z, σ (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') = _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) * σ z)
    (m m' : Fin g → ℤ) : 2 ∣ N m m' := by
  have hsq : ∀ z w, σ z ^ 2 = σ w ^ 2 :=
    _root_.GlobalTheory.entire_apply_eq_of_periodic_of_span_real (F := fun z => σ z ^ 2) (hσ.pow 2)
      (span_real_period_lattice_full hτ) (by
        rintro x _ ⟨⟨n, n'⟩, rfl⟩
        simp only
        rw [← add_assoc, h, mul_pow, _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.eC_pow,
          show ((2 : ℕ) : ℂ) * ((N n n' : ℂ) / 2) = ((N n n' : ℤ) : ℂ) by push_cast; ring,
          _root_.ReciprocityTheory.PTheta.eC_int, one_mul])
  have hconst : ∀ z, σ z - σ 0 = 0 := by
    refine _root_.GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero (t := fun z => σ z + σ 0)
      (hσ.sub_const _) (hσ.continuous.add continuous_const) ?_ ?_
    · intro ht
      have := congrFun ht 0
      simp only [Pi.zero_apply] at this
      exact h0 (by linear_combination this / 2)
    · intro z
      have := hsq z 0
      linear_combination this
  have he : _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) = 1 := by
    have h1 := h m m' 0
    rw [zero_add, sub_eq_zero.mp (hconst _)] at h1
    have h2 : (_root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) - 1) * σ 0 = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right h0)
  have hz := _root_.GlobalTheory.intCast_zmod_eq_of_eC_eq (N := 2) two_pos (p := N m m') (q := 0)
    (by rw [show ((N m m' : ℤ) : ℂ) / ((2 : ℕ) : ℂ) = (N m m' : ℂ) / 2 by norm_num, he]
        simp [_root_.ReciprocityTheory.PTheta.eC_zero])
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by simpa using hz)
end _root_.GlobalTheory
end GlobalTheory
