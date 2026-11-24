-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.exists_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:28.216825+00:00
-- url     : https://prove2.me/submissions/6269ceb3-7111-44b8-9508-6a4e83520507

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_pull
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_single
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_conj
import Theorems.Thm_GlobalTheory_SiegelNormalForm_isUnit_of_lagrangian
import Theorems.Thm_GlobalTheory_SiegelNormalForm_siegel_of_relations
import Theorems.Thm_GlobalTheory_SiegelNormalForm_quad_differentiable
import Theorems.Thm_GlobalTheory_SiegelNormalForm_quad_add_sub
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_bijective_neg_bilinForm
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.SiegelNormalForm
namespace _root_.GlobalTheory.SiegelNormalForm
theorem _root_.solution : (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Q : (Fin g → ℂ) → ℂ) (b : Fin g → ℂ), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ (∀ j, b j ≠ 0) ∧ (∀ (i : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (Pi.single i 1) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = cexp (Q (z + Pi.single i 1) - Q z)) ∧ (∀ (j : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (τ.mulVec (Pi.single j 1)) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = b j * cexp (-(2 * Real.pi * I) * z j) * cexp (Q (z + τ.mulVec (Pi.single j 1)) - Q z))) := by
  intro g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  have hreal : ∀ v : Fin g → ℂ, (v ⬝ᵥ Hm *ᵥ star v).im = 0 := fun v =>
    Complex.conj_eq_iff_im.mp (_root_.GlobalTheory.SiegelNormalForm.form_conj hH v v)
  have halt : (-Ef).IsAlt := by
    intro l
    have h := hEf l l
    rw [hreal] at h
    have h' : Ef l l = 0 := by exact_mod_cast h
    simp [h']
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_of_finrank halt (_root_.GlobalTheory.bijective_neg_bilinForm hbij) hrank
  have hEll : ∀ i j, Ef (b (Sum.inl i)) (b (Sum.inl j)) = 0 := fun i j => by
    simpa using hb.left_left i j
  have hErr : ∀ i j, Ef (b (Sum.inr i)) (b (Sum.inr j)) = 0 := fun i j => by
    simpa using hb.right_right i j
  have hElr : ∀ i j, (Ef (b (Sum.inl i)) (b (Sum.inr j)) : ℝ) = if i = j then -1 else 0 := by
    intro i j
    have h := hb.left_right i j
    simp only [LinearMap.neg_apply] at h
    split_ifs at h ⊢ with hij
    · have h' : Ef (b (Sum.inl i)) (b (Sum.inr j)) = -1 := by omega
      simp [h']
    · have h' : Ef (b (Sum.inl i)) (b (Sum.inr j)) = 0 := by omega
      simp [h']
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin g) (Fin g) ℂ,
      P = Matrix.of fun k i => (b (Sum.inl i) : Fin g → ℂ) k := ⟨_, rfl⟩
  obtain ⟨P', hP'def⟩ : ∃ P' : Matrix (Fin g) (Fin g) ℂ,
      P' = Matrix.of fun k j => (b (Sum.inr j) : Fin g → ℂ) k := ⟨_, rfl⟩
  have hPcol : ∀ i, P *ᵥ Pi.single i 1 = (b (Sum.inl i) : Fin g → ℂ) := by
    intro i
    rw [mulVec_single_one]
    ext k
    simp [hPdef]
  have hP'col : ∀ j, P' *ᵥ Pi.single j 1 = (b (Sum.inr j) : Fin g → ℂ) := by
    intro j
    rw [mulVec_single_one]
    ext k
    simp [hP'def]
  have hMentry : ∀ i j, (Pᵀ * Hm * P.map star) i j =
      (b (Sum.inl i) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inl j) : Fin g → ℂ) := by
    intro i j
    rw [← _root_.GlobalTheory.SiegelNormalForm.form_single (Pᵀ * Hm * P.map star) i j,
      ← _root_.GlobalTheory.SiegelNormalForm.form_pull, hPcol, hPcol]
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix (Fin g) (Fin g) ℝ,
      Y = (Pᵀ * Hm * P.map star).map Complex.re := ⟨_, rfl⟩
  have hMY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [hYdef]
    · rw [map_apply, Complex.ofReal_im, hMentry, ← hEf, hEll]
      simp
  have hunit : IsUnit P := by
    refine _root_.GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian P Hm (fun j => (b (Sum.inr j) : Fin g → ℂ))
      hpos Y hMY fun i j => ?_
    rw [hPcol, ← hEf, hElr]
  have hinj : Function.Injective P.mulVec := mulVec_injective_iff_isUnit.mpr hunit
  have hrel : ∀ u v : Fin g → ℂ,
      u ⬝ᵥ Y.map (↑) *ᵥ star v = (P *ᵥ u) ⬝ᵥ Hm *ᵥ star (P *ᵥ v) := by
    intro u v
    rw [_root_.GlobalTheory.SiegelNormalForm.form_pull, hMY]
  have hYsymm : ∀ i j, Y j i = Y i j := by
    intro i j
    simp only [hYdef, map_apply, hMentry]
    rw [← _root_.GlobalTheory.SiegelNormalForm.form_conj hH]
    simp
  have hYpos : Y.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨IsHermitian.ext fun i j => by simpa using hYsymm i j, fun x hx => ?_⟩
    set xc : Fin g → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h
      apply hx
      ext i
      simpa [hxc] using congrFun h i
    have hPx : P *ᵥ xc ≠ 0 := fun h => hxc0 (hinj (h.trans (mulVec_zero P).symm))
    have h := hpos _ hPx
    rw [← hrel] at h
    have hre : (xc ⬝ᵥ Y.map (↑) *ᵥ star xc).re = star x ⬝ᵥ Y *ᵥ x := by
      simp [hxc, dotProduct, mulVec, Complex.re_sum]
    linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : Matrix (Fin g) (Fin g) ℂ, τ = P⁻¹ * P' := ⟨_, rfl⟩
  have hPτ : P * τ = P' := by
    rw [hτdef, ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hunit),
      Matrix.one_mul]
  have hτcol : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = (b (Sum.inr j) : Fin g → ℂ) := by
    intro j
    rw [mulVec_mulVec, hPτ, hP'col]
  obtain ⟨hτsym, hτpos, hYB⟩ := _root_.GlobalTheory.SiegelNormalForm.siegel_of_relations Y hYpos τ
    (fun i j => by
      rw [hrel, hPcol, hτcol, ← hEf, hElr])
    (fun i j => by
      rw [hrel, hτcol, hτcol, ← hEf, hErr]
      simp)

  have hcols : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ),
      A *ᵥ v = ∑ i, v i • (A *ᵥ Pi.single i 1) := by
    intro A v
    ext k
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hχne : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using hχ l
  have hYsym' : (Y.map ((↑) : ℝ → ℂ)).IsSymm := IsSymm.ext fun i j => by simp [hYsymm]
  let φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := P.toLinearEquiv' hunit.invertible
  have hφ : ∀ z, φ z = P *ᵥ z := fun z => rfl
  let c : Fin g → ℂ := fun i => Complex.log (χ (b (Sum.inl i)))
  let Q : (Fin g → ℂ) → ℂ := _root_.GlobalTheory.SiegelNormalForm.quad (Y.map (↑)) c
  have hQ : ∀ z w, Q (z + w) - Q z = Real.pi * (z ⬝ᵥ Y.map (↑) *ᵥ w) + Q w := fun z w =>
    _root_.GlobalTheory.SiegelNormalForm.quad_add_sub hYsym' c z w
  have hconj_col : ∀ j, (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (τ *ᵥ Pi.single j 1) =
      (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ (τ *ᵥ Pi.single j 1) - (2 * I) • Pi.single j 1 := by
    intro j
    have hv : star (τ *ᵥ Pi.single j 1) =
        τ *ᵥ Pi.single j 1 - (2 * I) • (fun x => ((τ x j).im : ℂ)) := by
      ext x
      simp only [mulVec_single_one, Pi.star_apply, transpose_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      apply Complex.ext <;> simp <;> ring
    have hYim : (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ (fun x => ((τ x j).im : ℂ)) =
        Pi.single j 1 := by
      ext k
      have h := congrFun (congrFun hYB k) j
      simp only [mul_apply, map_apply, one_apply] at h
      simp only [mulVec, dotProduct, map_apply, Pi.single_apply]
      have h' : ((∑ i, Y k i * (τ i j).im : ℝ) : ℂ) = ((if k = j then 1 else 0 : ℝ) : ℂ) := by
        rw [h]
      push_cast at h'
      rw [h']
      split_ifs <;> simp
    rw [hv, mulVec_sub, mulVec_smul, hYim]
  refine ⟨φ, τ, Q, fun j => χ (b (Sum.inr j)) * cexp (Real.pi / 2 *
      ((b (Sum.inr j) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inr j) : Fin g → ℂ)) -
      Q (τ *ᵥ Pi.single j 1)), hτsym, hτpos, fun z => ?_,
    _root_.GlobalTheory.SiegelNormalForm.quad_differentiable _ _, by simp [Q, _root_.GlobalTheory.SiegelNormalForm.quad],
    fun j => mul_ne_zero (hχne _) (Complex.exp_ne_zero _), fun i l z hl => ?_,
    fun j l z hl => ?_⟩
  · rw [hφ]
    constructor
    · intro hz
      let l : Λ := ⟨P *ᵥ z, hz⟩
      refine ⟨fun i => b.repr l (Sum.inl i), fun j => b.repr l (Sum.inr j), hinj ?_⟩
      have hl : P *ᵥ z = ((l : Λ) : Fin g → ℂ) := rfl
      rw [hl, ← b.sum_repr l, Submodule.coe_sum, Fintype.sum_sum_type, mulVec_add, mulVec_mulVec,
        hPτ, hcols P, hcols P']
      simp [hPcol, hP'col, Int.cast_smul_eq_zsmul]
    · rintro ⟨m, n, rfl⟩
      rw [mulVec_add, mulVec_mulVec, hPτ, hcols P, hcols P']
      refine Λ.add_mem (Λ.sum_mem fun i _ => ?_) (Λ.sum_mem fun j _ => ?_)
      · rw [hPcol, Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ (b _).2
      · rw [hP'col, Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ (b _).2
  · rw [hφ, hPcol] at hl
    obtain rfl : l = b (Sum.inl i) := Subtype.ext hl
    have h1 : (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (b (Sum.inl i) : Fin g → ℂ) =
        z ⬝ᵥ Y.map (↑) *ᵥ Pi.single i 1 := by
      rw [← hPcol, ← hrel, Pi.star_single, star_one]
    have h2 : (b (Sum.inl i) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inl i) : Fin g → ℂ) =
        Pi.single i 1 ⬝ᵥ Y.map (↑) *ᵥ Pi.single i 1 := by
      rw [← hPcol, ← hrel, Pi.star_single, star_one]
    rw [hφ, h1, h2, hQ]
    simp only [Q, _root_.GlobalTheory.SiegelNormalForm.quad, dotProduct_single, mul_one]
    rw [← add_assoc, Complex.exp_add _ (c i), Complex.exp_log (hχne _), mul_comm]
  · rw [hφ, hτcol] at hl
    obtain rfl : l = b (Sum.inr j) := Subtype.ext hl
    have h1 : (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (b (Sum.inr j) : Fin g → ℂ) =
        z ⬝ᵥ Y.map (↑) *ᵥ (τ *ᵥ Pi.single j 1) - 2 * I * z j := by
      rw [← hτcol, ← hrel, hconj_col, dotProduct_sub, dotProduct_smul, dotProduct_single,
        smul_eq_mul, mul_one]
    rw [hφ, h1, hQ]
    dsimp only
    simp only [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
