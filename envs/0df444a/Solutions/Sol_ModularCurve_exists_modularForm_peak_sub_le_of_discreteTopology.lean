-- Prove2me | solution 1 for ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5d44df1e-bc68-5a67-8139-b4ef6a73fd07

import Mathlib
import Theorems.Thm_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped MatrixGroups Topology Manifold ModularForm
open UpperHalfPlane

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "exists_modularForm_eq_tsum_of_discreteTopology"
namespace E2bAux
p2m_open "ModularCurve"

section FromE1
open Complex

theorem isCompact_det_one_bounded (R : ℝ) :
    IsCompact {g : GL (Fin 2) ℝ | Matrix.GeneralLinearGroup.det g = 1 ∧
      ∀ i j, |(g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R} := by
  let C' : Set (Matrix (Fin 2) (Fin 2) ℝ) := {m | m.det = 1} ∩ {m | ∀ i j, |m i j| ≤ R}
  have hbox : IsCompact {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ R} := by
    have : {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ R} =
        Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-R) R)) := by
      ext m
      change (∀ i j, |m i j| ≤ R) ↔ ∀ i, i ∈ Set.univ → ∀ j, j ∈ Set.univ → m i j ∈ Set.Icc (-R) R
      simp [abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hC'cpt : IsCompact C' :=
    hbox.inter_left (isClosed_eq (continuous_id.matrix_det) continuous_const)

  have hdet : ∀ m ∈ C', m.det ≠ 0 := fun m hm => by rw [hm.1]; exact one_ne_zero
  let ψ : C' → GL (Fin 2) ℝ := fun m => Matrix.GeneralLinearGroup.mkOfDetNeZero m.1 (hdet m.1 m.2)
  have hψc : Continuous ψ := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    ·
      have : (fun m : C' => (((ψ m)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = fun m => (m.1).adjugate := by
        funext m
        have h1 : ((ψ m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = m.1 := rfl
        rw [Matrix.coe_units_inv, h1, Matrix.inv_def, m.2.1, Ring.inverse_one, one_smul]
      rw [this]
      exact Continuous.matrix_adjugate continuous_subtype_val
  have himage : {g : GL (Fin 2) ℝ | Matrix.GeneralLinearGroup.det g = 1 ∧
      ∀ i j, |(g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R} = Set.range ψ := by
    ext g
    constructor
    · rintro ⟨hg1, hg2⟩
      have hg1' : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, hg1, Units.val_one]
      refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) ℝ), hg1', hg2⟩, ?_⟩
      exact Units.ext rfl
    · rintro ⟨m, rfl⟩
      refine ⟨Units.ext ?_, m.2.2⟩
      simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact m.2.1
  rw [himage]
  haveI : CompactSpace C' := isCompact_iff_compactSpace.1 hC'cpt
  exact isCompact_range hψc

theorem finite_det_one_bounded {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : DiscreteTopology ↥Γ] (R : ℝ) :
    Set.Finite {γ : ↥Γ | Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ) = 1 ∧
      ∀ i j, |((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R} := by
  have hclosed : IsClosed (Γ : Set (GL (Fin 2) ℝ)) := Subgroup.isClosed_of_discrete
  have hemb : Topology.IsClosedEmbedding ((↑) : ↥Γ → GL (Fin 2) ℝ) := hclosed.isClosedEmbedding_subtypeVal
  have hcpt := hemb.isCompact_preimage (isCompact_det_one_bounded R)
  exact hcpt.finite_of_discrete

theorem coeff_bound {α β : ℝ} {z : ℂ} {y R₀ W : ℝ} (hy0 : 0 < y) (hy : y ≤ z.im) (hz : ‖z‖ ≤ R₀)
    (hw : ‖(α : ℂ) * z + β‖ ≤ W) : |α| ≤ W / y ∧ |β| ≤ W + W / y * R₀ := by
  have him : ((α : ℂ) * z + β).im = α * z.im := by simp
  have hre : ((α : ℂ) * z + β).re = α * z.re + β := by simp
  have h1 : |α| * z.im ≤ W := by
    have := Complex.abs_im_le_norm ((α : ℂ) * z + β)
    rw [him, abs_mul, abs_of_pos (hy0.trans_le hy)] at this
    exact this.trans hw
  have hα : |α| ≤ W / y := by
    rw [le_div_iff₀ hy0]
    calc |α| * y ≤ |α| * z.im := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ ≤ W := h1
  refine ⟨hα, ?_⟩
  have h2 : |α * z.re + β| ≤ W := by
    have := Complex.abs_re_le_norm ((α : ℂ) * z + β)
    rw [hre] at this
    exact this.trans hw
  have h3 : |z.re| ≤ R₀ := (Complex.abs_re_le_norm z).trans hz
  have hW : 0 ≤ W := (norm_nonneg _).trans hw
  calc |β| = |(α * z.re + β) - α * z.re| := by ring_nf
    _ ≤ |α * z.re + β| + |α * z.re| := abs_sub _ _
    _ ≤ W + |α| * |z.re| := by rw [abs_mul]; linarith
    _ ≤ W + W / y * R₀ := by
        gcongr

theorem finite_smul_mem {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (K : Set ℍ) {y R₀ : ℝ} (hy0 : 0 < y) (hK : ∀ τ ∈ K, y ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ R₀) :
    Set.Finite {γ : ↥Γ | ∃ τ ∈ K, (γ : GL (Fin 2) ℝ) • τ ∈ K} := by

  have hR₀ : ∀ τ ∈ K, 0 ≤ R₀ := fun τ hτ => (norm_nonneg _).trans (hK τ hτ).2
  set D : ℝ := Real.sqrt (R₀ / y) with hD
  set W : ℝ := R₀ * D with hW
  set R : ℝ := max (max (D / y) (D + D / y * R₀)) (max (W / y) (W + W / y * R₀)) with hRdef
  refine (finite_det_one_bounded (Γ := Γ) R).subset ?_
  rintro γ ⟨τ, hτ, hτ'⟩
  have hγdet := hdet _ γ.2
  have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ)) : ℝ) := by rw [hγdet]; simp
  refine ⟨hγdet, ?_⟩
  obtain ⟨hy1, hn1⟩ := hK τ hτ
  obtain ⟨hy2, hn2⟩ := hK _ hτ'
  have hR₀' : 0 ≤ R₀ := hR₀ τ hτ

  have him := UpperHalfPlane.im_smul_eq_div_normSq (γ : GL (Fin 2) ℝ) τ
  rw [hγdet, Units.val_one, abs_one, one_mul] at him
  have hnsq_pos : 0 < Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) :=
    Complex.normSq_pos.2 (denom_ne_zero _ _)
  have hdenom_sq : Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) ≤ R₀ / y := by
    have h1 : Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) = τ.im / ((γ : GL (Fin 2) ℝ) • τ).im := by
      rw [him]; field_simp
    rw [h1]
    have hτim : τ.im ≤ R₀ := (Complex.abs_im_le_norm (τ : ℂ)).trans hn1 |> le_trans (le_abs_self _)
    exact div_le_div₀ hR₀' hτim hy0 hy2
  have hdenom : ‖denom (γ : GL (Fin 2) ℝ) τ‖ ≤ D := by
    rw [hD, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm]
    exact Real.sqrt_le_sqrt hdenom_sq
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.sqrt_nonneg _
  have hnum : ‖num (γ : GL (Fin 2) ℝ) τ‖ ≤ W := by
    have hcoe := UpperHalfPlane.coe_smul_of_det_pos hdetpos τ
    have : num (γ : GL (Fin 2) ℝ) τ = (((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ := by
      rw [hcoe, div_mul_cancel₀ _ (denom_ne_zero _ _)]
    rw [this, norm_mul, hW]
    exact mul_le_mul hn2 hdenom (norm_nonneg _) hR₀'

  have hc := coeff_bound (α := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
    (β := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hy0 hy1 hn1 (by simpa [denom] using hdenom)
  have ha := coeff_bound (α := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
    (β := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hy0 hy1 hn1 (by simpa [num] using hnum)
  intro i j
  fin_cases i <;> fin_cases j
  · exact ha.1.trans (by rw [hRdef]; apply le_max_of_le_right; exact le_max_left _ _)
  · exact ha.2.trans (by rw [hRdef]; apply le_max_of_le_right; exact le_max_right _ _)
  · exact hc.1.trans (by rw [hRdef]; apply le_max_of_le_left; exact le_max_left _ _)
  · exact hc.2.trans (by rw [hRdef]; apply le_max_of_le_left; exact le_max_right _ _)

end FromE1

theorem normSq_sub_conj_sub_normSq_sub (w τ₀ : ℍ) :
    ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ 2 - ‖(w : ℂ) - (τ₀ : ℂ)‖ ^ 2 = 4 * w.im * τ₀.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem norm_sub_le_norm_sub_conj (w τ₀ : ℍ) :
    ‖(w : ℂ) - (τ₀ : ℂ)‖ ≤ ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ := by
  have h := normSq_sub_conj_sub_normSq_sub w τ₀
  have hpos : 0 ≤ 4 * w.im * τ₀.im := by positivity
  nlinarith [norm_nonneg ((w : ℂ) - (τ₀ : ℂ)), norm_nonneg ((w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))]

theorem im_add_im_le_norm_sub_conj (w τ₀ : ℍ) :
    w.im + τ₀.im ≤ ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ := by
  have h := Complex.abs_im_le_norm ((w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))
  have him : ((w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)).im = w.im + τ₀.im := by
    simp only [Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im]; ring
  rw [him, abs_of_pos (by positivity)] at h
  exact h

theorem norm_sub_conj_pos (w τ₀ : ℍ) : 0 < ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ :=
  lt_of_lt_of_le (by positivity) (im_add_im_le_norm_sub_conj w τ₀)

theorem sub_conj_ne_zero (w τ₀ : ℍ) : (w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) ≠ 0 :=
  norm_pos_iff.mp (norm_sub_conj_pos w τ₀)

theorem norm_sub_conj_le (w τ₀ : ℍ) :
    ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ≤ ‖(w : ℂ) - (τ₀ : ℂ)‖ + 2 * τ₀.im := by
  have : (w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) = ((w : ℂ) - (τ₀ : ℂ)) + ((τ₀ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖(τ₀ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ = 2 * τ₀.im := by
    have : (τ₀ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) = (2 * τ₀.im : ℝ) * Complex.I := by
      apply Complex.ext
      · simp [UpperHalfPlane.coe_re]
      · simp [UpperHalfPlane.coe_im]; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [h2]

def phi (τ₀ : ℍ) (n : ℕ) (k : ℤ) (w : ℍ) : ℂ :=
  (((w : ℂ) - (τ₀ : ℂ)) / ((w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n * ((w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k)

theorem norm_phi_le (τ₀ : ℍ) (n : ℕ) (k : ℤ) (w : ℍ) :
    ‖phi τ₀ n k w‖ ≤ ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ (-k) := by
  unfold phi
  rw [norm_mul, norm_pow, norm_div, norm_zpow]
  have h1 : ‖(w : ℂ) - (τ₀ : ℂ)‖ / ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ≤ 1 :=
    (div_le_one (norm_sub_conj_pos w τ₀)).mpr (norm_sub_le_norm_sub_conj w τ₀)
  have h0 : 0 ≤ ‖(w : ℂ) - (τ₀ : ℂ)‖ / ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ := by positivity
  have h2 : (‖(w : ℂ) - (τ₀ : ℂ)‖ / ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖) ^ n ≤ 1 := pow_le_one₀ h0 h1
  have h3 : 0 ≤ ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ (-k) := zpow_nonneg (norm_nonneg _) _
  calc _ ≤ 1 * ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ (-k) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := one_mul _

theorem mdifferentiable_phi (τ₀ : ℍ) (n : ℕ) (k : ℤ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (phi τ₀ n k) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : (z : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) ≠ 0 := by
    have := sub_conj_ne_zero ⟨z, hz⟩ τ₀
    simpa using this
  have h1 : DifferentiableAt ℂ (fun y : ℂ => y - (τ₀ : ℂ)) z := differentiableAt_id.sub_const _
  have h2 : DifferentiableAt ℂ (fun y : ℂ => y - (starRingEnd ℂ) (τ₀ : ℂ)) z := differentiableAt_id.sub_const _
  have hd : DifferentiableAt ℂ (fun y : ℂ =>
      ((y - (τ₀ : ℂ)) / (y - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n * (y - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k)) z :=
    ((h1.div h2 hz').pow n).mul (h2.zpow (Or.inl hz'))
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with x hx
  simp only [Function.comp_apply, phi, ofComplex_apply_of_im_pos hx, UpperHalfPlane.coe_mk]

theorem phi_decay (τ₀ : ℍ) (n : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    ∃ M : ℝ, ∀ w : ℍ, ‖phi τ₀ n k w‖ * ‖(w : ℂ) + Complex.I‖ ^ k ≤ M := by

  set c₀ : ℝ := 1 + ‖(starRingEnd ℂ) (τ₀ : ℂ) + Complex.I‖ / τ₀.im with hc₀
  refine ⟨c₀ ^ k, fun w => ?_⟩
  have hB := norm_sub_conj_pos w τ₀
  have hratio : ‖(w : ℂ) + Complex.I‖ ≤ c₀ * ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ := by
    have h1 : ‖(w : ℂ) + Complex.I‖ ≤ ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ + ‖(starRingEnd ℂ) (τ₀ : ℂ) + Complex.I‖ := by
      have : (w : ℂ) + Complex.I = ((w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) + ((starRingEnd ℂ) (τ₀ : ℂ) + Complex.I) := by ring
      rw [this]; exact norm_add_le _ _
    have h2 : ‖(starRingEnd ℂ) (τ₀ : ℂ) + Complex.I‖ ≤
        ‖(starRingEnd ℂ) (τ₀ : ℂ) + Complex.I‖ / τ₀.im * ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ τ₀.im_pos]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact le_trans (by linarith [w.im_pos]) (im_add_im_le_norm_sub_conj w τ₀)
    rw [hc₀, add_mul, one_mul]
    linarith
  have hc₀pos : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg hk⟩
  calc ‖phi τ₀ n k w‖ * ‖(w : ℂ) + Complex.I‖ ^ k
      ≤ ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ (-k) * ‖(w : ℂ) + Complex.I‖ ^ k :=
        mul_le_mul_of_nonneg_right (norm_phi_le τ₀ n k w) (zpow_nonneg (norm_nonneg _) _)
    _ = (‖(w : ℂ) + Complex.I‖ / ‖(w : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖) ^ k := by
        rw [div_zpow, zpow_neg, div_eq_inv_mul]
    _ ≤ c₀ ^ k := by
        rw [← hm, zpow_natCast, zpow_natCast]
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_iff₀ hB]
        exact hratio

theorem gauge_identity {γ : GL (Fin 2) ℝ} (hγ : Matrix.GeneralLinearGroup.det γ = 1) (σ τ₀ : ℍ) :
    4 * σ.im * τ₀.im / (‖(((γ • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ 2 * ‖denom γ σ‖ ^ 2) =
      1 - (‖(((γ • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ / ‖(((γ • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖) ^ 2 := by
  have him := UpperHalfPlane.im_smul_eq_div_normSq γ σ
  rw [hγ, Units.val_one, abs_one, one_mul] at him

  have hJ : ‖denom γ σ‖ ^ 2 = Complex.normSq (denom γ σ) := Complex.sq_norm _
  have hJpos : 0 < Complex.normSq (denom γ σ) := Complex.normSq_pos.2 (denom_ne_zero γ σ)
  have hσ : σ.im = (γ • σ).im * Complex.normSq (denom γ σ) := by
    rw [him]; field_simp
  have hB := norm_sub_conj_pos (γ • σ) τ₀
  have hkey := normSq_sub_conj_sub_normSq_sub (γ • σ) τ₀
  rw [hJ, hσ, div_pow]
  field_simp
  nlinarith [hkey, hJpos, hB]

theorem exists_nhds_norm_sub_ge {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (τ₀ σ₀ : ℍ) :
    ∃ U : Set ℍ, IsOpen U ∧ σ₀ ∈ U ∧ ∃ r : ℝ, 0 < r ∧
      ∀ σ ∈ U, ∀ γ : ↥Γ, (γ : GL (Fin 2) ℝ) • σ₀ ≠ τ₀ →
        r ≤ ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ := by
  classical

  obtain ⟨y, hy0, hyσ, hyτ⟩ : ∃ y : ℝ, 0 < y ∧ y < σ₀.im ∧ y < τ₀.im :=
    ⟨min σ₀.im τ₀.im / 2, by positivity,
      by have := min_le_left σ₀.im τ₀.im; have := σ₀.im_pos; linarith,
      by have := min_le_right σ₀.im τ₀.im; have := τ₀.im_pos; linarith⟩
  set R₀ : ℝ := max ‖(σ₀ : ℂ)‖ ‖(τ₀ : ℂ)‖ + 1 with hR₀
  have hRσ : ‖(σ₀ : ℂ)‖ < R₀ := by rw [hR₀]; have := le_max_left ‖(σ₀ : ℂ)‖ ‖(τ₀ : ℂ)‖; linarith
  have hRτ : ‖(τ₀ : ℂ)‖ < R₀ := by rw [hR₀]; have := le_max_right ‖(σ₀ : ℂ)‖ ‖(τ₀ : ℂ)‖; linarith
  set K : Set ℍ := {τ : ℍ | y ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ R₀} with hK
  have hKfin : Set.Finite {γ : ↥Γ | ∃ τ ∈ K, (γ : GL (Fin 2) ℝ) • τ ∈ K} :=
    finite_smul_mem hdet K hy0 (fun τ hτ => hτ)
  set F₁ : Finset ↥Γ := hKfin.toFinset.filter (fun γ => (γ : GL (Fin 2) ℝ) • σ₀ ≠ τ₀) with hF₁
  let δ : ↥Γ → ℝ := fun γ => ‖((((γ : GL (Fin 2) ℝ) • σ₀ : ℍ)) : ℂ) - (τ₀ : ℂ)‖
  have hδpos : ∀ γ ∈ F₁, 0 < δ γ := by
    intro γ hγ
    have hne := (Finset.mem_filter.mp hγ).2
    exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hne (UpperHalfPlane.ext_iff.mpr h))

  obtain ⟨ε₀, hε₀, hε₁, hε₂⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ τ₀.im - y ∧ ε₀ ≤ R₀ - ‖(τ₀ : ℂ)‖ :=
    ⟨min (τ₀.im - y) (R₀ - ‖(τ₀ : ℂ)‖), lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩

  obtain ⟨r, hr0, hrε, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ε₀ ∧ ∀ γ ∈ F₁, r ≤ δ γ / 2 := by
    by_cases hne : F₁.Nonempty
    · obtain ⟨γm, hγm, hmin⟩ := F₁.exists_min_image δ hne
      refine ⟨min ε₀ (δ γm / 2), lt_min hε₀ (by have := hδpos γm hγm; positivity), min_le_left _ _,
        fun γ hγ => (min_le_right _ _).trans ?_⟩
      have := hmin γ hγ
      linarith
    · exact ⟨ε₀, hε₀, le_rfl, fun γ hγ => (hne ⟨γ, hγ⟩).elim⟩

  have hcont : ∀ γ : ↥Γ, Continuous fun σ : ℍ => ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ := fun γ =>
    continuous_norm.comp ((UpperHalfPlane.continuous_coe.comp (continuous_const_smul _)).sub continuous_const)
  set U : Set ℍ := {σ : ℍ | y < σ.im ∧ ‖(σ : ℂ)‖ < R₀} ∩
    ⋂ γ ∈ F₁, {σ : ℍ | δ γ / 2 < ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖} with hU
  refine ⟨U, ?_, ?_, r, hr0, ?_⟩
  · refine IsOpen.inter ?_ (isOpen_biInter_finset fun γ _ => isOpen_lt continuous_const (hcont γ))
    exact (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
      (isOpen_lt (continuous_norm.comp UpperHalfPlane.continuous_coe) continuous_const)
  · refine ⟨⟨hyσ, hRσ⟩, Set.mem_iInter₂.mpr fun γ hγ => ?_⟩
    show δ γ / 2 < δ γ
    have := hδpos γ hγ
    linarith
  · intro σ hσ γ hγne
    obtain ⟨⟨hσy, hσR⟩, hσ2⟩ := hσ
    by_cases hγF : γ ∈ hKfin.toFinset
    · have hγ1 : γ ∈ F₁ := Finset.mem_filter.mpr ⟨hγF, hγne⟩
      have h := Set.mem_iInter₂.mp hσ2 γ hγ1
      have h' : δ γ / 2 < ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ := h
      linarith [hrδ γ hγ1]
    · by_contra hlt
      have hlt : ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ < r := lt_of_not_ge hlt
      apply hγF
      rw [Set.Finite.mem_toFinset]
      refine ⟨σ, ⟨hσy.le, hσR.le⟩, ?_, ?_⟩
      ·
        have h1 := Complex.abs_im_le_norm (((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ))
        rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h1
        have h2 := abs_sub_lt_iff.mp (lt_of_le_of_lt h1 hlt)
        linarith
      · have h1 := norm_sub_norm_le ((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) (τ₀ : ℂ)
        linarith

end ModularCurve.E2bAux

open ModularCurve.E2bAux in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (τ₀ σ₀ : ℍ) :
    ∃ U : Set ℍ, IsOpen U ∧ σ₀ ∈ U ∧ ∃ A ϑ : ℝ, 0 ≤ A ∧ 0 ≤ ϑ ∧ ϑ < 1 ∧
      ∀ (n : ℕ) (k : ℤ), 4 ≤ k →
        ∃ P : ModularForm Γ k,
          (∀ τ : ℍ, P τ = ∑' γ : ↥Γ,
            (((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)) ∧
          (∀ σ : ℍ, σ ∈ U →
            ‖P σ - ∑' γ : ↥Γ, Set.indicator {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • σ₀ = τ₀} (fun γ : ↥Γ =>
              (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)) γ‖
              ≤ A * ϑ ^ k * (2 * Real.sqrt (σ.im * τ₀.im)) ^ (-k)) := by
  classical
  haveI hΓ1 : Γ.HasDetOne := ⟨fun {γ} hγ => hdet γ hγ⟩

  obtain ⟨U₁, hU₁o, hσU₁, r, hr, hfar⟩ := exists_nhds_norm_sub_ge hdet τ₀ σ₀

  obtain ⟨M₄, hM₄⟩ := phi_decay τ₀ 0 4 (by norm_num)
  obtain ⟨hloc, -⟩ := ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology Γ hdet hcusp 4 le_rfl
    (phi τ₀ 0 4) (mdifferentiable_phi τ₀ 0 4) ⟨M₄, hM₄⟩
  obtain ⟨U₂, hU₂o, hσU₂, u, hu, hmaj⟩ := hloc σ₀

  have hT := τ₀.im_pos
  set c : ℝ := r / (r + 2 * τ₀.im) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c < 1 := by rw [hc, div_lt_one (by positivity)]; linarith
  set Θ : ℝ := Real.sqrt (1 - c ^ 2) with hΘ
  have hΘsq : Θ ^ 2 = 1 - c ^ 2 := by rw [hΘ]; exact Real.sq_sqrt (by nlinarith)
  have hΘ0 : 0 < Θ := by rw [hΘ]; exact Real.sqrt_pos.mpr (by nlinarith)
  have hΘ1 : Θ < 1 := by
    rw [hΘ, Real.sqrt_lt' one_pos]; nlinarith
  set Y : ℝ := 2 * σ₀.im with hY
  set S : ℝ := ∑' γ : ↥Γ, u γ with hS
  have hu0 : ∀ γ, 0 ≤ u γ := fun γ => (norm_nonneg _).trans (hmaj γ σ₀ hσU₂)
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  set A : ℝ := S * (4 * Y * τ₀.im) ^ 2 / Θ ^ 4 with hA
  refine ⟨U₁ ∩ U₂ ∩ {σ : ℍ | σ.im < Y}, ?_, ⟨⟨hσU₁, hσU₂⟩, ?_⟩, A, Θ, ?_, hΘ0.le, hΘ1, ?_⟩
  · exact (hU₁o.inter hU₂o).inter (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  · show σ₀.im < Y
    rw [hY]; linarith [σ₀.im_pos]
  · rw [hA]; positivity
  intro n k hk
  obtain ⟨Mk, hMk⟩ := phi_decay τ₀ n k (by linarith)
  obtain ⟨-, P, hP⟩ := ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology Γ hdet hcusp k hk
    (phi τ₀ n k) (mdifferentiable_phi τ₀ n k) ⟨Mk, hMk⟩
  refine ⟨P, fun τ => by rw [hP τ]; rfl, ?_⟩
  intro σ hσ
  obtain ⟨⟨hσ1, hσ2⟩, hσY⟩ := hσ
  have hσY' : σ.im < Y := hσY

  set D : ℝ := 2 * Real.sqrt (σ.im * τ₀.im) with hD
  have hD0 : 0 < D := by rw [hD]; have := σ.im_pos; positivity
  have hD2 : D ^ 2 = 4 * σ.im * τ₀.im := by
    rw [hD, mul_pow, Real.sq_sqrt (by have := σ.im_pos; positivity)]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = 4 + (m : ℤ) := ⟨(k - 4).toNat, by omega⟩

  set F : Set ↥Γ := {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • σ₀ = τ₀} with hF
  set t : ↥Γ → ℂ := fun γ : ↥Γ =>
    (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k) with ht
  have hPσ : P σ = ∑' γ, t γ := by rw [hP σ, ht]; simp only [phi]

  set X : ↥Γ → ℝ := fun γ =>
    (‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ * ‖denom (γ : GL (Fin 2) ℝ) σ‖)⁻¹ with hX
  have hab : ∀ γ : ↥Γ, 0 < ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ * ‖denom (γ : GL (Fin 2) ℝ) σ‖ :=
    fun γ => mul_pos (norm_sub_conj_pos _ _) (norm_pos_iff.mpr (denom_ne_zero _ _))
  have hX0 : ∀ γ, 0 < X γ := fun γ => by simp only [hX]; exact inv_pos.mpr (hab γ)

  have hnorm_t : ∀ γ, ‖t γ‖ ≤ X γ ^ 4 * X γ ^ m := by
    intro γ
    have hk' : k = ((4 + m : ℕ) : ℤ) := by rw [hm]; push_cast; ring
    have e2 : X γ ^ 4 * X γ ^ m =
        ((‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ * ‖denom (γ : GL (Fin 2) ℝ) σ‖) ^ (4 + m))⁻¹ := by
      simp only [hX]; rw [← pow_add, inv_pow]
    rw [e2, ht]
    dsimp only
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, norm_pow, norm_div, mul_assoc, ← mul_zpow, hk', zpow_neg, zpow_natCast]
    refine mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) ?_)
    exact (div_le_one (norm_sub_conj_pos _ _)).mpr (norm_sub_le_norm_sub_conj _ _)

  have hX4 : ∀ γ, X γ ^ 4 ≤ u γ := by
    intro γ
    have h := hmaj γ σ hσ2
    simp only [phi, pow_zero, one_mul, norm_mul, norm_zpow] at h
    have e : X γ ^ 4 = ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ ^ (-4 : ℤ) *
        ‖denom (γ : GL (Fin 2) ℝ) σ‖ ^ (-4 : ℤ) := by
      simp only [hX]
      rw [← mul_zpow, zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast, inv_pow]
    rw [e]; exact h

  have hgauge : ∀ γ : ↥Γ, (X γ * D) ^ 2 =
      1 - (‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ /
        ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖) ^ 2 := by
    intro γ
    rw [← gauge_identity (hdet _ γ.2) σ τ₀, mul_pow, hD2]
    simp only [hX]
    rw [inv_pow, mul_pow]
    field_simp
  have hXD : ∀ γ, X γ * D ≤ 1 := by
    intro γ
    have h := hgauge γ
    have : (X γ * D) ^ 2 ≤ 1 := by rw [h]; linarith [sq_nonneg (‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ /
        ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖)]
    exact (sq_le_one_iff₀ (by have := hX0 γ; positivity)).mp this
  have hXΘ : ∀ γ, γ ∉ F → X γ * D ≤ Θ := by
    intro γ hγ
    have hγ' : (γ : GL (Fin 2) ℝ) • σ₀ ≠ τ₀ := hγ
    have hfar' := hfar σ hσ1 γ hγ'
    set a' := ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (τ₀ : ℂ)‖ with ha'
    set a := ‖((((γ : GL (Fin 2) ℝ) • σ : ℍ)) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)‖ with ha
    have hapos : 0 < a := norm_sub_conj_pos _ _
    have hale : a ≤ a' + 2 * τ₀.im := norm_sub_conj_le _ _
    have hρ : c ≤ a' / a := by
      rw [hc, div_le_div_iff₀ (by positivity) hapos]
      nlinarith
    have h2 : (X γ * D) ^ 2 ≤ Θ ^ 2 := by
      rw [hgauge γ, hΘsq]
      nlinarith [hρ, hc0]
    exact (pow_le_pow_iff_left₀ (by have := hX0 γ; positivity) hΘ0.le two_ne_zero).mp h2

  have hbd' : ∀ γ, ‖t γ‖ ≤ (1 / D) ^ m * u γ := by
    intro γ
    have h1 : X γ ≤ 1 / D := by rw [le_div_iff₀ hD0]; exact hXD γ
    calc ‖t γ‖ ≤ X γ ^ 4 * X γ ^ m := hnorm_t γ
      _ ≤ u γ * (1 / D) ^ m := mul_le_mul (hX4 γ) (pow_le_pow_left₀ (hX0 γ).le h1 m) (by positivity) (hu0 γ)
      _ = (1 / D) ^ m * u γ := mul_comm _ _
  have hbd : ∀ γ, ‖Set.indicator Fᶜ t γ‖ ≤ (Θ / D) ^ m * u γ := by
    intro γ
    by_cases hγ : γ ∈ F
    · rw [Set.indicator_of_notMem (fun h => h hγ : γ ∉ Fᶜ), norm_zero]; exact mul_nonneg (by positivity) (hu0 γ)
    · rw [Set.indicator_of_mem (Set.mem_compl hγ)]
      have h1 : X γ ≤ Θ / D := by rw [le_div_iff₀ hD0]; exact hXΘ γ hγ
      calc ‖t γ‖ ≤ X γ ^ 4 * X γ ^ m := hnorm_t γ
        _ ≤ u γ * (Θ / D) ^ m := mul_le_mul (hX4 γ) (pow_le_pow_left₀ (hX0 γ).le h1 m) (by positivity) (hu0 γ)
        _ = (Θ / D) ^ m * u γ := mul_comm _ _

  have hst : Summable t := Summable.of_norm_bounded (hu.mul_left _) hbd'
  have hsm : Summable (Set.indicator F t) := hst.indicator _
  have hsc : Summable (Set.indicator Fᶜ t) := hst.indicator _
  have hdiff : P σ - ∑' γ, Set.indicator F t γ = ∑' γ, Set.indicator Fᶜ t γ := by
    rw [hPσ, ← hst.tsum_sub hsm]
    congr 1
    funext γ
    rw [Set.indicator_compl, Pi.sub_apply]
  show ‖P σ - ∑' γ, Set.indicator F t γ‖ ≤ A * Θ ^ k * D ^ (-k)
  rw [hdiff]
  have hD4 : D ^ 4 ≤ (4 * Y * τ₀.im) ^ 2 := by
    rw [show D ^ 4 = (D ^ 2) ^ 2 by ring, hD2]
    have : 4 * σ.im * τ₀.im ≤ 4 * Y * τ₀.im := by nlinarith [hσY', hT]
    exact pow_le_pow_left₀ (by have := σ.im_pos; positivity) this 2
  have key : A * Θ ^ k * D ^ (-k) = (Θ / D) ^ m * S * ((4 * Y * τ₀.im) ^ 2 / D ^ 4) := by
    have hk' : k = ((4 + m : ℕ) : ℤ) := by rw [hm]; push_cast; ring
    rw [hk', zpow_neg, zpow_natCast, zpow_natCast, hA, div_pow, pow_add, pow_add]
    field_simp
  calc ‖∑' γ, Set.indicator Fᶜ t γ‖ ≤ ∑' γ, ‖Set.indicator Fᶜ t γ‖ := norm_tsum_le_tsum_norm hsc.norm
    _ ≤ ∑' γ, (Θ / D) ^ m * u γ := Summable.tsum_le_tsum hbd hsc.norm (hu.mul_left _)
    _ = (Θ / D) ^ m * S := by rw [tsum_mul_left]
    _ ≤ (Θ / D) ^ m * S * ((4 * Y * τ₀.im) ^ 2 / D ^ 4) :=
        le_mul_of_one_le_right (by positivity) ((one_le_div (by positivity)).mpr hD4)
    _ = A * Θ ^ k * D ^ (-k) := key.symm

end
end S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology (solution)
