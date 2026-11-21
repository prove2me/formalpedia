-- Prove2me | solution 1 for NewtonianLipschitz.candidateMaximum_le_of_universal_safe_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:21:22.201186+00:00
-- url     : https://prove2.me/submissions/9e2fa4a9-1a41-4161-bde7-6a43940037eb

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_safe_secant_quotient_limit
public import Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (K : ℝ)
    (hK : ∀ x y : Vec3,
      (1 : ℝ) ≤ ‖x‖ → (1 : ℝ) ≤ ‖y‖ →
        ‖NewtonianPointSource.unitAxis.accelerationField x -
          NewtonianPointSource.unitAxis.accelerationField y‖ ≤
            K * ‖x - y‖) :
    candidateMaximum ≤ K := by
  let x : Vec3 :=
    normalizedVector candidateCriticalPoint candidateCriticalPoint
  let c : NewtonianPointSource := NewtonianPointSource.unitAxis
  obtain ⟨h, _hunit, hsafe, hlimit⟩ :=
    NewtonianPointSource.unitAxis_exists_safe_secant_quotient_limit
  have hxclear : (1 : ℝ) ≤ ‖x‖ := by
    change (1 : ℝ) ≤
      ‖normalizedVector candidateCriticalPoint candidateCriticalPoint‖
    rw [criticalDiagonal_cartesian_norm_eq_one]
  have hbound : ∀ s : ℝ, 0 < s →
      ‖s⁻¹ • (c.accelerationField (x + s • h) -
        c.accelerationField x)‖ ≤ K := by
    intro s hs
    obtain ⟨hclear, hdist, _⟩ := hsafe s hs
    have hpair := hK (x + s • h) x hclear hxclear
    have hpositive : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    calc
      ‖s⁻¹ • (c.accelerationField (x + s • h) -
          c.accelerationField x)‖ =
          s⁻¹ * ‖c.accelerationField (x + s • h) -
            c.accelerationField x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpositive]
      _ ≤ s⁻¹ * (K * ‖(x + s • h) - x‖) :=
        mul_le_mul_of_nonneg_left hpair hpositive
      _ = K := by
        rw [hdist]
        field_simp [ne_of_gt hs]
  have heventually :
      ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ‖s⁻¹ • (c.accelerationField (x + s • h) -
          c.accelerationField x)‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbound s hs
  exact le_of_tendsto_of_tendsto hlimit tendsto_const_nhds heventually
end NewtonianLipschitz
