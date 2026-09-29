-- Prove2me | solution 1 for ModularCurve.exists_eq_const_of_norm_multiplier_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2e45e377-8529-5e63-b775-07e1ebd54f64

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one

open scoped MatrixGroups Real Manifold ModularForm
open UpperHalfPlane Filter Topology Complex Function Metric

namespace ModularCurve
namespace UnitaryAutomorphicUnit

local notation "𝕢" => Function.Periodic.qParam

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (δ : SL(2, ℤ)) :
    δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have hconj : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ hTmem δ
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hconj).2.2.1

section Main

variable {N : ℕ} [NeZero N] {F : ℍ → ℂ} {χ : CongruenceSubgroup.Gamma0 N → ℂ}

local notation "Γ" => CongruenceSubgroup.Gamma0 N

structure Hyp (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ) : Prop where
  holo : DifferentiableOn ℂ (fun z : ℂ => F (ofComplex z)) {z : ℂ | 0 < z.im}
  mult : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ
  unit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1
  cusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)

omit [NeZero N] in

theorem norm_apply_smul (h : Hyp F χ) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
    ‖F (γ • z)‖ = ‖F z‖ := by
  have := h.mult ⟨γ, hγ⟩ z
  rw [show ((⟨γ, hγ⟩ : Γ) : SL(2, ℤ)) = γ from rfl] at this
  rw [this, norm_mul, h.unit, one_mul]

omit [NeZero N] in

theorem apply_smul_T_zpow_smul (h : Hyp F χ) (δ : SL(2, ℤ)) (w : ℍ) :
    F (δ • (ModularGroup.T ^ (N : ℤ) • w)) = F (δ • w) := by
  obtain ⟨L, hL0, hL⟩ := h.cusp δ
  set γ₀ : Γ := ⟨δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹, conj_T_zpow_mem_Gamma0 N δ⟩ with hγ₀
  have hkey : ∀ w : ℍ, (γ₀ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)
      = δ • (ModularGroup.T ^ (N : ℤ) • w) := by
    intro w
    rw [hγ₀]
    change (δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w) = _
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  have hc' : ∀ w : ℍ, F (δ • (ModularGroup.T ^ (N : ℤ) • w)) = χ γ₀ * F (δ • w) := by
    intro w
    rw [← hkey]
    exact h.mult γ₀ (δ • w)

  have hlim1 : Tendsto (fun w : ℍ => F (δ • (ModularGroup.T ^ (N : ℤ) • w))) atImInfty (𝓝 L) := by
    have hfun : (fun w : ℍ => F (δ • (ModularGroup.T ^ (N : ℤ) • w)))
        = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => (((N : ℤ) : ℤ) : ℝ) +ᵥ w := by
      funext w
      simp only [Function.comp_apply, UpperHalfPlane.modular_T_zpow_smul]
    rw [hfun]
    exact hL.comp (tendsto_vadd_atImInfty _)
  have hlim2 : Tendsto (fun w : ℍ => F (δ • (ModularGroup.T ^ (N : ℤ) • w))) atImInfty
      (𝓝 (χ γ₀ * L)) := by
    have : (fun w : ℍ => F (δ • (ModularGroup.T ^ (N : ℤ) • w))) = fun w => χ γ₀ * F (δ • w) :=
      funext hc'
    rw [this]
    exact hL.const_mul _
  have hχ1 : χ γ₀ = 1 := by
    have hEq : L = χ γ₀ * L := tendsto_nhds_unique hlim1 hlim2
    have : (χ γ₀ - 1) * L = 0 := by rw [sub_mul, one_mul, ← hEq, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hL0
  rw [hc' w, hχ1, one_mul]

noncomputable def K (F : ℍ → ℂ) (ρ : SL(2, ℤ)) : ℍ → ℂ := fun w => F (ρ⁻¹ • w)

omit [NeZero N] in
theorem K_periodic (h : Hyp F χ) (ρ : SL(2, ℤ)) :
    Periodic (K F ρ ∘ ofComplex) (N : ℝ) := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + (N : ℝ)).im := by simpa using hz
    simp only [Function.comp_apply, K]
    rw [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz]
    have hT : (⟨z + (N : ℝ), hz'⟩ : ℍ) = ModularGroup.T ^ (N : ℤ) • (⟨z, hz⟩ : ℍ) := by
      rw [UpperHalfPlane.modular_T_zpow_smul]
      ext1
      simp [UpperHalfPlane.coe_vadd, add_comm]
    rw [hT, apply_smul_T_zpow_smul h ρ⁻¹]
  · have hz : z.im ≤ 0 := not_lt.mp hz
    have hz' : (z + (N : ℝ)).im ≤ 0 := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hz' hz]

omit [NeZero N] in
theorem K_mdifferentiable (h : Hyp F χ) (ρ : SL(2, ℤ)) : MDiff (K F ρ) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => ((ρ⁻¹ • ofComplex z : ℍ) : ℂ)) ↑τ :=
    (hasDerivAt_smul_ofComplex ρ⁻¹ τ).differentiableAt
  have h2 : DifferentiableAt ℂ (fun z : ℂ => F (ofComplex z)) ((ρ⁻¹ • τ : ℍ) : ℂ) :=
    h.holo.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds (ρ⁻¹ • τ).im_pos)
  have h3 : ((ρ⁻¹ • τ : ℍ) : ℂ) = (fun z : ℂ => ((ρ⁻¹ • ofComplex z : ℍ) : ℂ)) ↑τ := by
    simp only [ofComplex_apply]
  rw [h3] at h2
  have h4 := h2.comp (↑τ : ℂ) h1
  have hfun : K F ρ ∘ ofComplex
      = (fun z : ℂ => F (ofComplex z)) ∘ (fun z : ℂ => ((ρ⁻¹ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, K, ofComplex_apply]
  rw [hfun]
  exact h4

omit [NeZero N] in
theorem K_tendsto (h : Hyp F χ) (ρ : SL(2, ℤ)) :
    ∃ M : ℂ, Tendsto (K F ρ) atImInfty (𝓝 M) := by
  obtain ⟨L, -, hL⟩ := h.cusp ρ⁻¹
  exact ⟨L, hL⟩

omit [NeZero N] in
theorem K_bounded (h : Hyp F χ) (ρ : SL(2, ℤ)) :
    IsBoundedAtImInfty (K F ρ) := by
  obtain ⟨M, hM⟩ := K_tendsto h ρ
  have := hM.isBigO_one ℝ
  exact this

noncomputable def Φ (N : ℕ) (F : ℍ → ℂ) (ρ : SL(2, ℤ)) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction (N : ℝ) (K F ρ)

theorem hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

theorem Φ_differentiableOn (h : Hyp F χ) (ρ : SL(2, ℤ)) :
    DifferentiableOn ℂ (Φ N F ρ) (ball 0 1) :=
  differentiableOn_cuspFunction_ball hNpos (K_periodic h ρ) (K_mdifferentiable h ρ)
    (K_bounded h ρ)

theorem Φ_qParam (h : Hyp F χ) (ρ : SL(2, ℤ)) (w : ℍ) :
    Φ N F ρ (𝕢 (N : ℝ) ↑w) = F (ρ⁻¹ • w) :=
  UpperHalfPlane.eq_cuspFunction w (hNpos (N := N)).ne' (K_periodic h ρ)

omit [NeZero N] in
theorem qParam_mem_ball (w : ℍ) : 𝕢 (N : ℝ) ↑w ∈ ball (0 : ℂ) 1 ∨ (N : ℝ) ≤ 0 := by
  by_cases hN : (0 : ℝ) < N
  · left
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑w := w.2
    calc Real.exp (-2 * π * Complex.im ↑w / N) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hN
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero
  · right; exact not_lt.mp hN

theorem qParam_mem_ball' (w : ℍ) : 𝕢 (N : ℝ) ↑w ∈ ball (0 : ℂ) 1 := by
  rcases qParam_mem_ball (N := N) w with h | h
  · exact h
  · exact absurd hNpos (not_lt.mpr h)

theorem qParam_mem_closedBall {w : ℍ} (hw : 1 / 2 ≤ w.im) :
    𝕢 (N : ℝ) ↑w ∈ closedBall (0 : ℂ) (Real.exp (-π / N)) := by
  rw [mem_closedBall_zero_iff, Function.Periodic.norm_qParam, Real.exp_le_exp, UpperHalfPlane.coe_im]
  rw [div_le_div_iff_of_pos_right hNpos]
  nlinarith [Real.pi_pos]

theorem F_const (h : Hyp F χ) : ∃ c : ℂ, ∀ z : ℍ, F z = c := by
  classical
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  set r : ℝ := Real.exp (-π / N) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hNpos

  have hmax : ∀ j : SL(2, ℤ) ⧸ Γ, ∃ q ∈ closedBall (0 : ℂ) r,
      IsMaxOn (norm ∘ Φ N F j.out) (closedBall (0 : ℂ) r) q := fun j =>
    (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn (nonempty_closedBall.mpr hr0)
      (((Φ_differentiableOn h j.out).continuousOn.mono (closedBall_subset_ball hr1)).norm)
  choose q hq hqmax using hmax
  set m : SL(2, ℤ) ⧸ Γ → ℝ := fun j => ‖Φ N F j.out (q j)‖ with hm
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ m ⟨(1 : SL(2, ℤ)), Finset.mem_univ _⟩
  set B : ℝ := m j₀ with hB

  have hbound : ∀ z : ℍ, ‖F z‖ ≤ B := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_one_half_le_im_smul z
    obtain ⟨g0, hg0⟩ := QuotientGroup.mk_out_eq_mul Γ g
    set j : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk g with hj
    have h1 : ‖F z‖ = ‖Φ N F j.out (𝕢 (N : ℝ) ↑(g • z))‖ := by
      rw [Φ_qParam h, hg0, mul_inv_rev, mul_smul, inv_smul_smul]
      exact (norm_apply_smul h (inv_mem g0.2) z).symm
    rw [h1]
    exact (hqmax j (qParam_mem_closedBall hg)).trans (hj₀ j (Finset.mem_univ _))

  set ρ₀ : SL(2, ℤ) := j₀.out with hρ₀
  have hΦd : DifferentiableOn ℂ (Φ N F ρ₀) (ball 0 1) := Φ_differentiableOn h ρ₀
  have hnonzero : ∀ p ∈ ball (0 : ℂ) 1, p ≠ 0 → ‖Φ N F ρ₀ p‖ ≤ B := by
    intro p hp hp0
    have him : 0 < (Function.Periodic.invQParam (N : ℝ) p).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one hNpos (mem_ball_zero_iff.mp hp) hp0
    have : Φ N F ρ₀ p = F (ρ₀⁻¹ • ⟨_, him⟩) := by
      rw [Φ, UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hp0,
        Function.comp_apply, K, ofComplex_apply_of_im_pos him]
    rw [this]
    exact hbound _
  have hall : ∀ p ∈ ball (0 : ℂ) 1, ‖Φ N F ρ₀ p‖ ≤ B := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · have hcont : ContinuousAt (Φ N F ρ₀) 0 :=
        (hΦd.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
      have ht : Tendsto (fun p => ‖Φ N F ρ₀ p‖) (𝓝[≠] 0) (𝓝 ‖Φ N F ρ₀ 0‖) :=
        (hcont.tendsto.mono_left nhdsWithin_le_nhds).norm
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with p hp0 hp1
      exact hnonzero p hp1 hp0
    · exact hnonzero p hp hp0
  have hq₀ball : q j₀ ∈ ball (0 : ℂ) 1 := closedBall_subset_ball hr1 (hq j₀)
  have hismax : IsMaxOn (norm ∘ Φ N F ρ₀) (ball 0 1) (q j₀) := by
    intro p hp
    exact hall p hp
  have hconst := Complex.eq_const_of_exists_max hΦd hq₀ball hismax

  refine ⟨Φ N F ρ₀ (q j₀), fun z => ?_⟩
  have h1 : F z = Φ N F ρ₀ (𝕢 (N : ℝ) ↑(ρ₀ • z)) := by
    rw [Φ_qParam h, inv_smul_smul]
  rw [h1]
  exact hconst (qParam_mem_ball' _)

end Main

end ModularCurve.UnitaryAutomorphicUnit

open UpperHalfPlane in
open scoped MatrixGroups Topology in
theorem solution
    {N : ℕ} [NeZero N] (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hF : DifferentiableOn ℂ (fun z : ℂ => F (ofComplex z)) {z : ℂ | 0 < z.im})
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ C : ℂ, ∀ τ : ℍ, F τ = C :=
  ModularCurve.UnitaryAutomorphicUnit.F_const ⟨hF, hχ, hunit, hcusp⟩

end S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one
end P2MW
export P2MW.S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one (solution)
