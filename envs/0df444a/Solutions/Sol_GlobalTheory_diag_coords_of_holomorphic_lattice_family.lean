-- Prove2me | solution 1 for GlobalTheory.diag_coords_of_holomorphic_lattice_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:31.810981+00:00
-- url     : https://prove2.me/submissions/0cb1c3f0-3e1c-487b-9315-e008a76e0598

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeRealCoordinateBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoordinateProjectionComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAntilinearNormalFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDeformationMultiplication
import Theorems.Thm_GlobalTheory_T_exists_antilinear_normal_form
import Theorems.Thm_GlobalTheory_T_exists_coordinate_projection_complex
import Theorems.Thm_GlobalTheory_T_lattice_real_coordinate_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
  intro Ω _ _ g K ρ hreal hsep Λ hd hs hΛ V τ hV h0 hτ0 hτd hM
  obtain ⟨ρr, hρ⟩ : ∃ ρr : K → Fin g → ℝ, ∀ a j, ((ρr a j : ℝ) : ℂ) = ρ a j :=
    ⟨fun a j ↦ (ρ a j).re, fun a j ↦ Complex.conj_eq_iff_re.mp (hreal a j)⟩
  have hsepr : ∀ j k, j ≠ k → ∃ a, ρr a j ≠ ρr a k := by
    intro j k hjk
    obtain ⟨a, ha⟩ := hsep j k hjk
    exact ⟨a, fun h ↦ ha (by rw [← hρ, ← hρ, h])⟩
  obtain ⟨n, b, c, hbc, hφ⟩ := GlobalTheory.T.lattice_real_coordinate_basis g Λ hd hs
  obtain ⟨T, hTapp⟩ : ∃ T : Ω → (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ),
      ∀ z v, T z v = ∑ i, c i v • τ z (b i) :=
    ⟨fun z ↦ ∑ i, (c i).smulRight (τ z (b i)), fun z v ↦ by simp⟩
  have hTΛ : ∀ z (x : Λ), T z x = τ z x := fun z x ↦ by rw [hTapp]; exact hφ (τ z) x
  have hT0 : ∀ v, T 0 v = v := fun v ↦ by rw [hTapp]; simp only [hτ0]; exact hbc v
  have hTd : ∀ v, DifferentiableOn ℂ (fun z ↦ T z v) V := by
    intro v
    simp only [hTapp]
    have := DifferentiableOn.sum (u := Finset.univ) (A := fun i z ↦ c i v • τ z (b i))
      (fun i _ ↦ (hτd (b i)).const_smul (c i v))
    simpa [Finset.sum_fn] using this
  have hcomm : ∀ z a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
      ∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v) := by
    intro z a M hMz
    let Dg : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      { toFun := fun v m ↦ ρ a m * v m
        map_add' := by intro v w; ext m; simp [mul_add]
        map_smul' := by intro r v; ext m; simp; ring }
    have key := LinearMap.ext_on (f := (T z).comp Dg) (g := (M.restrictScalars ℝ).comp (T z)) hs (by
      intro x hx
      have hx' : (fun j ↦ ρ a j * x j) ∈ Λ := hΛ a x hx
      have e := hMz ⟨x, hx⟩ ⟨_, hx'⟩ rfl
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
      rw [← hTΛ, ← hTΛ] at e
      exact e)
    intro v
    have := LinearMap.congr_fun key v
    simpa [Dg, hρ] using this
  obtain ⟨α, hα⟩ : ∃ α : Ω → Fin g → ℂ, ∀ z j,
      α z j = (T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) / 2 := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Ω → Fin g → ℂ, ∀ z j,
      β z j = (T z (Pi.single j 1) j + Complex.I * T z (Pi.single j Complex.I) j) / 2 := ⟨_, fun _ _ ↦ rfl⟩
  have hTs : ∀ z j (y : ℂ), T z (Pi.single j y) j = α z j * y + β z j * starRingEnd ℂ y := by
    intro z j y
    have hy : (Pi.single j y : Fin g → ℂ) = y.re • (Pi.single j 1 : Fin g → ℂ) + y.im • (Pi.single j Complex.I : Fin g → ℂ) := by
      ext m
      rcases eq_or_ne m j with rfl | h
      · simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
        exact (Complex.re_add_im y).symm
      · simp [h]
    rw [hy, map_add, map_smul, map_smul, hα, hβ]
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    have hc : starRingEnd ℂ y = (y.re : ℂ) - (y.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hc]
    have hy2 : y = (y.re : ℂ) + (y.im : ℂ) * Complex.I := (Complex.re_add_im y).symm
    linear_combination (-(T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) / 2) * hy2
      + ((y.im : ℂ) * T z (Pi.single j Complex.I) j) * Complex.I_sq
  have hα0 : ∀ j, α 0 j = 1 := by
    intro j; rw [hα, hT0, hT0]; simp [Complex.I_mul_I]
  have hβ0 : ∀ j, β 0 j = 0 := by
    intro j; rw [hβ, hT0, hT0]; simp [Complex.I_mul_I]
  have hαd : ∀ j, DifferentiableOn ℂ (fun z ↦ α z j) V := by
    intro j; simp only [hα]
    have h3 : DifferentiableOn ℂ (fun z ↦ T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) V :=
      (differentiableOn_pi.1 (hTd _) j).sub ((differentiableOn_pi.1 (hTd _) j).const_mul Complex.I)
    simpa [div_eq_mul_inv] using h3.mul_const (2 : ℂ)⁻¹
  have hβd : ∀ j, DifferentiableOn ℂ (fun z ↦ β z j) V := by
    intro j; simp only [hβ]
    have h3 : DifferentiableOn ℂ (fun z ↦ T z (Pi.single j 1) j + Complex.I * T z (Pi.single j Complex.I) j) V :=
      (differentiableOn_pi.1 (hTd _) j).add ((differentiableOn_pi.1 (hTd _) j).const_mul Complex.I)
    simpa [div_eq_mul_inv] using h3.mul_const (2 : ℂ)⁻¹
  set V' : Set Ω := V ∩ ⋂ j, (V ∩ (fun z ↦ ‖α z j‖ - ‖β z j‖) ⁻¹' Set.Ioi 0) with hV'
  have hV'o : IsOpen V' := by
    refine hV.inter (isOpen_iInter_of_finite fun j ↦ ContinuousOn.isOpen_inter_preimage ?_ hV isOpen_Ioi)
    exact ((hαd j).continuousOn.norm).sub (hβd j).continuousOn.norm
  have hV'm : ∀ z ∈ V', z ∈ V ∧ ∀ j, ‖β z j‖ < ‖α z j‖ := by
    intro z hz
    simp only [hV', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos] at hz
    exact ⟨hz.1, fun j ↦ (hz.2 j).2⟩
  have h0' : (0 : Ω) ∈ V' := by
    simp only [hV', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos, hα0, hβ0]
    simp [h0]
  have hαne : ∀ z ∈ V', ∀ j, α z j ≠ 0 := fun z hz j ↦
    norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) ((hV'm z hz).2 j))
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω → Fin g → ℂ, ∀ z j, ζ z j = β z j / α z j := ⟨_, fun _ _ ↦ rfl⟩
  have hζd : DifferentiableOn ℂ ζ V' := by
    refine differentiableOn_pi.2 fun j ↦ ?_
    simp only [hζ]
    have hsub : V' ⊆ V := fun z hz ↦ (hV'm z hz).1
    simp only [div_eq_mul_inv]
    exact ((hβd j).mono hsub).mul (((hαd j).mono hsub).inv fun z hz ↦ hαne z hz j)
  have hpt : ∀ z ∈ V', ∃ Dz : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, Dz (T z v) = fun j ↦ v j + β z j / α z j * starRingEnd ℂ (v j)) ∧
      ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v)) →
        ∀ w, Dz (M w) = fun j ↦ (ρr a j : ℂ) * Dz w j := by
    intro z hz
    have hMex : ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
        ∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v) := fun a ↦ by
      obtain ⟨M, hMz⟩ := hM z (hV'm z hz).1 a
      exact ⟨M, hcomm z a M hMz⟩
    obtain ⟨Dz, h1, h2⟩ := GlobalTheory.T.exists_antilinear_normal_form g (T z) (GlobalTheory.T.exists_coordinate_projection_complex g K ρr hsepr (T z) hMex) (α z) (β z) (hV'm z hz).2 (hTs z)
    exact ⟨Dz, h1, fun a M hMa w ↦ h2 (ρr a) M hMa w⟩
  classical
  let D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := fun z ↦
    if hz : z ∈ V' then Classical.choose (hpt z hz) else LinearEquiv.refl ℂ _
  refine ⟨V', D, ζ, hV'o, h0', fun z hz ↦ (hV'm z hz).1, hζd, ?_, ?_, ?_, ?_⟩
  · funext j; rw [hζ, hβ0]; simp
  · intro z hz j
    rw [hζ, norm_div, div_lt_one (norm_pos_iff.mpr (hαne z hz j))]
    exact (hV'm z hz).2 j
  · intro z hz x
    have := (Classical.choose_spec (hpt z hz)).1 x
    simp only [D, dif_pos hz]
    rw [← hTΛ, this]
    funext j; rw [hζ]
  · intro z hz a M hMz w
    have := (Classical.choose_spec (hpt z hz)).2 a M (hcomm z a M hMz) w
    simp only [D, dif_pos hz]
    rw [this]; simp only [hρ]
end GlobalTheory
