-- Prove2me | solution 1 for HryniewiczCriterion.gaussLinkingIntegral_ne_zero_of_transverse_disk
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T19:15:15.680134+00:00
-- url     : https://prove2.me/submissions/4c1d1e18-c7ae-47db-a5ad-53db0f85760a

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_small_transverse_loop
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_disk_eq_sum_small_loops
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_circle_immersion
import Theorems.Thm_HryniewiczCriterion_finite_transverse_disk_crossings

open HryniewiczCriterion
open MeasureTheory Set Filter Topology

/-!
# Reduction of `gaussLinkingIntegral_ne_zero_of_transverse_disk`

Pole off the disk and the knot; finitely many interior crossings; the boundary loop is a
`k`-fold circle (`k ≠ 0`); residue formula; each crossing contributes `sign σ`.
-/


noncomputable section

namespace HryniewiczCriterion

lemma td_hyperplane_null : volume {p : R4 | p 3 = 0} = 0 := by
  let S : Submodule ℝ R4 := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3)
  have hS : (S : Set R4) = {p : R4 | p 3 = 0} := by
    ext p; simp [S]
  rw [← hS]
  refine Measure.addHaar_submodule volume S ?_
  intro htop
  have h : (Pi.single 3 1 : R4) ∈ S := htop ▸ Submodule.mem_top
  simp [S] at h

lemma td_dot4_self_nonneg (u : R4) : 0 ≤ dot4 u u := by
  simp only [dot4, Fin.sum_univ_four]
  nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1), mul_self_nonneg (u 2),
    mul_self_nonneg (u 3)]

lemma td_dot4_self_pos {u : R4} (hu : u ≠ 0) : 0 < dot4 u u := by
  rcases (td_dot4_self_nonneg u).lt_or_eq with h | h
  · exact h
  · exfalso; apply hu
    have h0 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 0 := by
      have := h.symm; simp only [dot4, Fin.sum_univ_four] at this; nlinarith
    funext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2),
      sq_nonneg (u 3)]

lemma td_euclidNorm_pos {u : R4} (hu : u ≠ 0) : 0 < euclidNorm u :=
  Real.sqrt_pos.2 (td_dot4_self_pos hu)

lemma td_euclidNorm_smul (c : ℝ) (v : R4) : euclidNorm (c • v) = |c| * euclidNorm v := by
  have h : dot4 (c • v) (c • v) = c ^ 2 * dot4 v v := by
    simp only [dot4, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring
  rw [euclidNorm, euclidNorm, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The cone `{c • f v : v ∈ U}` over a surface differentiable on `U` is null. -/
lemma td_cone_null (f : Plane → R4) (U : Set Plane) (hf : DifferentiableOn ℝ f U) :
    volume {M : R4 | ∃ (c : ℝ), ∃ v ∈ U, M = c • f v} = 0 := by
  set F : R4 → R4 := fun p => p 2 • f ![p 0, p 1]
  set S : Set R4 := {p : R4 | p 3 = 0 ∧ (![p 0, p 1] : Plane) ∈ U}
  have hsub : {M : R4 | ∃ (c : ℝ), ∃ v ∈ U, M = c • f v} ⊆ F '' S := by
    rintro M ⟨c, v, hv, rfl⟩
    have hv' : (![v 0, v 1] : Plane) = v := by ext i; fin_cases i <;> rfl
    refine ⟨![v 0, v 1, c, 0], ⟨by simp, by simpa using hv'.symm ▸ hv⟩, ?_⟩
    simp [F, hv']
  have hl : Differentiable ℝ (fun p : R4 => (![p 0, p 1] : Plane)) := by
    rw [differentiable_pi]; intro i; fin_cases i <;> simp <;> fun_prop
  have hF : DifferentiableOn ℝ F S := by
    intro p hp
    have h1 : DifferentiableWithinAt ℝ (fun p : R4 => f ![p 0, p 1]) S p :=
      (hf _ hp.2).comp p (hl p).differentiableWithinAt (fun q hq => hq.2)
    exact (differentiableAt_apply 2 p).differentiableWithinAt.smul h1
  have hS : volume S = 0 := measure_mono_null (fun p hp => hp.1) td_hyperplane_null
  exact measure_mono_null hsub (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF hS)

/-- A unit pole missing the unit points of `f(U)` and a loop. -/
theorem td_exists_pole (f : Plane → R4) (U : Set Plane) (hf : DifferentiableOn ℝ f U)
    (g : ℝ → R4) (hg : Differentiable ℝ g) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ v ∈ U, euclidNorm (f v) = 1 → f v ≠ N) ∧
      ∀ s, euclidNorm (g s) = 1 → g s ≠ N := by
  set g' : Plane → R4 := fun v => g (v 0)
  have hg' : DifferentiableOn ℝ g' univ := fun v _ =>
    ((hg (v 0)).comp v (differentiableAt_apply 0 v)).differentiableWithinAt
  set bad := {M : R4 | ∃ (c : ℝ), ∃ v ∈ U, M = c • f v} ∪
    {M : R4 | ∃ (c : ℝ), ∃ v ∈ (univ : Set Plane), M = c • g' v}
  have hU : volume bad = 0 :=
    measure_union_null (td_cone_null f U hf) (td_cone_null g' univ hg')
  have hne : (badᶜ).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hpos := isOpen_univ.measure_pos (volume : Measure R4) univ_nonempty
    rw [← hemp, hU] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨M, hM⟩ := hne
  have hM1 : ∀ (c : ℝ), ∀ v ∈ U, M ≠ c • f v := fun c v hv he => hM (Or.inl ⟨c, v, hv, he⟩)
  have hM2 : ∀ (c : ℝ) s, M ≠ c • g s := fun c s he =>
    hM (Or.inr ⟨c, fun _ => s, mem_univ _, by simpa [g'] using he⟩)
  have hM0 : M ≠ 0 := fun h0 => hM2 0 0 (by simp [h0])
  have hp := td_euclidNorm_pos hM0
  have hMN : M = euclidNorm M • ((euclidNorm M)⁻¹ • M) := by
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  refine ⟨(euclidNorm M)⁻¹ • M, ?_, ?_, ?_⟩
  · rw [td_euclidNorm_smul, abs_inv, abs_of_pos hp, inv_mul_cancel₀ hp.ne']
  · intro v hv _ he
    exact hM1 (euclidNorm M) v hv (he ▸ hMN)
  · intro s _ he
    exact hM2 (euclidNorm M) s (he ▸ hMN)

lemma td_sign (σ d : ℝ) (h : 0 < σ * d) :
    (if 0 < d then (1 : ℝ) else -1) = if 0 < σ then 1 else -1 := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · simp [not_lt.2 h1.le, not_lt.2 h2.le]

theorem gaussLinkingIntegral_ne_zero_of_transverse_disk' (E : Plane → R4) (U : Set Plane)
    (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hbd : ∀ s t, E (u s) ≠ γ t) (σ : ℝ)
    (htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      0 < σ * Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]))
    (hcross : ∃ t, ∃ v ∈ closedUnitDisk, E v = γ t) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ s, E (u s) ≠ N ∧ γ s ≠ N) ∧
      ∃ n : ℤ, n ≠ 0 ∧ gaussLinkingIntegral N (fun s => E (u s)) γ = n := by
  have hE1 : ContDiffOn ℝ 1 E U := hE.of_le (by norm_num)
  have hEd : DifferentiableOn ℝ E U := hE.differentiableOn (by norm_num)
  have hγd : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  obtain ⟨N, hN, hNE', hNγ'⟩ := td_exists_pole E U hEd γ hγd
  have hNγ : ∀ t, γ t ≠ N := fun t => hNγ' t (hγunit t)
  have hNE : ∀ v ∈ closedUnitDisk, E v ≠ N := fun v hv => hNE' v (hDU hv) (hEunit v hv)
  have hCD : unitCircle ⊆ closedUnitDisk := fun w (hw : w 0 ^ 2 + w 1 ^ 2 = 1) =>
    show w 0 ^ 2 + w 1 ^ 2 ≤ 1 from le_of_eq hw
  have hucD : ∀ s, u s ∈ closedUnitDisk := fun s => hCD (hucirc s)
  obtain ⟨hsurj, k, hk, hGk⟩ := gaussLinkingIntegral_circle_immersion E U hU
    (hCD.trans hDU) hE (fun v hv => hEunit v (hCD hv)) u hu huper hucirc hu' γ hγ hγper hγunit
    hbd N hN hNγ (fun s => hNE _ (hucD s))
  have hfin := finite_transverse_disk_crossings E U hU hDU hE1 γ (hγ.of_le (by norm_num)) hγper
    (fun t v hv he h0 => by
      have := htr t v hv he; rw [h0, mul_zero] at this; exact lt_irrefl _ this)
  set Z := hfin.toFinset with hZdef
  have hmemZ : ∀ v, v ∈ Z ↔ v ∈ closedUnitDisk ∧ ∃ t, E v = γ t := fun v => hfin.mem_toFinset
  have hZopen : ∀ z ∈ Z, z ∈ openUnitDisk := by
    intro z hz
    obtain ⟨hzD, t, ht⟩ := (hmemZ z).1 hz
    rcases lt_or_eq_of_le (show z 0 ^ 2 + z 1 ^ 2 ≤ 1 from hzD) with h | h
    · exact h
    · obtain ⟨s, hs⟩ := hsurj z h
      exact absurd (hs ▸ ht) (hbd s t)
  have hmiss : ∀ v ∈ closedUnitDisk, v ∉ Z → ∀ t, E v ≠ γ t :=
    fun v hv hvZ t he => hvZ ((hmemZ v).2 ⟨hv, t, he⟩)
  obtain ⟨ρB, hρB, hB⟩ := gaussLinkingIntegral_disk_eq_sum_small_loops E U hU hDU hE hEunit
    γ hγ hγper hγunit Z hZopen hmiss N hN hNγ hNE
  have hev : ∀ z ∈ Z, ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ =
        if 0 < σ then 1 else -1 := by
    intro z hz
    obtain ⟨hzD, t₀, ht₀⟩ := (hmemZ z).1 hz
    have hopen : IsOpen (openUnitDisk ∩ ((Z.erase z : Finset Plane) : Set Plane)ᶜ) :=
      (isOpen_lt (by fun_prop) continuous_const : IsOpen openUnitDisk).inter (Z.erase z).finite_toSet.isClosed.isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen z
      ⟨hZopen z hz, by simp⟩
    have hballD : ∀ v ∈ Metric.ball z r, v ∈ closedUnitDisk :=
      fun v hv => show v 0 ^ 2 + v 1 ^ 2 ≤ 1 from le_of_lt (hball hv).1
    have hdet0 := htr t₀ z hzD ht₀
    have hdne : Matrix.det (Matrix.of ![γ t₀, deriv γ t₀,
        fderiv ℝ E z (Pi.single 0 1), fderiv ℝ E z (Pi.single 1 1)]) ≠ 0 := fun h => by
      rw [h, mul_zero] at hdet0; exact lt_irrefl _ hdet0
    obtain ⟨ρA, hρA, hA⟩ := gaussLinkingIntegral_small_transverse_loop E z r hr
      (hE.mono fun v hv => hDU (hballD v hv)) (fun v hv => hEunit v (hballD v hv))
      γ hγ hγper hγunit hγinj t₀ ht₀
      (fun v hv hvz t he => (hball hv).2
        (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvz, (hmemZ v).2 ⟨hballD v hv, t, he⟩⟩)))
      hdne N hN hNγ (fun v hv => hNE v (hballD v hv))
    filter_upwards [Ioo_mem_nhdsGT hρA] with ρ hρ
    rw [hA ρ hρ.1 hρ.2]
    exact td_sign σ _ hdet0
  have hall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 ρB ∧ ∀ z ∈ Z,
      gaussLinkingIntegral N (fun s => E (z + ρ • circlePoint s)) γ =
        if 0 < σ then 1 else -1 :=
    Filter.Eventually.and (Ioo_mem_nhdsGT hρB) ((eventually_all_finset Z).2 hev)
  obtain ⟨ρ, hρ, hρZ⟩ := hall.exists
  have hZne : Z.Nonempty := by
    obtain ⟨t, v, hv, he⟩ := hcross
    exact ⟨v, (hmemZ v).2 ⟨hv, t, he⟩⟩
  refine ⟨N, hN, fun s => ⟨hNE _ (hucD s), hNγ s⟩,
    k * Z.card * (if 0 < σ then 1 else -1), ?_, ?_⟩
  · have hc : (Z.card : ℤ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hZne).ne'
    refine mul_ne_zero (mul_ne_zero hk hc) ?_
    split_ifs <;> norm_num
  · rw [hGk, hB ρ hρ.1 hρ.2, Finset.sum_congr rfl hρZ, Finset.sum_const, nsmul_eq_mul]
    push_cast
    split_ifs <;> ring

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 2 E U) (hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1)
    (u : ℝ → Plane) (hu : ContDiff ℝ 2 u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (hu' : ∀ s, deriv u s ≠ 0)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 2 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hγunit : ∀ t, euclidNorm (γ t) = 1) (hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n)
    (hbd : ∀ s t, E (u s) ≠ γ t) (σ : ℝ)
    (htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      0 < σ * Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]))
    (hcross : ∃ t, ∃ v ∈ closedUnitDisk, E v = γ t) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ s, E (u s) ≠ N ∧ γ s ≠ N) ∧
      ∃ n : ℤ, n ≠ 0 ∧ gaussLinkingIntegral N (fun s => E (u s)) γ = n :=
  HryniewiczCriterion.gaussLinkingIntegral_ne_zero_of_transverse_disk' E U hU hDU hE hEunit u hu huper hucirc hu' γ hγ hγper hγunit hγinj hbd σ htr hcross
