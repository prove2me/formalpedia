-- Prove2me | solution 1 for ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c7111919-2310-5d70-b0d2-d5c79d89f1b7

import Mathlib
import Theorems.Thm_UpperHalfPlane_denom_eq_of_smul_eq_self
import Theorems.Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
import Theorems.Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem
import Theorems.Thm_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
import Theorems.Thm_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

namespace T3aAux

theorem smul_pow_of_fix {Γ : Subgroup (GL (Fin 2) ℝ)} (τ₀ : ℍ)
    (γ : ↥Γ) (hγ : (γ : GL (Fin 2) ℝ) • τ₀ = τ₀) (m : ℕ) : ((γ ^ m : ↥Γ) : GL (Fin 2) ℝ) • τ₀ = τ₀ := by
  induction m with
  | zero => simp
  | succ j ih => rw [pow_succ, Subgroup.coe_mul, mul_smul, hγ, ih]

theorem denom_pow_of_fix {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (τ₀ : ℍ)
    (γ : ↥Γ) (hγ : (γ : GL (Fin 2) ℝ) • τ₀ = τ₀) (m : ℕ) :
    denom (((γ ^ m : ↥Γ)) : GL (Fin 2) ℝ) τ₀ = (denom (γ : GL (Fin 2) ℝ) τ₀) ^ m := by
  induction m with
  | zero => simp [denom]
  | succ m ih =>
    have h5 := (UpperHalfPlane.denom_eq_of_smul_eq_self ((γ ^ m : ↥Γ) : GL (Fin 2) ℝ) (hdet _ (γ ^ m).2) τ₀
      (smul_pow_of_fix τ₀ γ hγ m)).2.2.2.2 (γ : GL (Fin 2) ℝ) (hdet _ γ.2) hγ
    rw [pow_succ, Subgroup.coe_mul, h5, ih, pow_succ]

theorem denom_pow_card_stabilizer {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (τ₀ : ℍ)
    (γ : ↥Γ) (hγ : γ ∈ MulAction.stabilizer ↥Γ τ₀) :
    (denom (γ : GL (Fin 2) ℝ) τ₀) ^ Nat.card ↥(MulAction.stabilizer ↥Γ τ₀) = 1 := by
  have hγ' : (γ : GL (Fin 2) ℝ) • τ₀ = τ₀ := MulAction.mem_stabilizer_iff.1 hγ
  rw [← denom_pow_of_fix hdet τ₀ γ hγ']
  have h1 : (⟨γ, hγ⟩ : ↥(MulAction.stabilizer ↥Γ τ₀)) ^ Nat.card ↥(MulAction.stabilizer ↥Γ τ₀) = 1 := pow_card_eq_one'
  have h2 : γ ^ Nat.card ↥(MulAction.stabilizer ↥Γ τ₀) = 1 := by
    have := congrArg (fun x : ↥(MulAction.stabilizer ↥Γ τ₀) => (x : ↥Γ)) h1
    simpa using this
  rw [h2]
  simp [denom]

theorem sub_conj_ne_zero (σ τ₀ : ℍ) : (σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.sub_im, Complex.zero_im] at this
  have h2 : ((starRingEnd ℂ) (τ₀ : ℂ)).im = -τ₀.im := by
    rw [← UpperHalfPlane.coe_im]; exact Complex.conj_im _
  rw [h2, UpperHalfPlane.coe_im] at this
  linarith [σ.im_pos, τ₀.im_pos]

theorem stab_term_eq {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (τ₀ : ℍ) (n : ℕ) (k : ℤ)
    (hdiv : (Nat.card ↥(MulAction.stabilizer ↥Γ τ₀) : ℤ) ∣ 2 * (n : ℤ) + k) (σ : ℍ)
    (γ : ↥Γ) (hγ : (γ : GL (Fin 2) ℝ) • τ₀ = τ₀) :
    (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)
    = (((σ : ℂ) - (τ₀ : ℂ)) / ((σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n * ((σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) := by
  obtain ⟨hn1, h2, h3, -, -⟩ := UpperHalfPlane.denom_eq_of_smul_eq_self (γ : GL (Fin 2) ℝ) (hdet _ γ.2) τ₀ hγ
  set E : ℂ := denom (γ : GL (Fin 2) ℝ) τ₀ with hE
  have hE0 : E ≠ 0 := by intro h; rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  set A : ℂ := (((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ) with hA
  set B : ℂ := (((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) with hB
  set D : ℂ := denom (γ : GL (Fin 2) ℝ) σ with hD
  set x : ℂ := (σ : ℂ) - (τ₀ : ℂ) with hx
  set y : ℂ := (σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ) with hy
  have hD0 : D ≠ 0 := denom_ne_zero _ σ
  have hy0 : y ≠ 0 := sub_conj_ne_zero σ τ₀
  have h2' : B * D = y * E := h2 σ
  have h3' : A * D * E = x := h3 σ
  have hA' : A = x / (D * E) := by rw [eq_div_iff (mul_ne_zero hD0 hE0), ← h3']; ring
  have hB' : B = y * E / D := by rw [eq_div_iff hD0, h2']
  have hEpow : E ^ (2 * (n : ℤ) + k) = 1 := by
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, zpow_mul, zpow_natCast, hE, denom_pow_card_stabilizer hdet τ₀ γ (MulAction.mem_stabilizer_iff.2 ?_), one_zpow]
    exact hγ
  have hAB : A / B = x / y * (E ^ 2)⁻¹ := by
    rw [hA', hB']; field_simp
  have hBD : B ^ (-k) * D ^ (-k) = y ^ (-k) * E ^ (-k) := by
    rw [← mul_zpow, ← mul_zpow, h2']
  have hEE : (E ^ 2)⁻¹ ^ n * E ^ (-k) = 1 := by
    rw [inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hE0]
    have : -((2 * n : ℕ) : ℤ) + -k = -(2 * (n : ℤ) + k) := by push_cast; ring
    rw [this, zpow_neg, hEpow, inv_one]
  calc (A / B) ^ n * B ^ (-k) * D ^ (-k) = (A / B) ^ n * (B ^ (-k) * D ^ (-k)) := by ring
    _ = (x / y * (E ^ 2)⁻¹) ^ n * (y ^ (-k) * E ^ (-k)) := by rw [hAB, hBD]
    _ = (x / y) ^ n * y ^ (-k) * ((E ^ 2)⁻¹ ^ n * E ^ (-k)) := by rw [mul_pow]; ring
    _ = (x / y) ^ n * y ^ (-k) := by rw [hEE, mul_one]

theorem stab_sum {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) [hdisc : DiscreteTopology ↥Γ]
    (τ₀ : ℍ) (n : ℕ) (k : ℤ)
    (hdiv : (Nat.card ↥(MulAction.stabilizer ↥Γ τ₀) : ℤ) ∣ 2 * (n : ℤ) + k) (σ : ℍ) :
    ∑' γ : ↥Γ, Set.indicator {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • τ₀ = τ₀} (fun γ : ↥Γ =>
      (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)) γ
    = (Nat.card ↥(MulAction.stabilizer ↥Γ τ₀) : ℂ) *
      ((((σ : ℂ) - (τ₀ : ℂ)) / ((σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n * ((σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k)) := by
  classical
  haveI hfin : Finite ↥(MulAction.stabilizer ↥Γ τ₀) :=
    (UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet τ₀).1
  set S : Set ↥Γ := {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • τ₀ = τ₀} with hS
  have hSeq : S = (MulAction.stabilizer ↥Γ τ₀ : Set ↥Γ) := by
    ext γ
    rw [hS, Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have hSfin : S.Finite := by rw [hSeq]; exact Set.toFinite _
  set φ : ℂ := (((σ : ℂ) - (τ₀ : ℂ)) / ((σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((σ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) with hφ
  have hterm : ∀ γ ∈ S, (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k) = φ :=
    fun γ hγ => by rw [hφ]; exact stab_term_eq hdet τ₀ n k hdiv σ γ hγ
  have hsupp : Function.support (Set.indicator S (fun γ : ↥Γ =>
      (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k))) ⊆ ↑hSfin.toFinset := by
    intro γ hγ
    rw [Function.mem_support] at hγ
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hγ (Set.indicator_of_notMem h _)
  rw [tsum_eq_sum' hsupp]
  have hsum : ∑ γ ∈ hSfin.toFinset, Set.indicator S (fun γ : ↥Γ =>
      (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
      ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)) γ = ∑ γ ∈ hSfin.toFinset, φ := by
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    rw [Set.Finite.mem_toFinset] at hγ
    rw [Set.indicator_of_mem hγ, hterm γ hγ]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Set.ncard_eq_toFinset_card S hSfin, ← Nat.card_coe_set_eq, hSeq]
  rfl

end T3aAux

namespace T3aAux

theorem norm_sub_conj (τ : ℍ) : ‖(τ : ℂ) - (starRingEnd ℂ) (τ : ℂ)‖ = 2 * τ.im := by
  have : (τ : ℂ) - (starRingEnd ℂ) (τ : ℂ) = (2 * τ.im : ℝ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re]
    · rw [Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im]; simp; ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith [τ.im_pos])]

theorem sqrt_im_mul_self (τ : ℍ) : Real.sqrt (τ.im * τ.im) = τ.im := Real.sqrt_mul_self τ.im_pos.le

theorem eventually_small {A ϑ : ℝ} (hA : 0 ≤ A) (h0 : 0 ≤ ϑ) (h1 : ϑ < 1) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → A * ϑ ^ m < 1 / 2 := by
  have ht : Filter.Tendsto (fun m : ℕ => A * ϑ ^ m) Filter.atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul A
    simpa using this
  have hev := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, hN⟩

theorem partA {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (hneg : -1 ∈ Γ) [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) (τ σ : ℍ) (hne : ∀ γ ∈ Γ, γ • τ ≠ σ) :
    ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ := by
  classical

  haveI hfinτ : Finite ↥(MulAction.stabilizer ↥Γ τ) := (UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet τ).1
  haveI hfinσ : Finite ↥(MulAction.stabilizer ↥Γ σ) := (UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet σ).1
  set eτ : ℕ := Nat.card ↥(MulAction.stabilizer ↥Γ τ) with heτ
  set eσ : ℕ := Nat.card ↥(MulAction.stabilizer ↥Γ σ) with heσ
  have heτpos : 0 < eτ := Nat.card_pos
  have heσpos : 0 < eσ := Nat.card_pos
  have heτ2 : 2 ∣ eτ := UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem Γ hdet hneg τ

  obtain ⟨U₁, hU₁o, hτU₁, A₁, ϑ₁, hA₁, hϑ₁0, hϑ₁1, H₁⟩ :=
    ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology Γ hdet hcusp τ τ
  obtain ⟨U₂, hU₂o, hσU₂, A₂, ϑ₂, hA₂, hϑ₂0, hϑ₂1, H₂⟩ :=
    ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology Γ hdet hcusp τ σ
  obtain ⟨U₃, hU₃o, hσU₃, A₃, ϑ₃, hA₃, hϑ₃0, hϑ₃1, H₃⟩ :=
    ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology Γ hdet hcusp σ σ
  obtain ⟨U₄, hU₄o, hτU₄, A₄, ϑ₄, hA₄, hϑ₄0, hϑ₄1, H₄⟩ :=
    ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology Γ hdet hcusp σ τ

  obtain ⟨N₁, hN₁⟩ := eventually_small hA₁ hϑ₁0 hϑ₁1
  obtain ⟨N₂, hN₂⟩ := eventually_small hA₂ hϑ₂0 hϑ₂1
  obtain ⟨N₃, hN₃⟩ := eventually_small hA₃ hϑ₃0 hϑ₃1
  obtain ⟨N₄, hN₄⟩ := eventually_small hA₄ hϑ₄0 hϑ₄1
  set M : ℕ := max (max (max N₁ N₂) (max N₃ N₄)) 4 with hM
  set m : ℕ := eτ * eσ * M with hm
  have hMle : M ≤ m := by
    rw [hm]; exact Nat.le_mul_of_pos_left M (Nat.mul_pos heτpos heσpos)
  have hN₁m : N₁ ≤ m := le_trans (by rw [hM]; omega) hMle
  have hN₂m : N₂ ≤ m := le_trans (by rw [hM]; omega) hMle
  have hN₃m : N₃ ≤ m := le_trans (by rw [hM]; omega) hMle
  have hN₄m : N₄ ≤ m := le_trans (by rw [hM]; omega) hMle
  have h4m : 4 ≤ m := le_trans (by rw [hM]; omega) hMle
  set k : ℤ := (m : ℤ) with hk
  have hk4 : (4 : ℤ) ≤ k := by rw [hk]; exact_mod_cast h4m
  have hkeven : Even k := by
    rw [hk, Int.even_coe_nat, hm]
    exact ((even_iff_two_dvd.2 heτ2).mul_right _).mul_right _
  have hdivτ : (eτ : ℤ) ∣ 2 * ((0 : ℕ) : ℤ) + k := by
    rw [hk, hm]; push_cast; simp only [mul_zero, zero_add]; exact ⟨(eσ : ℤ) * (M : ℤ), by ring⟩
  have hdivσ : (eσ : ℤ) ∣ 2 * ((0 : ℕ) : ℤ) + k := by
    rw [hk, hm]; push_cast; simp only [mul_zero, zero_add]; exact ⟨(eτ : ℤ) * (M : ℤ), by ring⟩

  obtain ⟨h, hhf, hhb⟩ := H₁ 0 k hk4
  obtain ⟨h₂, hh₂f, hh₂b⟩ := H₂ 0 k hk4
  obtain ⟨g, hgf, hgb⟩ := H₃ 0 k hk4
  obtain ⟨g₄, hg₄f, hg₄b⟩ := H₄ 0 k hk4
  have hh₂ : ∀ x : ℍ, h₂ x = h x := fun x => by rw [hh₂f, hhf]
  have hg₄ : ∀ x : ℍ, g₄ x = g x := fun x => by rw [hg₄f, hgf]
  refine ⟨k, hk4, hkeven, g, h, ?_⟩

  have hSτ := stab_sum hdet τ 0 k hdivτ τ
  have hSσ := stab_sum hdet σ 0 k hdivσ σ
  have hemptyσ : {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • σ = τ} = ∅ := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hγ
    apply hne (γ⁻¹ : ↥Γ) (γ⁻¹).2
    show ((γ⁻¹ : ↥Γ) : GL (Fin 2) ℝ) • τ = σ
    rw [Subgroup.coe_inv, ← hγ, inv_smul_smul]
  have hemptyτ : {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • τ = σ} = ∅ := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hne γ γ.2

  have b₁ := hhb τ hτU₁
  have b₂ := hh₂b σ hσU₂
  have b₃ := hgb σ hσU₃
  have b₄ := hg₄b τ hτU₄
  rw [hSτ] at b₁
  rw [hSσ] at b₃
  rw [hemptyσ] at b₂
  rw [hemptyτ] at b₄
  simp only [Set.indicator_empty, tsum_zero, sub_zero, pow_zero, one_mul] at b₁ b₂ b₃ b₄
  rw [hh₂] at b₂
  rw [hg₄] at b₄
  rw [sqrt_im_mul_self] at b₁ b₃

  set Nτ : ℝ := (2 * τ.im) ^ (-k) with hNτ
  set Nσ : ℝ := (2 * σ.im) ^ (-k) with hNσ
  have hNτpos : 0 < Nτ := by rw [hNτ]; exact zpow_pos (by linarith [τ.im_pos]) _
  have hNσpos : 0 < Nσ := by rw [hNσ]; exact zpow_pos (by linarith [σ.im_pos]) _
  have hcross : (2 * Real.sqrt (σ.im * τ.im)) ^ (-k) * (2 * Real.sqrt (τ.im * σ.im)) ^ (-k) = Nσ * Nτ := by
    rw [hNσ, hNτ, ← mul_zpow, ← mul_zpow]
    congr 1
    rw [mul_comm τ.im σ.im]
    have hs : Real.sqrt (σ.im * τ.im) * Real.sqrt (σ.im * τ.im) = σ.im * τ.im :=
      Real.mul_self_sqrt (by positivity)
    linear_combination (4 : ℝ) * hs
  have hnormτ : ‖((τ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖ = Nτ := by
    rw [norm_zpow, norm_sub_conj]
  have hnormσ : ‖((σ : ℂ) - (starRingEnd ℂ) (σ : ℂ)) ^ (-k)‖ = Nσ := by
    rw [norm_zpow, norm_sub_conj]

  have hk_m : ∀ (ϑ : ℝ), ϑ ^ k = ϑ ^ m := fun ϑ => by rw [hk, zpow_natCast]
  have s₁ : A₁ * ϑ₁ ^ k < 1 / 2 := by rw [hk_m]; exact hN₁ m hN₁m
  have s₂ : A₂ * ϑ₂ ^ k < 1 / 2 := by rw [hk_m]; exact hN₂ m hN₂m
  have s₃ : A₃ * ϑ₃ ^ k < 1 / 2 := by rw [hk_m]; exact hN₃ m hN₃m
  have s₄ : A₄ * ϑ₄ ^ k < 1 / 2 := by rw [hk_m]; exact hN₄ m hN₄m
  have p₂ : 0 ≤ A₂ * ϑ₂ ^ k := mul_nonneg hA₂ (zpow_nonneg hϑ₂0 _)
  have p₄ : 0 ≤ A₄ * ϑ₄ ^ k := mul_nonneg hA₄ (zpow_nonneg hϑ₄0 _)

  have lhτ : ((eτ : ℝ) - 1 / 2) * Nτ < ‖h τ‖ := by
    have := norm_sub_norm_le ((eτ : ℂ) * ((τ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)) (h τ)
    rw [norm_sub_rev] at b₁
    rw [norm_mul, hnormτ, Complex.norm_natCast] at this
    have := mul_lt_mul_of_pos_right s₁ hNτpos
    linarith
  have lgσ : ((eσ : ℝ) - 1 / 2) * Nσ < ‖g σ‖ := by
    have := norm_sub_norm_le ((eσ : ℂ) * ((σ : ℂ) - (starRingEnd ℂ) (σ : ℂ)) ^ (-k)) (g σ)
    rw [norm_sub_rev] at b₃
    rw [norm_mul, hnormσ, Complex.norm_natCast] at this
    have := mul_lt_mul_of_pos_right s₃ hNσpos
    linarith
  have uhσ : ‖h σ‖ ≤ A₂ * ϑ₂ ^ k * (2 * Real.sqrt (σ.im * τ.im)) ^ (-k) := b₂
  have ugτ : ‖g τ‖ ≤ A₄ * ϑ₄ ^ k * (2 * Real.sqrt (τ.im * σ.im)) ^ (-k) := b₄
  have heτ1 : (1 : ℝ) ≤ eτ := by exact_mod_cast heτpos
  have heσ1 : (1 : ℝ) ≤ eσ := by exact_mod_cast heσpos

  intro heq
  have hprod : ‖g σ‖ * ‖h τ‖ = ‖g τ‖ * ‖h σ‖ := by
    rw [← norm_mul, ← norm_mul, ← heq]
  have hsq1 : 0 < 2 * Real.sqrt (σ.im * τ.im) := by positivity
  have hsq2 : 0 < 2 * Real.sqrt (τ.im * σ.im) := by positivity
  have c1 : 0 ≤ (2 * Real.sqrt (σ.im * τ.im)) ^ (-k) := zpow_nonneg hsq1.le _
  have c2 : 0 ≤ (2 * Real.sqrt (τ.im * σ.im)) ^ (-k) := zpow_nonneg hsq2.le _
  have upper : ‖g τ‖ * ‖h σ‖ ≤ (1 / 2) * (1 / 2) * (Nσ * Nτ) := by
    calc ‖g τ‖ * ‖h σ‖ ≤ (A₄ * ϑ₄ ^ k * (2 * Real.sqrt (τ.im * σ.im)) ^ (-k)) *
          (A₂ * ϑ₂ ^ k * (2 * Real.sqrt (σ.im * τ.im)) ^ (-k)) :=
            mul_le_mul ugτ uhσ (norm_nonneg _) (by positivity)
      _ = (A₄ * ϑ₄ ^ k) * (A₂ * ϑ₂ ^ k) * ((2 * Real.sqrt (σ.im * τ.im)) ^ (-k) * (2 * Real.sqrt (τ.im * σ.im)) ^ (-k)) := by ring
      _ = (A₄ * ϑ₄ ^ k) * (A₂ * ϑ₂ ^ k) * (Nσ * Nτ) := by rw [hcross]
      _ ≤ (1 / 2) * (1 / 2) * (Nσ * Nτ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul s₄.le s₂.le p₂ (by norm_num)
  have lower : (1 / 2) * (1 / 2) * (Nσ * Nτ) < ‖g σ‖ * ‖h τ‖ := by
    have e1 : (1 / 2 : ℝ) * Nσ ≤ ((eσ : ℝ) - 1 / 2) * Nσ := mul_le_mul_of_nonneg_right (by linarith) hNσpos.le
    have e2 : (1 / 2 : ℝ) * Nτ ≤ ((eτ : ℝ) - 1 / 2) * Nτ := mul_le_mul_of_nonneg_right (by linarith) hNτpos.le
    have e3 : 0 ≤ (1 / 2 : ℝ) * Nσ := by positivity
    have e4 : 0 ≤ (1 / 2 : ℝ) * Nτ := by positivity
    calc (1 / 2) * (1 / 2) * (Nσ * Nτ) = ((1 / 2) * Nσ) * ((1 / 2) * Nτ) := by ring
      _ ≤ (((eσ : ℝ) - 1 / 2) * Nσ) * (((eτ : ℝ) - 1 / 2) * Nτ) := mul_le_mul e1 e2 e4 (e3.trans e1)
      _ < ‖g σ‖ * ‖h τ‖ := mul_lt_mul'' lgσ lhτ (e3.trans e1) (e4.trans e2)
  linarith

end T3aAux

namespace T3aAux

theorem analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) (τ : ℍ) :
    AnalyticAt ℂ (f ∘ ↑ofComplex) (τ : ℂ) := by
  have hd := (UpperHalfPlane.mdifferentiable_iff).1 hf
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

theorem meromorphicOrderAt_div_of_ne_zero {F G : ℂ → ℂ} {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀) (hG : AnalyticAt ℂ G z₀)
    (hG0 : G z₀ ≠ 0) : meromorphicOrderAt (fun z => F z / G z) z₀ = meromorphicOrderAt F z₀ := by
  have h1 : (fun z => F z / G z) = F * G⁻¹ := by funext z; simp [div_eq_mul_inv]
  rw [h1, meromorphicOrderAt_mul hF.meromorphicAt hG.meromorphicAt.inv, meromorphicOrderAt_inv,
    hG.meromorphicOrderAt_eq, (hG.analyticOrderAt_eq_zero).2 hG0]
  simp

theorem div_smul_eq {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} (g h : ModularForm Γ k)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ) (z : ℍ) : g (γ • z) / h (γ • z) = g z / h z := by
  rw [SlashInvariantForm.slash_action_eqn'' g hγ z, SlashInvariantForm.slash_action_eqn'' h hγ z]
  rw [mul_div_mul_left _ _ (zpow_ne_zero k (denom_ne_zero γ z))]

theorem norm_coeff_le_of_sphere_bound {R G : ℂ → ℂ} {z₀ : ℂ} {e : ℕ} {ρ ρ' C : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hR : DifferentiableOn ℂ R (Metric.ball z₀ ρ')) (hG : AnalyticAt ℂ G z₀)
    (hfac : ∀ᶠ z in 𝓝 z₀, R z = (z - z₀) ^ e • G z)
    (hC : ∀ z ∈ Metric.sphere z₀ ρ, ‖R z‖ ≤ C) : ‖G z₀‖ ≤ C / ρ ^ e := by
  classical
  let R₁ : ℂ → ℂ := fun z => if z = z₀ then G z₀ else R z / (z - z₀) ^ e
  have hR₁z₀ : R₁ z₀ = G z₀ := by simp [R₁]

  have hev : ∀ᶠ z in 𝓝 z₀, R₁ z = G z := by
    filter_upwards [hfac] with z hz
    by_cases h : z = z₀
    · simp [R₁, h]
    · simp only [R₁, h, if_false, hz, smul_eq_mul]
      rw [mul_div_cancel_left₀ _ (pow_ne_zero e (sub_ne_zero.2 h))]

  have hdiff : DifferentiableOn ℂ R₁ (Metric.ball z₀ ρ') := by
    intro z hz
    by_cases h : z = z₀
    · subst h
      exact (hG.differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt
    · have hopen : IsOpen (Metric.ball z₀ ρ' \ {z₀}) := Metric.isOpen_ball.sdiff isClosed_singleton
      have hzmem : z ∈ Metric.ball z₀ ρ' \ {z₀} := ⟨hz, h⟩
      have h2 : DifferentiableOn ℂ (fun w => R w / (w - z₀) ^ e) (Metric.ball z₀ ρ' \ {z₀}) := by
        refine (hR.mono Set.diff_subset).div ((differentiableOn_id.sub (differentiableOn_const _)).pow e) ?_
        intro w hw; exact pow_ne_zero e (sub_ne_zero.2 hw.2)
      have h3 : DifferentiableAt ℂ (fun w => R w / (w - z₀) ^ e) z := h2.differentiableAt (hopen.mem_nhds hzmem)
      refine (h3.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds h] with w hw
      simp [R₁, hw]
  have hdcc : DiffContOnCl ℂ R₁ (Metric.ball z₀ ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hρ.ne']
    exact hdiff.mono (Metric.closedBall_subset_ball hρρ')
  have hfront : ∀ z ∈ frontier (Metric.ball z₀ ρ), ‖R₁ z‖ ≤ C / ρ ^ e := by
    intro z hz
    rw [frontier_ball z₀ hρ.ne'] at hz
    have hzρ : ‖z - z₀‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hne : z ≠ z₀ := by
      intro h; rw [h, sub_self, norm_zero] at hzρ; exact hρ.ne' hzρ.symm
    simp only [R₁, hne, if_false, norm_div, norm_pow, hzρ]
    exact div_le_div_of_nonneg_right (hC z hz) (pow_pos hρ e).le
  have := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdcc hfront
    (z := z₀) (by rw [closure_ball z₀ hρ.ne']; exact Metric.mem_closedBall_self hρ.le)
  rwa [hR₁z₀] at this

end T3aAux

namespace T3aAux

set_option maxHeartbeats 4000000 in

theorem partB {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (hneg : -1 ∈ Γ) [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) (τ : ℍ) :
    ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ) := by
  classical
  haveI : Γ.HasDetOne := ⟨fun hg => hdet _ hg⟩
  haveI hfinτ : Finite ↥(MulAction.stabilizer ↥Γ τ) := (UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one Γ hdet τ).1
  set e2 : ℕ := Nat.card ↥(MulAction.stabilizer ↥Γ τ) with he2
  have he2pos : 0 < e2 := Nat.card_pos
  have he22 : 2 ∣ e2 := UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem Γ hdet hneg τ
  set e : ℕ := e2 / 2 with he
  have hee : 2 * e = e2 := Nat.mul_div_cancel' he22
  have hepos : 0 < e := by omega
  set z₀ : ℂ := (τ : ℂ) with hz₀
  set w₀ : ℂ := (starRingEnd ℂ) (τ : ℂ) with hw₀
  set y : ℝ := τ.im with hy
  have hy0 : 0 < y := τ.im_pos
  have hzw : z₀ - w₀ = (2 * y : ℝ) * Complex.I := by
    apply Complex.ext
    · simp [hz₀, hw₀, Complex.sub_re, Complex.conj_re]
    · rw [hz₀, hw₀, Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im]; simp [hy]; ring
  have hnzw : ‖z₀ - w₀‖ = 2 * y := by
    rw [hzw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]

  obtain ⟨U, hUo, hτU, A, ϑ, hA, hϑ0, hϑ1, H⟩ :=
    ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology Γ hdet hcusp τ τ

  have hUo' : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hUo
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hUo' z₀ ⟨τ, hτU, rfl⟩

  set ρ : ℝ := min (r₀ / 2) (y * (1 - ϑ) / 2) with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; exact lt_min (by linarith) (by nlinarith)
  have hρr : ρ < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρy : ρ ≤ y * (1 - ϑ) / 2 := min_le_right _ _
  have hρy2 : ρ < y := by nlinarith
  set s : ℝ := 2 * Real.sqrt ((y - ρ) * y) with hs
  have hs0 : 0 < s := by rw [hs]; exact mul_pos two_pos (Real.sqrt_pos.2 (by nlinarith))

  set q₁ : ℝ := 2 * y * ϑ / s with hq₁
  set q₂ : ℝ := 2 * y * ϑ / (2 * y - ρ) with hq₂
  have hq₁0 : 0 ≤ q₁ := by rw [hq₁]; positivity
  have hq₂0 : 0 ≤ q₂ := by rw [hq₂]; exact div_nonneg (by positivity) (by linarith)
  have hq₁1 : q₁ < 1 := by
    rw [hq₁, div_lt_one hs0, hs]
    have h1 : y * ϑ < Real.sqrt ((y - ρ) * y) := by
      rw [show y * ϑ = Real.sqrt ((y * ϑ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_lt_sqrt (by positivity)
      have h2 : y * y * (1 + ϑ) / 2 ≤ (y - ρ) * y := by nlinarith [hρy, hy0]
      have hyy : 0 < y * y := mul_pos hy0 hy0
      have h3 : ϑ ^ 2 * 2 < 1 + ϑ := by nlinarith
      have h4 : (y * ϑ) ^ 2 < y * y * (1 + ϑ) / 2 := by
        rw [mul_pow]; nlinarith
      linarith
    linarith
  have hq₂1 : q₂ < 1 := by
    rw [hq₂, div_lt_one (by linarith)]
    nlinarith
  set q : ℝ := max q₁ q₂ with hq
  have hq0 : 0 ≤ q := le_max_of_le_left hq₁0
  have hq1 : q < 1 := max_lt hq₁1 hq₂1

  set K₀ : ℝ := A * (1 + 2 * A + 2 * e2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  set target : ℝ := (e2 : ℝ) * ((2 * y) ^ e)⁻¹ * ρ ^ e with htarget
  have htarget0 : 0 < target := by rw [htarget]; positivity
  obtain ⟨N₁, hN₁⟩ := eventually_small hA hϑ0 hϑ1
  have hev2 : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → K₀ * q ^ m < target := by
    have ht : Filter.Tendsto (fun m : ℕ => K₀ * q ^ m) Filter.atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul K₀
      simpa using this
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually_lt_const htarget0)
    exact ⟨N, hN⟩
  obtain ⟨N₂, hN₂⟩ := hev2
  set M : ℕ := max (max N₁ N₂) 4 with hM
  set m : ℕ := e2 * M with hm
  have hMle : M ≤ m := by rw [hm]; exact Nat.le_mul_of_pos_left M he2pos
  have hN₁m : N₁ ≤ m := le_trans (by rw [hM]; omega) hMle
  have hN₂m : N₂ ≤ m := le_trans (by rw [hM]; omega) hMle
  have h4m : 4 ≤ m := le_trans (by rw [hM]; omega) hMle
  set k : ℤ := (m : ℤ) with hk
  have hk4 : (4 : ℤ) ≤ k := by rw [hk]; exact_mod_cast h4m
  have hkeven : Even k := by
    rw [hk, Int.even_coe_nat, hm]; exact (even_iff_two_dvd.2 he22).mul_right _
  have hdiv0 : (e2 : ℤ) ∣ 2 * ((0 : ℕ) : ℤ) + k := by
    rw [hk, hm]; push_cast; simp only [mul_zero, zero_add]; exact ⟨(M : ℤ), by ring⟩
  have hdive : (e2 : ℤ) ∣ 2 * ((e : ℕ) : ℤ) + k := by
    rw [hk, hm]; refine ⟨(M : ℤ) + 1, ?_⟩; push_cast; rw [← hee]; push_cast; ring
  have small1 : A * ϑ ^ m < 1 / 2 := hN₁ m hN₁m
  have small2 : K₀ * q ^ m < target := hN₂ m hN₂m

  obtain ⟨h, hhf, hhb⟩ := H 0 k hk4
  obtain ⟨g₁, hg₁f, hg₁b⟩ := H e k hk4
  set c : ℂ := g₁ τ / h τ with hc
  set g : ModularForm Γ k := g₁ - c • h with hg
  have hgapp : ∀ σ : ℍ, g σ = g₁ σ - c * h σ := fun σ => by
    rw [hg, ModularForm.sub_apply]; rfl

  have hzp : ∀ x : ℝ, x ^ (-k) = (x ^ m)⁻¹ := fun x => by rw [hk, zpow_neg, zpow_natCast]
  have hzpC : ∀ x : ℂ, x ^ (-k) = (x ^ m)⁻¹ := fun x => by rw [hk, zpow_neg, zpow_natCast]
  have hϑk : ϑ ^ k = ϑ ^ m := by rw [hk, zpow_natCast]
  set N : ℝ := ((2 * y) ^ m)⁻¹ with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hy2 : 0 < 2 * y := by linarith

  have hS0 := stab_sum hdet τ 0 k hdiv0
  have hSe := stab_sum hdet τ e k hdive
  have bτ := hhb τ hτU
  rw [hS0 τ, sqrt_im_mul_self] at bτ
  simp only [pow_zero, one_mul] at bτ
  have bτe := hg₁b τ hτU
  rw [hSe τ, sqrt_im_mul_self] at bτe
  simp only [sub_self, zero_div, zero_pow hepos.ne', zero_mul, mul_zero, sub_zero] at bτe

  have hnormmain : ‖((τ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖ = N := by
    rw [norm_zpow, norm_sub_conj, hzp, hN]
  rw [hϑk, ← hy, hzp] at bτ bτe
  change ‖h τ - (e2 : ℂ) * ((τ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖ ≤ A * ϑ ^ m * N at bτ
  change ‖g₁ τ‖ ≤ A * ϑ ^ m * N at bτe

  have hsmallN : A * ϑ ^ m * N < 1 / 2 * N := mul_lt_mul_of_pos_right small1 hNpos
  have lh : 1 / 2 * N < ‖h τ‖ := by
    have := norm_sub_norm_le ((e2 : ℂ) * ((τ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)) (h τ)
    rw [norm_sub_rev] at bτ
    rw [norm_mul, hnormmain, Complex.norm_natCast] at this
    have he21 : (1 : ℝ) ≤ e2 := by exact_mod_cast he2pos
    have he2N : N ≤ (e2 : ℝ) * N := by nlinarith
    linarith
  have hhτ : h τ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at lh; linarith [hNpos]

  have hcb : ‖c‖ ≤ 2 * (A * ϑ ^ m) := by
    rw [hc, norm_div]
    rw [div_le_iff₀ (by linarith [hNpos] : 0 < ‖h τ‖)]
    have hAm : 0 ≤ A * ϑ ^ m := mul_nonneg hA (pow_nonneg hϑ0 m)
    calc ‖g₁ τ‖ ≤ A * ϑ ^ m * N := bτe
      _ = 2 * (A * ϑ ^ m) * (1 / 2 * N) := by ring
      _ ≤ 2 * (A * ϑ ^ m) * ‖h τ‖ := mul_le_mul_of_nonneg_left lh.le (by positivity)
  refine ⟨k, hk4, hkeven, g, h, hhτ, ?_⟩

  have hga : AnalyticAt ℂ (fun z : ℂ => g (ofComplex z)) z₀ := analyticAt_comp_ofComplex g.holo' τ
  have hha : AnalyticAt ℂ (fun z : ℂ => h (ofComplex z)) z₀ := analyticAt_comp_ofComplex h.holo' τ
  have hhz₀ : (fun z : ℂ => h (ofComplex z)) z₀ ≠ 0 := by
    show h (ofComplex (τ : ℂ)) ≠ 0; rwa [ofComplex_apply]
  rw [meromorphicOrderAt_div_of_ne_zero hga hha hhz₀, hga.meromorphicOrderAt_eq]

  suffices hord : analyticOrderAt (fun z : ℂ => g (ofComplex z)) z₀ = e by
    rw [hord]; rfl

  have hgτ : g τ = 0 := by rw [hgapp, hc, div_mul_cancel₀ _ hhτ, sub_self]
  have hgz₀ : (fun z : ℂ => g (ofComplex z)) z₀ = 0 := by
    show g (ofComplex (τ : ℂ)) = 0; rwa [ofComplex_apply]

  have hsphere : ∀ z ∈ Metric.sphere z₀ ρ, ∃ σ : ℍ, σ ∈ U ∧ (σ : ℂ) = z ∧ y - ρ ≤ σ.im ∧ 2 * y - ρ ≤ ‖(σ : ℂ) - w₀‖ := by
    intro z hz
    have hzρ : ‖z - z₀‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzball : z ∈ Metric.ball z₀ r₀ := by
      rw [Metric.mem_ball, dist_eq_norm, hzρ]; exact hρr
    obtain ⟨σ, hσU, hσz⟩ := hball hzball
    refine ⟨σ, hσU, hσz, ?_, ?_⟩
    · have h1 := Complex.abs_im_le_norm (z - z₀)
      rw [hzρ, Complex.sub_im] at h1
      have : z.im = σ.im := by rw [← hσz, UpperHalfPlane.coe_im]
      rw [← this]
      have h2 := neg_abs_le (z.im - z₀.im)
      have : z₀.im = y := by rw [hz₀, UpperHalfPlane.coe_im]
      linarith
    · rw [hσz]
      have := norm_sub_norm_le (z₀ - w₀) (z₀ - z)
      rw [hnzw, show z₀ - w₀ - (z₀ - z) = z - w₀ by ring, norm_sub_rev z₀ z, hzρ] at this
      linarith

  have hballH : Metric.ball z₀ r₀ ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz; obtain ⟨σ, _, rfl⟩ := hball hz; exact σ.im_pos
  have hw₀im : w₀.im = -y := by rw [hw₀, Complex.conj_im, UpperHalfPlane.coe_im]
  have hzw₀ : ∀ z ∈ Metric.ball z₀ r₀, z - w₀ ≠ 0 := by
    intro z hz h
    have := hballH hz
    simp only [Set.mem_setOf_eq] at this
    have h2 := congrArg Complex.im h
    rw [Complex.sub_im, hw₀im, Complex.zero_im] at h2
    linarith

  set Fg : ℂ → ℂ := fun z => g (ofComplex z) with hFg
  have hFgd : DifferentiableOn ℂ Fg (Metric.ball z₀ r₀) :=
    ((UpperHalfPlane.mdifferentiable_iff).1 g.holo').mono hballH

  have hle : analyticOrderAt Fg z₀ ≤ (e : ℕ∞) := by
    by_contra hlt
    push Not at hlt
    have hle1 : ((e + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt Fg z₀ := by
      rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt hlt
    obtain ⟨G, hGa, hGev⟩ := (natCast_le_analyticOrderAt hga).1 hle1
    set Φ : ℂ → ℂ := fun z => ((z - w₀) ^ e)⁻¹ * (z - w₀) ^ (-k) with hΦ
    set G₁ : ℂ → ℂ := fun z => (z - z₀) * G z - (e2 : ℂ) * Φ z with hG₁
    set R : ℂ → ℂ := fun z => Fg z - (e2 : ℂ) * ((z - z₀) ^ e * Φ z) with hR
    have hΦd : DifferentiableOn ℂ Φ (Metric.ball z₀ r₀) := by
      rw [hΦ]
      refine DifferentiableOn.mul ?_ ?_
      · refine DifferentiableOn.inv ((differentiableOn_id.sub (differentiableOn_const _)).pow e) ?_
        intro z hz; exact pow_ne_zero e (hzw₀ z hz)
      · exact ((differentiableOn_id.sub (differentiableOn_const _)).zpow (Or.inl (fun z hz => hzw₀ z hz)))
    have hΦa : AnalyticAt ℂ Φ z₀ := hΦd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
    have hG₁a : AnalyticAt ℂ G₁ z₀ := by
      rw [hG₁]
      exact ((analyticAt_id.sub analyticAt_const).mul hGa).sub (analyticAt_const.mul hΦa)
    have hRd : DifferentiableOn ℂ R (Metric.ball z₀ r₀) := by
      rw [hR]
      exact hFgd.sub ((differentiableOn_const _).mul (((differentiableOn_id.sub (differentiableOn_const _)).pow e).mul hΦd))
    have hfac : ∀ᶠ z in 𝓝 z₀, R z = (z - z₀) ^ e • G₁ z := by
      filter_upwards [hGev] with z hz
      simp only [hR, hG₁, smul_eq_mul]
      rw [hz, smul_eq_mul]
      ring

    have hG₁z₀ : ‖G₁ z₀‖ = (e2 : ℝ) * ((2 * y) ^ e)⁻¹ * N := by
      have : G₁ z₀ = -((e2 : ℂ) * Φ z₀) := by simp only [hG₁]; ring
      rw [this, norm_neg, norm_mul, Complex.norm_natCast]
      simp only [hΦ, norm_mul, norm_inv, norm_pow, norm_zpow, hnzw, hzp, hN]
      ring

    set CR : ℝ := A * ϑ ^ m * (s ^ m)⁻¹ + 2 * (A * ϑ ^ m) * ((e2 : ℝ) * ((2 * y - ρ) ^ m)⁻¹ + A * ϑ ^ m * (s ^ m)⁻¹) with hCR
    have hsph : ∀ z ∈ Metric.sphere z₀ ρ, ‖R z‖ ≤ CR := by
      intro z hz
      obtain ⟨σ, hσU, hσz, hσim, hσw⟩ := hsphere z hz
      have hofc : ofComplex z = σ := by rw [← hσz, ofComplex_apply]

      have b0 := hhb σ hσU
      have be := hg₁b σ hσU
      rw [hS0 σ] at b0
      rw [hSe σ] at be
      simp only [pow_zero, one_mul] at b0

      have hsσ : s ≤ 2 * Real.sqrt (σ.im * τ.im) := by
        rw [hs, ← hy]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hσim hy0.le)) (by norm_num)
      have hgauge : (2 * Real.sqrt (σ.im * τ.im)) ^ (-k) ≤ (s ^ m)⁻¹ := by
        rw [hzp]
        exact inv_anti₀ (pow_pos hs0 m) (pow_le_pow_left₀ hs0.le hsσ m)
      have hAm : 0 ≤ A * ϑ ^ m := mul_nonneg hA (pow_nonneg hϑ0 m)
      rw [hϑk] at b0 be
      have b0' : ‖h σ - (e2 : ℂ) * ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖ ≤ A * ϑ ^ m * (s ^ m)⁻¹ :=
        b0.trans (mul_le_mul_of_nonneg_left hgauge hAm)
      have be' : ‖g₁ σ - (e2 : ℂ) * ((((σ : ℂ) - (τ : ℂ)) / ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ))) ^ e *
          ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k))‖ ≤ A * ϑ ^ m * (s ^ m)⁻¹ :=
        be.trans (mul_le_mul_of_nonneg_left hgauge hAm)

      have hmain : ‖((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖ ≤ ((2 * y - ρ) ^ m)⁻¹ := by
        rw [norm_zpow, hzp]
        have h2yρ : 0 < 2 * y - ρ := by linarith
        exact inv_anti₀ (pow_pos h2yρ m) (pow_le_pow_left₀ h2yρ.le (by rw [← hw₀]; exact hσw) m)

      have hRz : R z = (g₁ σ - (e2 : ℂ) * ((((σ : ℂ) - (τ : ℂ)) / ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ))) ^ e *
          ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k))) - c * (h σ - (e2 : ℂ) * ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k))
          - c * ((e2 : ℂ) * ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)) := by
        simp only [hR, hFg, hΦ]
        rw [hofc, hgapp σ, ← hσz, hw₀, hz₀, div_pow, div_eq_mul_inv]
        ring
      rw [hRz]
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, hCR]
      have t1 := be'
      have t2 : ‖c‖ * ‖h σ - (e2 : ℂ) * ((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖ ≤ 2 * (A * ϑ ^ m) * (A * ϑ ^ m * (s ^ m)⁻¹) :=
        mul_le_mul hcb b0' (norm_nonneg _) (by positivity)
      have t3 : ‖c‖ * ((e2 : ℝ) * ‖((σ : ℂ) - (starRingEnd ℂ) (τ : ℂ)) ^ (-k)‖) ≤ 2 * (A * ϑ ^ m) * ((e2 : ℝ) * ((2 * y - ρ) ^ m)⁻¹) :=
        mul_le_mul hcb (mul_le_mul_of_nonneg_left hmain (by positivity)) (by positivity) (by positivity)
      linarith
    have hcoef := norm_coeff_le_of_sphere_bound hρ0 hρr hRd hG₁a hfac hsph

    have h2yρ : 0 < 2 * y - ρ := by linarith
    have hq₁m : ϑ ^ m * (s ^ m)⁻¹ = q₁ ^ m * N := by
      rw [hq₁, hN, div_pow, mul_pow]
      field_simp
      ring
    have hq₂m : ϑ ^ m * ((2 * y - ρ) ^ m)⁻¹ = q₂ ^ m * N := by
      rw [hq₂, hN, div_pow, mul_pow]
      field_simp
    have hq₁le : q₁ ^ m ≤ q ^ m := pow_le_pow_left₀ hq₁0 (le_max_left _ _) m
    have hq₂le : q₂ ^ m ≤ q ^ m := pow_le_pow_left₀ hq₂0 (le_max_right _ _) m
    have hϑm1 : ϑ ^ m ≤ 1 := pow_le_one₀ hϑ0 hϑ1.le
    have hqm0 : 0 ≤ q ^ m := pow_nonneg hq0 m
    have hCReq : CR = N * (A * q₁ ^ m + 2 * A * (e2 : ℝ) * q₂ ^ m + 2 * A ^ 2 * (ϑ ^ m * q₁ ^ m)) := by
      have : CR = A * (ϑ ^ m * (s ^ m)⁻¹) + 2 * A * (e2 : ℝ) * (ϑ ^ m * ((2 * y - ρ) ^ m)⁻¹) +
          2 * A ^ 2 * ϑ ^ m * (ϑ ^ m * (s ^ m)⁻¹) := by rw [hCR]; ring
      rw [this, hq₁m, hq₂m]; ring
    have hCRle : CR ≤ K₀ * q ^ m * N := by
      rw [hCReq, hK₀]
      have t1 : A * q₁ ^ m ≤ A * q ^ m := mul_le_mul_of_nonneg_left hq₁le hA
      have t2 : 2 * A * (e2 : ℝ) * q₂ ^ m ≤ 2 * A * (e2 : ℝ) * q ^ m := mul_le_mul_of_nonneg_left hq₂le (by positivity)
      have t3 : 2 * A ^ 2 * (ϑ ^ m * q₁ ^ m) ≤ 2 * A ^ 2 * (1 * q ^ m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hϑm1 hq₁le (pow_nonneg hq₁0 m) zero_le_one) (by positivity)
      have : N * (A * q₁ ^ m + 2 * A * (e2 : ℝ) * q₂ ^ m + 2 * A ^ 2 * (ϑ ^ m * q₁ ^ m)) ≤
          N * (A * q ^ m + 2 * A * (e2 : ℝ) * q ^ m + 2 * A ^ 2 * (1 * q ^ m)) :=
        mul_le_mul_of_nonneg_left (by linarith) hNpos.le
      refine this.trans (le_of_eq ?_)
      ring
    have hρe : 0 < ρ ^ e := pow_pos hρ0 e
    have hfinal : (e2 : ℝ) * ((2 * y) ^ e)⁻¹ * N < (e2 : ℝ) * ((2 * y) ^ e)⁻¹ * N := by
      calc (e2 : ℝ) * ((2 * y) ^ e)⁻¹ * N = ‖G₁ z₀‖ := hG₁z₀.symm
        _ ≤ CR / ρ ^ e := hcoef
        _ ≤ K₀ * q ^ m * N / ρ ^ e := div_le_div_of_nonneg_right hCRle hρe.le
        _ < target * N / ρ ^ e := by
            apply div_lt_div_of_pos_right _ hρe
            exact mul_lt_mul_of_pos_right small2 hNpos
        _ = (e2 : ℝ) * ((2 * y) ^ e)⁻¹ * N := by
            rw [htarget]; field_simp
    exact lt_irrefl _ hfinal

  have hne_top : analyticOrderAt Fg z₀ ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top e) hle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne_top
  have hn_le : n ≤ e := by
    have := hle; rw [← hn] at this; exact_mod_cast this
  have hn_pos : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    exact ((hga.analyticOrderAt_eq_zero).1 hn.symm) hgz₀

  have hinv : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, (fun σ : ℍ => g σ / h σ) (γ • z) = (fun σ : ℍ => g σ / h σ) z :=
    fun γ hγ _ => Filter.Eventually.of_forall fun z => div_smul_eq g h hγ z
  have hordQ : meromorphicOrderAt (fun z : ℂ => (fun σ : ℍ => g σ / h σ) (ofComplex z)) (τ : ℂ) = ((n : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) z₀ = ((n : ℤ) : WithTop ℤ)
    rw [meromorphicOrderAt_div_of_ne_zero hga hha hhz₀, hga.meromorphicOrderAt_eq]
    show ENat.map Nat.cast (analyticOrderAt Fg z₀) = ((n : ℤ) : WithTop ℤ)
    rw [← hn]; rfl
  have hdvd := UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one Γ hdet
    (fun σ : ℍ => g σ / h σ) τ hinv n hordQ
  have hediv : e ∣ n := by
    have h1 : ((2 * e : ℕ) : ℤ) ∣ 2 * (n : ℤ) := by rw [hee]; exact hdvd
    have h2 : (e : ℤ) ∣ (n : ℤ) := by
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, by push_cast at hc; linarith⟩
    exact_mod_cast h2
  have hneq : n = e := by
    obtain ⟨c, hc⟩ := hediv
    have hc0 : c ≠ 0 := by rintro rfl; exact hn_pos (by rw [hc, mul_zero])
    have hc1 : c ≤ 1 := by
      by_contra hlt; push Not at hlt
      have : e * 2 ≤ e * c := Nat.mul_le_mul_left e hlt
      rw [← hc] at this; omega
    have : c = 1 := by omega
    rw [hc, this, mul_one]
  rw [← hn, hneq]

end T3aAux

open T3aAux in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) :

    (∀ τ σ : ℍ, (∀ γ ∈ Γ, γ • τ ≠ σ) →
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ) ∧

    (∀ τ : ℍ, ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ)) :=
  ⟨fun τ σ hne => T3aAux.partA hdet hneg hcusp τ σ hne, fun τ => T3aAux.partB hdet hneg hcusp τ⟩

end S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology (solution)
