-- Prove2me | solution 1 for ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7ea74616-c784-56d6-b874-8b155de15d6a

import Mathlib
import Theorems.Thm_PowerSeries_coeff_mem_subring_of_coeff_mul_mem
import Theorems.Thm_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_mul_width
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg
import Theorems.Thm_ModularForm_exists_levelOne_coe_eq_sum_slash
import Theorems.Thm_CongruenceSubgroup_exists_finset_transversal_adapted_T_S
import Theorems.Thm_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false
set_option linter.unusedVariables false

namespace TRAssembly

open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

theorem denom_T_zpow (j : ℤ) (τ : UpperHalfPlane) : denom (ModularGroup.T ^ j : SL(2, ℤ)) τ = 1 := by
  rw [ModularGroup.denom_apply]
  simp [ModularGroup.coe_T_zpow]

def pmSubgroup (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by rw [← mul_neg]; exact Γ.mul_mem ha hb)
    · exact Or.inr (by rw [← neg_mul]; exact Γ.mul_mem ha hb)
    · exact Or.inl (by rw [← neg_mul_neg]; exact Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have h1 : (-a)⁻¹ ∈ Γ := Γ.inv_mem ha
      have h2 : (-a)⁻¹ = -a⁻¹ := inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
      rwa [h2] at h1

theorem mem_pmSubgroup_iff {Γ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} : g ∈ pmSubgroup Γ ↔ g ∈ Γ ∨ -g ∈ Γ :=
  Iff.rfl

theorem exists_width (Γ : Subgroup SL(2, ℤ)) (h : ℕ) (hh : 0 < h) (hT : ModularGroup.T ^ h ∈ Γ) :
    ∃ h₀ : ℕ, 0 < h₀ ∧ h₀ ∣ h ∧ (ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ) ∧
      (∀ j : ℕ, 0 < j → j < h₀ → ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ) := by
  classical
  let P : ℕ → Prop := fun n => 0 < n ∧ (ModularGroup.T ^ n ∈ Γ ∨ -(ModularGroup.T ^ n) ∈ Γ)
  have hex : ∃ n, P n := ⟨h, hh, Or.inl hT⟩
  have hspec : P (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ j, 0 < j → j < Nat.find hex → ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ := by
    intro j hj hjlt
    have hnot : ¬ P j := Nat.find_min hex hjlt
    exact ⟨fun hm => hnot ⟨hj, Or.inl hm⟩, fun hm => hnot ⟨hj, Or.inr hm⟩⟩
  refine ⟨Nat.find hex, hspec.1, ?_, hspec.2, hmin⟩
  have hr : ModularGroup.T ^ (h % Nat.find hex) ∈ pmSubgroup Γ := by
    have h1 : ModularGroup.T ^ h ∈ pmSubgroup Γ := Or.inl hT
    have h2 : ModularGroup.T ^ Nat.find hex ∈ pmSubgroup Γ := hspec.2
    have heq : ModularGroup.T ^ h =
        (ModularGroup.T ^ Nat.find hex) ^ (h / Nat.find hex) * ModularGroup.T ^ (h % Nat.find hex) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [heq] at h1
    exact (Subgroup.mul_mem_cancel_left _ (Subgroup.pow_mem _ h2 _)).mp h1
  by_contra hndvd
  have hpos : 0 < h % Nat.find hex := Nat.pos_of_ne_zero (fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
  have hlt : h % Nat.find hex < Nat.find hex := Nat.mod_lt _ hspec.1
  rcases hr with hr | hr
  · exact (hmin _ hpos hlt).1 hr
  · exact (hmin _ hpos hlt).2 hr

theorem slash_T_zpow_apply (X : UpperHalfPlane → ℂ) (κ : ℤ) (j : ℤ) (τ : UpperHalfPlane) :
    (X ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ = X ((j : ℝ) +ᵥ τ) := by
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, modular_T_zpow_smul, denom_T_zpow, one_zpow, mul_one]

theorem slash_T_pow_apply (X : UpperHalfPlane → ℂ) (κ : ℤ) (j : ℕ) (τ : UpperHalfPlane) :
    (X ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ = X (((j : ℕ) : ℝ) +ᵥ τ) := by
  have h := slash_T_zpow_apply X κ (j : ℤ) τ
  rwa [zpow_natCast, Int.cast_natCast] at h

section Degenerate

theorem T_mem_of_S_mul_T_zpow_mem (Γ : Subgroup SL(2, ℤ))
    (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ) {j : ℤ}
    (hdeg : ModularGroup.S * ModularGroup.T ^ j ∈ Γ ∨ -(ModularGroup.S * ModularGroup.T ^ j) ∈ Γ) :
    ModularGroup.T ∈ Γ := by
  have key : ∀ γ : SL(2, ℤ), (γ = ModularGroup.S * ModularGroup.T ^ j ∨ γ = -(ModularGroup.S * ModularGroup.T ^ j)) →
      γ⁻¹ * (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) * γ = ModularGroup.T := by
    rintro γ (rfl | rfl)
    · group
    · rw [inv_neg, neg_mul, neg_mul, mul_neg, neg_neg]
      group
  rcases hdeg with h | h
  · rw [← key _ (Or.inl rfl)]
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem h) hS) h
  · rw [← key _ (Or.inr rfl)]
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem h) hS) h

theorem coeff_qExpansion_one_eq_of_T_mem
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h) (hT1 : ModularGroup.T ∈ Γ) {k : ℤ}
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑G : UpperHalfPlane → ℂ)).coeff n =
      (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff (h * n) := by

  have hper : ∀ x : ℤ, (x : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := fun x => by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT1]
    exact ⟨x, by simp⟩
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by exact_mod_cast hper 1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hhper : (h : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by exact_mod_cast hper h
  have hGper1 : Function.Periodic ((⇑G : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex G h1
  have hGperh : Function.Periodic ((⇑G : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) h :=
    SlashInvariantFormClass.periodic_comp_ofComplex G hhper
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑G : UpperHalfPlane → ℂ) := ModularFormClass.holo G
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty (⇑G : UpperHalfPlane → ℂ) := ModularFormClass.bdd_at_infty G

  set a : ℕ → ℂ := fun m => (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff m with ha
  have hsum : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => a m • Function.Periodic.qParam (h : ℝ) τ ^ m) (G τ) :=
    fun τ => UpperHalfPlane.hasSum_qExpansion hh' hGperh hhol hbdd τ

  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h) with hξ
  have hq1 : ∀ τ : UpperHalfPlane, Function.Periodic.qParam (h : ℝ) (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) =
      ξ * Function.Periodic.qParam (h : ℝ) τ := by
    intro τ
    rw [Function.Periodic.qParam, Function.Periodic.qParam, UpperHalfPlane.coe_vadd, hξ, ← Complex.exp_add]
    congr 1
    push_cast
    ring

  have hvan : ∀ m : ℕ, ¬ h ∣ m → a m = 0 := by
    intro m hm
    have hanal := UpperHalfPlane.analyticAt_cuspFunction_zero hh' hGperh hhol hbdd
    have hsum' : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => (a m * ξ ^ m) • Function.Periodic.qParam (h : ℝ) τ ^ m) (G τ) := by
      intro τ
      have := hsum ((1 : ℝ) +ᵥ τ)
      rw [SlashInvariantForm.vAdd_apply_of_mem_strictPeriods G τ h1] at this
      simp_rw [hq1 τ, mul_pow, smul_eq_mul] at this
      simpa only [smul_eq_mul, mul_assoc] using this
    have huniq := UpperHalfPlane.qExpansion_coeff_unique G hh' hanal hsum' m

    have hξm : ξ ^ m ≠ 1 := by
      rw [hξ, ← Complex.exp_nat_mul, Ne, Complex.exp_eq_one_iff]
      rintro ⟨z, hz⟩
      apply hm
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp at hz

      have hz' : (m : ℤ) = h * z := by exact_mod_cast hz
      exact Int.natCast_dvd_natCast.mp ⟨z, hz'⟩
    have heq : a m * ξ ^ m = a m := huniq
    have : a m * (ξ ^ m - 1) = 0 := by rw [mul_sub, mul_one, heq, sub_self]
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hξm)

  have hsum1 : ∀ τ : UpperHalfPlane, HasSum (fun n : ℕ => a (h * n) • Function.Periodic.qParam 1 τ ^ n) (G τ) := by
    intro τ
    have hinj : Function.Injective (fun n : ℕ => h * n) := fun x y hxy => Nat.eq_of_mul_eq_mul_left hh hxy
    have key := (hinj.hasSum_iff (f := fun m : ℕ => a m • Function.Periodic.qParam (h : ℝ) τ ^ m) (a := G τ)
      (fun m hm => by
        have hm' : ¬ h ∣ m := fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩
        simp [hvan m hm'])).mpr (hsum τ)
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Function.Periodic.qParam (h : ℝ) τ ^ h := by
      rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      push_cast
      field_simp
    convert key using 1 <;> try rfl
    funext n
    simp only [Function.comp_apply, hq, ← pow_mul]
  have hanal1 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑G : UpperHalfPlane → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hGper1 hhol hbdd
  exact (UpperHalfPlane.qExpansion_coeff_unique G one_pos hanal1 hsum1 n).symm

theorem denom_neg_SL (γ : SL(2, ℤ)) (τ : UpperHalfPlane) : denom (-γ : SL(2, ℤ)) τ = -denom γ τ := by
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
  ring

theorem coeff_mem_of_S_mul_T_zpow_mem
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ} (hkw : Even (k + w))
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ))
    (hΘS₀ : ∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0)
    (hΘS₁ : ∃ v ∈ R, v * (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1)
    (hΘS : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im))
    (hdeg : ∃ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∈ Γ ∨ -(ModularGroup.S * ModularGroup.T ^ j) ∈ Γ)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by
  obtain ⟨j, hj⟩ := hdeg
  have hT1 : ModularGroup.T ∈ Γ := T_mem_of_S_mul_T_zpow_mem Γ hS hj

  have hper : ∀ x : ℤ, (x : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := fun x => by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT1]
    exact ⟨x, by simp⟩
  have hGz : ∀ (x : ℤ) (τ : UpperHalfPlane), G ((x : ℝ) +ᵥ τ) = G τ := fun x τ =>
    SlashInvariantForm.vAdd_apply_of_mem_strictPeriods G τ (hper x)

  have hSeq : (ModularGroup.S : SL(2, ℤ)) = (ModularGroup.S * ModularGroup.T ^ j) * ModularGroup.T ^ (-j) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

  obtain ⟨ε, hεR, hF⟩ : ∃ ε : ℂ, ε ∈ R ∧
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ε • (⇑G : UpperHalfPlane → ℂ) := by
    rcases hj with hγ | hγ
    · refine ⟨1, R.one_mem, ?_⟩
      have hmem : ((ModularGroup.S * ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
        Subgroup.mem_map_of_mem _ hγ
      rw [one_smul, ← ModularForm.SL_slash, hSeq, SlashAction.slash_mul,
        ModularForm.SL_slash _ (ModularGroup.S * ModularGroup.T ^ j),
        SlashInvariantForm.slash_action_eqn G _ hmem]
      funext τ
      rw [ModularForm.SL_slash, slash_T_zpow_apply, hGz]
    · refine ⟨((-1 : ℂ) ^ k)⁻¹, ?_, ?_⟩
      · rcases Int.even_or_odd k with hk | hk
        · rw [hk.neg_one_zpow, inv_one]; exact R.one_mem
        · rw [hk.neg_one_zpow, inv_neg, inv_one]; exact R.neg_mem R.one_mem

      have hSeq' : (ModularGroup.S : SL(2, ℤ)) = -((-(ModularGroup.S * ModularGroup.T ^ j)) * ModularGroup.T ^ (-j)) := by
        rw [neg_mul, neg_neg]; exact hSeq
      have hval : ∀ τ : UpperHalfPlane,
          G (((-(ModularGroup.S * ModularGroup.T ^ j)) * ModularGroup.T ^ (-j)) • τ) *
            denom ((-(ModularGroup.S * ModularGroup.T ^ j)) * ModularGroup.T ^ (-j) : SL(2, ℤ)) τ ^ (-k) = G τ := by
        intro τ
        have hmem : ((-(ModularGroup.S * ModularGroup.T ^ j) : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
          Subgroup.mem_map_of_mem _ hγ
        rw [← ModularForm.SL_slash_apply, SlashAction.slash_mul,
          ModularForm.SL_slash _ (-(ModularGroup.S * ModularGroup.T ^ j)),
          SlashInvariantForm.slash_action_eqn G _ hmem, ModularForm.SL_slash,
          slash_T_zpow_apply, hGz]
      have hneg : ∀ x : ℂ, (-x) ^ (-k) = ((-1 : ℂ) ^ k)⁻¹ * x ^ (-k) := fun x => by
        rw [neg_eq_neg_one_mul, mul_zpow, zpow_neg]
      funext τ
      rw [Pi.smul_apply, smul_eq_mul, ← ModularForm.SL_slash, hSeq', ModularForm.SL_slash_apply,
        ModularGroup.SL_neg_smul, denom_neg_SL, hneg, mul_left_comm, hval]

  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by exact_mod_cast hper 1
  have hanal1 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑G : UpperHalfPlane → ℂ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos (SlashInvariantFormClass.periodic_comp_ofComplex G h1)
      (ModularFormClass.holo G) (ModularFormClass.bdd_at_infty G)
  rw [hF, UpperHalfPlane.qExpansion_smul hanal1, map_smul, smul_eq_mul,
    coeff_qExpansion_one_eq_of_T_mem Γ h hh hT1 G n]
  exact R.mul_mem hεR (hG _)

end Degenerate

end TRAssembly

namespace TRMain

open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

theorem exists_four_mul_add_six_mul {N : ℤ} (hN : Even N) (h4 : 4 ≤ N) :
    ∃ a b : ℕ, 4 * (a : ℤ) + 6 * (b : ℤ) = N := by
  obtain ⟨M, hM⟩ := hN
  rcases Int.even_or_odd M with ⟨t, ht⟩ | ⟨t, ht⟩
  ·
    refine ⟨t.toNat, 0, ?_⟩
    have ht0 : 0 ≤ t := by omega
    rw [Int.toNat_of_nonneg ht0]
    push_cast
    omega
  ·
    refine ⟨(t - 1).toNat, 1, ?_⟩
    have ht1 : 0 ≤ t - 1 := by omega
    rw [Int.toNat_of_nonneg ht1]
    push_cast
    omega

theorem exists_params {k w : ℤ} (hkw : Even (k + w)) (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ)) (hm₀' : 0 < m₀)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∃ r a b d : ℕ, Odd r ∧ 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (d : ℤ) - (k + (r : ℤ) * w) ∧ d < r * m₀ ∧ (n : ℝ) < r * δ := by

  obtain ⟨R₁, hR₁⟩ := exists_nat_gt ((n : ℝ) / δ)
  let R : ℕ := max R₁ (Int.toNat (k + 16))
  let r : ℕ := 2 * R + 1
  have hrodd : Odd r := ⟨R, rfl⟩
  have hRr : R ≤ r := by simp only [r]; omega
  have hrR₁ : R₁ ≤ r := (le_max_left _ _).trans hRr
  have hrk : k + 16 ≤ (r : ℤ) := by
    have h1 : k + 16 ≤ ((Int.toNat (k + 16) : ℕ) : ℤ) := Int.self_le_toNat (k + 16)
    have h2 : (Int.toNat (k + 16) : ℤ) ≤ (R : ℤ) := by exact_mod_cast le_max_right R₁ (Int.toNat (k + 16))
    have h3 : (R : ℤ) ≤ (r : ℤ) := by simp only [r]; push_cast; omega
    omega
  have hrδ : (n : ℝ) < r * δ := by
    have : (n : ℝ) / δ < r := hR₁.trans_le (by exact_mod_cast hrR₁)
    rwa [div_lt_iff₀ hδ] at this

  have hrm : 1 ≤ r * m₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  let d : ℕ := r * m₀ - 1
  have hd : d < r * m₀ := Nat.sub_one_lt_of_le hrm le_rfl
  have hdZ : (d : ℤ) = (r : ℤ) * m₀ - 1 := by
    simp only [d]; rw [Nat.cast_sub hrm]; push_cast; ring

  have hN4 : 4 ≤ 12 * (d : ℤ) - (k + (r : ℤ) * w) := by
    rw [hdZ]
    have hc : 1 ≤ 12 * (m₀ : ℤ) - w := by omega
    have hr0 : (0 : ℤ) ≤ r := by positivity
    nlinarith
  have hNeven : Even (12 * (d : ℤ) - (k + (r : ℤ) * w)) := by
    obtain ⟨R', hR'⟩ := hrodd
    have hr' : (r : ℤ) = 2 * R' + 1 := by exact_mod_cast hR'
    rw [hr']
    obtain ⟨s, hs⟩ := hkw
    refine ⟨6 * (d : ℤ) - s - R' * w, ?_⟩
    linear_combination -hs
  obtain ⟨a, b, hab⟩ := exists_four_mul_add_six_mul hNeven hN4
  exact ⟨r, a, b, d, ⟨R, rfl⟩, hab, hd, hrδ⟩

open Filter Asymptotics

theorem mdifferentiable_slash {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {κ : ℤ}
    (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ) (x : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑X : UpperHalfPlane → ℂ) ∣[κ] (x : GL (Fin 2) ℝ)) :=
  (ModularFormClass.holo X).slash κ _

theorem isBoundedAtImInfty_slash {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {κ : ℤ}
    (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ) (x : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty ((⇑X : UpperHalfPlane → ℂ) ∣[κ] (x : GL (Fin 2) ℝ)) := by
  have h := ModularFormClass.bdd_at_infty_slash X x
  rwa [ModularForm.SL_slash] at h

theorem denom_T_zpow (j : ℤ) (τ : UpperHalfPlane) : denom (ModularGroup.T ^ j : SL(2, ℤ)) τ = 1 := by
  rw [ModularGroup.denom_apply]
  simp [ModularGroup.coe_T_zpow]

theorem slash_T_zpow_apply (X : UpperHalfPlane → ℂ) (κ : ℤ) (j : ℤ) (τ : UpperHalfPlane) :
    (X ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ = X ((j : ℝ) +ᵥ τ) := by
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, modular_T_zpow_smul, denom_T_zpow, one_zpow, mul_one]

theorem slash_T_pow_apply (X : UpperHalfPlane → ℂ) (κ : ℤ) (j : ℕ) (τ : UpperHalfPlane) :
    (X ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ = X (((j : ℕ) : ℝ) +ᵥ τ) := by
  have h := slash_T_zpow_apply X κ (j : ℤ) τ
  rwa [zpow_natCast, Int.cast_natCast] at h

theorem periodic_comp_ofComplex_of_slash_T_pow_eq (f : UpperHalfPlane → ℂ) (κ : ℤ) (m : ℕ)
    (hf : f ∣[κ] ((ModularGroup.T ^ m : SL(2, ℤ)) : GL (Fin 2) ℝ) = f) :
    Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (m : ℝ) := by
  intro w
  by_cases hw : 0 < Complex.im w
  · have hw' : 0 < Complex.im (w + (m : ℝ)) := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw']
    have h := congrFun hf ⟨w, hw⟩
    rw [slash_T_pow_apply] at h
    convert h using 2 <;> try rfl
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_vadd, add_comm]
  · have hw' : ¬ 0 < Complex.im (w + (m : ℝ)) := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hw),
      ofComplex_apply_of_im_nonpos (not_lt.mp hw')]

theorem slash_S_slash_T_eq {Γ : Subgroup SL(2, ℤ)} {κ : ℤ} (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ) :
    ((⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[κ]
        ((ModularGroup.T ^ 1 : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  have hmem : (((ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∈
      (Γ : Subgroup (GL (Fin 2) ℝ)) := Subgroup.mem_map_of_mem _ hS
  have heq : (ModularGroup.S : SL(2, ℤ)) * ModularGroup.T ^ 1 =
      (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) * ModularGroup.S := by
    rw [pow_one, inv_mul_cancel_right]
  rw [← ModularForm.SL_slash, ← ModularForm.SL_slash, ← SlashAction.slash_mul, heq, SlashAction.slash_mul,
    ModularForm.SL_slash _ (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹),
    SlashInvariantForm.slash_action_eqn X _ hmem]

section G4

variable (φ ψ : UpperHalfPlane → ℂ)

theorem periodic_pow (hψp : Function.Periodic (ψ ∘ UpperHalfPlane.ofComplex) (1 : ℝ)) (r : ℕ) :
    Function.Periodic ((ψ ^ r) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
  intro w
  have := hψp w
  simp only [Function.comp_apply, Pi.pow_apply] at this ⊢
  rw [this]

theorem mdifferentiable_pow (hψh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ) (r : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ψ ^ r) := by
  induction r with
  | zero => (simp; exact mdifferentiable_const (c := (1 : ℂ)))
  | succ r ih => simpa [pow_succ] using ih.mul hψh

theorem isBoundedAtImInfty_pow (hψb : UpperHalfPlane.IsBoundedAtImInfty ψ) (r : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (ψ ^ r) := by
  induction r with
  | zero => (have h__af := (Filter.const_boundedAtFilter UpperHalfPlane.atImInfty (1 : ℂ)); simp at h__af; exact h__af)
  | succ r ih => (have h__af := ih.mul hψb; simp [pow_succ] at h__af ⊢; exact h__af)

theorem qExpansion_one_mul_pow
    (hφp : Function.Periodic (φ ∘ UpperHalfPlane.ofComplex) (1 : ℝ)) (hφh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ)
    (hφb : UpperHalfPlane.IsBoundedAtImInfty φ)
    (hψp : Function.Periodic (ψ ∘ UpperHalfPlane.ofComplex) (1 : ℝ)) (hψh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ)
    (hψb : UpperHalfPlane.IsBoundedAtImInfty ψ) (r : ℕ) :
    UpperHalfPlane.qExpansion 1 (φ * ψ ^ r) = UpperHalfPlane.qExpansion 1 φ * UpperHalfPlane.qExpansion 1 ψ ^ r := by
  have hψr : ∀ r : ℕ, AnalyticAt ℂ (cuspFunction 1 (ψ ^ r)) 0 := fun r =>
    analyticAt_cuspFunction_zero one_pos (periodic_pow ψ hψp r) (mdifferentiable_pow ψ hψh r)
      (isBoundedAtImInfty_pow ψ hψb r)
  have hφa : AnalyticAt ℂ (cuspFunction 1 φ) 0 := analyticAt_cuspFunction_zero one_pos hφp hφh hφb
  have hψa : AnalyticAt ℂ (cuspFunction 1 ψ) 0 := analyticAt_cuspFunction_zero one_pos hψp hψh hψb
  have hpow : ∀ r : ℕ, UpperHalfPlane.qExpansion 1 (ψ ^ r) = UpperHalfPlane.qExpansion 1 ψ ^ r := by
    intro r
    induction r with
    | zero => simp [qExpansion_one]
    | succ r ih => rw [pow_succ, qExpansion_mul (hψr r) hψa, ih, pow_succ]
  rw [qExpansion_mul hφa (hψr r), hpow]

end G4

theorem coeff_pow_eq_zero_of_lt {K : Type*} [CommRing K] (U : PowerSeries K) (m₀ r : ℕ)
    (hU : ∀ i : ℕ, i < m₀ → PowerSeries.coeff i U = 0) (i : ℕ) (hi : i < r * m₀) :
    PowerSeries.coeff i (U ^ r) = 0 := by
  have hdvd : PowerSeries.X ^ m₀ ∣ U := by
    rw [PowerSeries.X_pow_dvd_iff]
    exact hU
  obtain ⟨V, hV⟩ := hdvd
  rw [hV, mul_pow, ← pow_mul, mul_comm m₀ r, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (not_le.mpr hi)]

theorem coeff_pow_mul {K : Type*} [CommRing K] (U : PowerSeries K) (m₀ r : ℕ)
    (hU : ∀ i : ℕ, i < m₀ → PowerSeries.coeff i U = 0) :
    PowerSeries.coeff (r * m₀) (U ^ r) = (PowerSeries.coeff m₀ U) ^ r := by
  have hdvd : PowerSeries.X ^ m₀ ∣ U := by
    rw [PowerSeries.X_pow_dvd_iff]
    exact hU
  obtain ⟨V, hV⟩ := hdvd
  subst hV
  rw [mul_pow, ← pow_mul, mul_comm m₀ r, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff]

theorem isBigO_mul_pow_exp (g θ : UpperHalfPlane → ℂ) (hg : UpperHalfPlane.IsBoundedAtImInfty g) (c : ℝ)
    (hθ : θ =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * c) * τ.im)) (r : ℕ) :
    (g * θ ^ r) =O[UpperHalfPlane.atImInfty]
      fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((r : ℝ) * c)) * τ.im) := by
  have h1 : (θ ^ r) =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * c) * τ.im) ^ r := by
    have h__af := hθ.pow r
    simp at h__af ⊢
    exact h__af
  have hg' : g =O[UpperHalfPlane.atImInfty] fun _ : UpperHalfPlane => (1 : ℝ) := hg
  have h2 : (g * θ ^ r) =O[UpperHalfPlane.atImInfty]
      fun τ : UpperHalfPlane => (1 : ℝ) * Real.exp (-(2 * Real.pi * c) * τ.im) ^ r := hg'.mul h1
  refine h2.trans (Asymptotics.isBigO_of_le _ fun τ => ?_)
  rw [one_mul, ← Real.exp_nat_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  apply le_of_eq
  congr 1
  ring

section G7

variable {ι : Type*} (s : Finset ι) (f : ι → UpperHalfPlane → ℂ) (h : ℝ)

theorem periodic_sum (hp : ∀ i ∈ s, Function.Periodic (f i ∘ UpperHalfPlane.ofComplex) h) :
    Function.Periodic ((∑ i ∈ s, f i) ∘ UpperHalfPlane.ofComplex) h := by
  intro w
  simp only [Function.comp_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hp i hi w

theorem mdifferentiable_sum (hh : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const (c := (0 : ℂ)))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hh a (Finset.mem_insert_self a s)).add (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

theorem isBoundedAtImInfty_sum (hb : ∀ i ∈ s, UpperHalfPlane.IsBoundedAtImInfty (f i)) :
    UpperHalfPlane.IsBoundedAtImInfty (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (have h__af := (Filter.const_boundedAtFilter UpperHalfPlane.atImInfty (0 : ℂ)); simp at h__af; exact h__af)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hb a (Finset.mem_insert_self a s)).add (ih fun i hi => hb i (Finset.mem_insert_of_mem hi))

theorem qExpansion_sum (hh0 : 0 < h) (hp : ∀ i ∈ s, Function.Periodic (f i ∘ UpperHalfPlane.ofComplex) h)
    (hh : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) (hb : ∀ i ∈ s, UpperHalfPlane.IsBoundedAtImInfty (f i)) :
    UpperHalfPlane.qExpansion h (∑ i ∈ s, f i) = ∑ i ∈ s, UpperHalfPlane.qExpansion h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
      have hp' : ∀ i ∈ s, Function.Periodic (f i ∘ UpperHalfPlane.ofComplex) h := fun i hi => hp i (Finset.mem_insert_of_mem hi)
      have hh' : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) := fun i hi => hh i (Finset.mem_insert_of_mem hi)
      have hb' : ∀ i ∈ s, UpperHalfPlane.IsBoundedAtImInfty (f i) := fun i hi => hb i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        qExpansion_add (analyticAt_cuspFunction_zero hh0 (hp a (Finset.mem_insert_self a s))
          (hh a (Finset.mem_insert_self a s)) (hb a (Finset.mem_insert_self a s)))
          (analyticAt_cuspFunction_zero hh0 (periodic_sum s f h hp') (mdifferentiable_sum s f hh')
            (isBoundedAtImInfty_sum s f hb')),
        ih hp' hh' hb']

end G7

private theorem _root_.TRMain.denom_neg_SL (γ : SL(2, ℤ)) (τ : UpperHalfPlane) : denom (-γ : SL(2, ℤ)) τ = -denom γ τ := by
  simp only [ModularGroup.denom_apply, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
  ring

p2m_export "TRMain" "denom_neg_SL"
theorem SL_slash_neg (f : UpperHalfPlane → ℂ) {κ : ℤ} (hκ : Even κ) (γ : SL(2, ℤ)) :
    f ∣[κ] ((-γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = f ∣[κ] (γ : GL (Fin 2) ℝ) := by
  funext τ
  rw [← ModularForm.SL_slash, ← ModularForm.SL_slash, ModularForm.SL_slash_apply, ModularForm.SL_slash_apply,
    ModularGroup.SL_neg_smul, denom_neg_SL, (Even.neg hκ).neg_zpow]

theorem slash_T_pow_eq_of_pm_mem {Γ : Subgroup SL(2, ℤ)} {κ : ℤ} (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    (hκ : Even κ) (m : ℕ) (hm : ModularGroup.T ^ m ∈ Γ ∨ -(ModularGroup.T ^ m) ∈ Γ) :
    (⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ m : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑X := by
  rcases hm with hm | hm
  · exact SlashInvariantForm.slash_action_eqn X _ (Subgroup.mem_map_of_mem _ hm)
  · rw [← SL_slash_neg (⇑X) hκ]
    exact SlashInvariantForm.slash_action_eqn X _ (Subgroup.mem_map_of_mem _ hm)

theorem periodic_of_pm_mem {Γ : Subgroup SL(2, ℤ)} {κ : ℤ} (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    (hκ : Even κ) (m : ℕ) (hm : ModularGroup.T ^ m ∈ Γ ∨ -(ModularGroup.T ^ m) ∈ Γ) :
    Function.Periodic ((⇑X : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (m : ℝ) :=
  periodic_comp_ofComplex_of_slash_T_pow_eq _ κ m (slash_T_pow_eq_of_pm_mem X hκ m hm)

theorem analyticAt_cuspFunction_one_zero (f : UpperHalfPlane → ℂ)
    (hp : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ)) (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hb : UpperHalfPlane.IsBoundedAtImInfty f) : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 :=
  analyticAt_cuspFunction_zero one_pos hp hh hb

theorem coeff_qExpansion_one_sum_slash_T_pow {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) {κ : ℤ} (hκ : Even κ) (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    (h₀ : ℕ) (hh₀ : 0 < h₀) (hh₀h : h₀ ∣ h) (hT₀ : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ) (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ∑ j ∈ Finset.range h₀, ((⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ)) =
      (h₀ : ℂ) * PowerSeries.coeff (h * i) (UpperHalfPlane.qExpansion (h : ℝ) (⇑X : UpperHalfPlane → ℂ)) := by
  have hper₀ : Function.Periodic ((⇑X : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (h₀ : ℝ) :=
    periodic_of_pm_mem X hκ h₀ hT₀
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑X : UpperHalfPlane → ℂ) := ModularFormClass.holo X
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty (⇑X : UpperHalfPlane → ℂ) := ModularFormClass.bdd_at_infty X
  have hfun : (fun τ : UpperHalfPlane =>
      ∑ j ∈ Finset.range h₀, ((⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ) =
      fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀, (⇑X : UpperHalfPlane → ℂ) (((j : ℕ) : ℝ) +ᵥ τ) := by
    funext τ
    exact Finset.sum_congr rfl fun j _ => slash_T_pow_apply _ _ _ _
  rw [hfun, UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff (⇑X) h₀ hh₀ hper₀ hhol hbdd i]
  congr 1
  obtain ⟨m', hm'⟩ := hh₀h
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hm'; omega
  have hw := UpperHalfPlane.qExpansion_coeff_mul_width (⇑X) (h₀ : ℝ) (by exact_mod_cast hh₀) hper₀ hhol hbdd
    m' hm'pos (h * i)
  have hcast : ((m' : ℝ) * (h₀ : ℝ)) = (h : ℝ) := by rw [hm']; push_cast; ring
  rw [hcast] at hw
  rw [hw, if_pos ⟨h₀ * i, by rw [hm']; ring⟩]
  congr 1
  rw [hm', show h₀ * m' * i = m' * (h₀ * i) by ring, Nat.mul_div_cancel_left _ hm'pos]

theorem sum_slash_T_pow_slash_T_eq {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) {κ : ℤ} (hκ : Even κ) (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    (h₀ : ℕ) (hh₀ : 0 < h₀) (hh₀h : h₀ ∣ h) (hT₀ : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ) :
    (fun τ : UpperHalfPlane =>
        ∑ j ∈ Finset.range h₀, ((⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ) ∣[κ]
        ((ModularGroup.T ^ 1 : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      fun τ : UpperHalfPlane =>
        ∑ j ∈ Finset.range h₀, ((⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ := by
  funext τ
  rw [slash_T_pow_apply]
  simp only [slash_T_pow_apply]

  have hshift : ∀ j : ℕ, (⇑X : UpperHalfPlane → ℂ) (((j : ℕ) : ℝ) +ᵥ ((((1 : ℕ) : ℕ) : ℝ) +ᵥ τ)) =
      (⇑X : UpperHalfPlane → ℂ) ((((j + 1 : ℕ) : ℕ) : ℝ) +ᵥ τ) := fun j => by
    rw [vadd_vadd]
    congr 1
    push_cast
    ring
  simp only [hshift]
  have hper : (⇑X : UpperHalfPlane → ℂ) ((((h₀ : ℕ) : ℕ) : ℝ) +ᵥ τ) = (⇑X : UpperHalfPlane → ℂ) ((((0 : ℕ) : ℕ) : ℝ) +ᵥ τ) := by
    rw [← slash_T_pow_apply (⇑X) κ h₀ τ, slash_T_pow_eq_of_pm_mem X hκ h₀ hT₀]
    simp
  have h1 := Finset.sum_range_succ' (fun j : ℕ => (⇑X : UpperHalfPlane → ℂ) (((j : ℕ) : ℝ) +ᵥ τ)) h₀
  have h2 := Finset.sum_range_succ (fun j : ℕ => (⇑X : UpperHalfPlane → ℂ) (((j : ℕ) : ℝ) +ᵥ τ)) h₀
  have h3 : ∑ x ∈ Finset.range h₀, (⇑X : UpperHalfPlane → ℂ) (((x + 1 : ℕ) : ℝ) +ᵥ τ) =
      ∑ x ∈ Finset.range h₀, (⇑X : UpperHalfPlane → ℂ) (((x : ℕ) : ℝ) +ᵥ τ) +
        (⇑X : UpperHalfPlane → ℂ) (((h₀ : ℕ) : ℝ) +ᵥ τ) - (⇑X : UpperHalfPlane → ℂ) (((0 : ℕ) : ℝ) +ᵥ τ) := by
    linear_combination h2 - h1
  rw [h3, hper, add_sub_cancel_right]

theorem natCast_mem_strictPeriods (Γ : Subgroup SL(2, ℤ)) (h : ℕ) (hT : ModularGroup.T ^ h ∈ Γ) :
    (h : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT' : ModularGroup.T ^ (h : ℤ) ∈ Γ := by exact_mod_cast hT
  simp only [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  refine ⟨ModularGroup.T ^ (h : ℤ), hT', ?_⟩
  rw [ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coeff_mul_mem {R : Subring ℂ} {P Q : PowerSeries ℂ} (hP : ∀ i, PowerSeries.coeff i P ∈ R)
    (hQ : ∀ i, PowerSeries.coeff i Q ∈ R) (i : ℕ) : PowerSeries.coeff i (P * Q) ∈ R := by
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem fun p _ => R.mul_mem (hP _) (hQ _)

theorem coeff_pow_mem {R : Subring ℂ} {P : PowerSeries ℂ} (hP : ∀ i, PowerSeries.coeff i P ∈ R) (r : ℕ) (i : ℕ) :
    PowerSeries.coeff i (P ^ r) ∈ R := by
  induction r generalizing i with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> simp [R.one_mem, R.zero_mem]
  | succ r ih => rw [pow_succ]; exact coeff_mul_mem ih hP i

theorem slash_T_pow_eq_of_mem_or_neg_mem {Γ : Subgroup SL(2, ℤ)} {κ : ℤ} (hκ : Even κ)
    (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ) (h₀ : ℕ)
    (hT₀ : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ) :
    (⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ h₀ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑X := by
  rcases hT₀ with h | h
  · exact SlashInvariantForm.slash_action_eqn X _ (Subgroup.mem_map_of_mem _ h)
  ·
    have hmem : ((-(ModularGroup.T ^ h₀) : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
      Subgroup.mem_map_of_mem _ h
    have key := SlashInvariantForm.slash_action_eqn X _ hmem
    funext τ
    have h1 := congrFun key τ
    rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, TRAssembly.denom_neg_SL,
      Even.neg_zpow (Even.neg hκ), ← ModularForm.SL_slash_apply] at h1
    rw [← ModularForm.SL_slash]
    exact h1

theorem pow_slash_SL2 (w : ℤ) (A : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) (r : ℕ) :
    (f ^ r) ∣[(r : ℤ) * w] A = (f ∣[w] A) ^ r := by
  induction r with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    funext τ
    rw [ModularForm.SL_slash_apply]; simp
  | succ r ih =>
    rw [pow_succ, pow_succ, show ((r + 1 : ℕ) : ℤ) * w = (r : ℤ) * w + w by push_cast; ring,
      ModularForm.mul_slash_SL2, ih]

theorem mdifferentiable_finset_sum {ι : Type*} (t : Finset ι) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ t, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => ∑ i ∈ t, f i τ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact mdifferentiable_const
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isBoundedAtImInfty_finset_sum {ι : Type*} (t : Finset ι) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ t, UpperHalfPlane.IsBoundedAtImInfty (f i)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ => ∑ i ∈ t, f i τ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact UpperHalfPlane.atImInfty.const_boundedAtFilter 0
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem T_pow_injective : Function.Injective fun j : ℕ => (ModularGroup.T ^ j : SL(2, ℤ)) := by
  intro i j hij
  have := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) hij
  simp only at this
  rw [← zpow_natCast, ← zpow_natCast, ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow] at this
  simpa using this

theorem S_ne_T_pow (j : ℕ) : (ModularGroup.S : SL(2, ℤ)) ≠ ModularGroup.T ^ j := by
  intro hij
  have := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) hij
  rw [← zpow_natCast, ModularGroup.coe_T_zpow, ModularGroup.coe_S] at this
  simp at this

theorem sum_transversal_split {M : Type*} [AddCommGroup M] (s : Finset SL(2, ℤ)) (h₀ : ℕ)
    (hTs : ∀ j : ℕ, j < h₀ → ModularGroup.T ^ j ∈ s) (hSs : ModularGroup.S ∈ s) (φ : SL(2, ℤ) → M) :
    ∑ x ∈ s, φ x = (∑ j ∈ Finset.range h₀, φ (ModularGroup.T ^ j)) + φ ModularGroup.S +
      ∑ x ∈ s.filter (fun x => (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) ∧ x ≠ ModularGroup.S), φ x := by
  classical

  set A : Finset SL(2, ℤ) := (Finset.range h₀).image fun j => ModularGroup.T ^ j with hA
  set C : Finset SL(2, ℤ) := s.filter (fun x => (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) ∧ x ≠ ModularGroup.S) with hC
  have hAs : A ⊆ s := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hTs j (Finset.mem_range.mp hj)
  have hs : s = (insert ModularGroup.S A) ∪ C := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, hC]
    constructor
    · intro hx
      by_cases h1 : x = ModularGroup.S
      · exact Or.inl (Or.inl h1)
      by_cases h2 : ∃ j : ℕ, j < h₀ ∧ x = ModularGroup.T ^ j
      · obtain ⟨j, hj, rfl⟩ := h2
        exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩))
      · push Not at h2
        exact Or.inr ⟨hx, fun j hj => h2 j hj, h1⟩
    · rintro ((rfl | hx) | ⟨hx, -⟩)
      · exact hSs
      · exact hAs hx
      · exact hx
  have hdisj : Disjoint (insert ModularGroup.S A) C := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    rw [Finset.mem_filter] at hxC
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hxC.2.2 rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hxC.2.1 j (Finset.mem_range.mp hj) rfl
  have hSA : ModularGroup.S ∉ A := by
    intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact S_ne_T_pow j hj.symm
  rw [hs, Finset.sum_union hdisj, Finset.sum_insert hSA, hA,
    Finset.sum_image fun i _ j _ hij => T_pow_injective hij]
  abel

end TRMain

open scoped MatrixGroups ModularForm Manifold in
open UpperHalfPlane TRMain in
set_option maxHeartbeats 3200000 in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ} (hkw : Even (k + w))
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ))
    (hΘS₀ : ∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0)
    (hΘS₁ : ∃ v ∈ R, v * (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1)
    (hΘS : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im))
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by
  classical

  have hm₀' : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h0 | h0
    · exfalso
      subst h0
      have hw : w < 0 := by simpa using hm₀
      have hΘ0 : Θ = 0 := ModularForm.isZero_of_neg_weight hw Θ
      obtain ⟨v, -, hv⟩ := hΘS₁
      have hz : ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) = 0 := by
        rw [hΘ0, ModularForm.coe_zero, SlashAction.zero_slash]
      rw [hz, UpperHalfPlane.qExpansion_zero, map_zero, mul_zero] at hv
      exact zero_ne_one hv
    · exact h0

  by_cases hdeg : ∃ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∈ Γ ∨ -(ModularGroup.S * ModularGroup.T ^ j) ∈ Γ
  · exact TRAssembly.coeff_mem_of_S_mul_T_zpow_mem Γ h hh hT hS R hkw G hG Θ hΘ m₀ hm₀ hΘS₀ hΘS₁ hΘS δ hδ
      hdecay hdeg n
  push Not at hdeg

  obtain ⟨h₀, hh₀, hh₀h, hT₀, hmin⟩ := TRAssembly.exists_width Γ h hh hT
  obtain ⟨s, hcover, hsep, hTs, hSs, hrest⟩ :=
    CongruenceSubgroup.exists_finset_transversal_adapted_T_S Γ (fun j => hdeg j) h₀ hh₀ hT₀ hmin
  obtain ⟨r, a, b, d, hrodd, hwt, hd, hrδ⟩ := exists_params hkw m₀ hm₀ hm₀' δ hδ n
  have hev : Even (k + (r : ℤ) * w) := by
    obtain ⟨t, ht⟩ := hrodd
    have : k + (r : ℤ) * w = (k + w) + 2 * ((t : ℤ) * w) := by rw [ht]; push_cast; ring
    rw [this]
    exact hkw.add (even_two_mul _)

  let X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k + (r : ℤ) * w) := (G.mul (Θ.pow r)).mcast (by ring)
  have hXcoe : (⇑X : UpperHalfPlane → ℂ) = ⇑G * (⇑Θ) ^ r := by
    simp [X, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
  have hXslash : ∀ x : SL(2, ℤ), (⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ) =
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] (x : GL (Fin 2) ℝ)) * ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (x : GL (Fin 2) ℝ)) ^ r := by
    intro x
    rw [hXcoe, ← ModularForm.SL_slash, ModularForm.mul_slash_SL2, pow_slash_SL2, ModularForm.SL_slash,
      ModularForm.SL_slash]

  have hhR : (h : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := natCast_mem_strictPeriods Γ h hT
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hXR : ∀ m : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑X : UpperHalfPlane → ℂ)).coeff m ∈ R := by
    intro m
    have e : UpperHalfPlane.qExpansion (h : ℝ) (⇑X : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ) *
          UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ) ^ r := by
      show UpperHalfPlane.qExpansion (h : ℝ) ⇑((G.mul (Θ.pow r)).mcast _) = _
      rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul hh' hhR, ModularForm.qExpansion_pow hh' hhR]
    rw [e]
    exact coeff_mul_mem hG (coeff_pow_mem hΘ r) m

  obtain ⟨F, hF⟩ := ModularForm.exists_levelOne_coe_eq_sum_slash Γ hev X s hcover hsep
  set gS : UpperHalfPlane → ℂ := (⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) with hgS
  set θS : UpperHalfPlane → ℂ := (⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) with hθS
  set FA : UpperHalfPlane → ℂ := fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀,
    ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ with hFA
  set FS : UpperHalfPlane → ℂ := (⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)
    with hFS
  set C : Finset SL(2, ℤ) := s.filter (fun x => (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) ∧ x ≠ ModularGroup.S)
    with hC
  set FC : UpperHalfPlane → ℂ := fun τ : UpperHalfPlane => ∑ x ∈ C,
    ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) τ with hFC
  have hsplit : (⇑F : UpperHalfPlane → ℂ) = FA + FS + FC := by
    rw [hF, sum_transversal_split s h₀ hTs hSs _, Finset.sum_fn, Finset.sum_fn]
  have hFSeq : FS = gS * θS ^ r := hXslash ModularGroup.S

  have h1SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hXh : ∀ x : SL(2, ℤ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) :=
    fun x => mdifferentiable_slash X x
  have hXb : ∀ x : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) :=
    fun x => isBoundedAtImInfty_slash X x
  have hgSh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) gS := mdifferentiable_slash G _
  have hgSb : UpperHalfPlane.IsBoundedAtImInfty gS := isBoundedAtImInfty_slash G _
  have hθSh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) θS := mdifferentiable_slash Θ _
  have hθSb : UpperHalfPlane.IsBoundedAtImInfty θS := isBoundedAtImInfty_slash Θ _
  have hgSp : Function.Periodic (gS ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq gS k 1 (slash_S_slash_T_eq G hS)
    rwa [Nat.cast_one] at this
  have hθSp : Function.Periodic (θS ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq θS w 1 (slash_S_slash_T_eq Θ hS)
    rwa [Nat.cast_one] at this
  have hFSp : Function.Periodic (FS ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq FS (k + (r : ℤ) * w) 1 (slash_S_slash_T_eq X hS)
    rwa [Nat.cast_one] at this
  have hFSh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) FS := hXh _
  have hFSb : UpperHalfPlane.IsBoundedAtImInfty FS := hXb _
  have hFAh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) FA := mdifferentiable_finset_sum _ _ fun j _ => hXh _
  have hFAb : UpperHalfPlane.IsBoundedAtImInfty FA := isBoundedAtImInfty_finset_sum _ _ fun j _ => hXb _
  have hFCh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) FC := mdifferentiable_finset_sum _ _ fun x _ => hXh _
  have hFCb : UpperHalfPlane.IsBoundedAtImInfty FC := isBoundedAtImInfty_finset_sum _ _ fun x _ => hXb _

  have hXT₀ : (⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] ((ModularGroup.T ^ h₀ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑X :=
    slash_T_pow_eq_of_pm_mem X hev h₀ hT₀
  have hFAT : FA ∣[k + (r : ℤ) * w] ((ModularGroup.T ^ 1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = FA :=
    sum_slash_T_pow_slash_T_eq h hh hT hev X h₀ hh₀ hh₀h hT₀
  have hFAp : Function.Periodic (FA ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq FA (k + (r : ℤ) * w) 1 hFAT
    rwa [Nat.cast_one] at this
  have hFp : Function.Periodic ((⇑F : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex F h1SL
  have hFCeq : FC = (⇑F : UpperHalfPlane → ℂ) - FA - FS := by rw [hsplit]; abel
  have hFCp : Function.Periodic (FC ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    rw [hFCeq]
    exact (hFp.sub hFAp).sub hFSp

  have hqF : UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 FA + UpperHalfPlane.qExpansion 1 FS + UpperHalfPlane.qExpansion 1 FC := by
    rw [hsplit, UpperHalfPlane.qExpansion_add, UpperHalfPlane.qExpansion_add]
    · exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hFAp hFAh hFAb
    · exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hFSp hFSh hFSb
    · refine UpperHalfPlane.analyticAt_cuspFunction_zero one_pos (hFAp.add hFSp) (hFAh.add hFSh) (hFAb.add hFSb)
    · exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hFCp hFCh hFCb
  have hA : ∀ i : ℕ, (UpperHalfPlane.qExpansion 1 FA).coeff i ∈ R := by
    intro i
    have e := coeff_qExpansion_one_sum_slash_T_pow h hh hT hev X h₀ hh₀ hh₀h hT₀ i
    rw [e]
    exact R.mul_mem (natCast_mem R h₀) (hXR _)
  have hSq : UpperHalfPlane.qExpansion 1 FS = UpperHalfPlane.qExpansion 1 gS * UpperHalfPlane.qExpansion 1 θS ^ r := by
    rw [hFSeq]
    exact qExpansion_one_mul_pow gS θS hgSp hgSh hgSb hθSp hθSh hθSb r
  have hS0 : ∀ i : ℕ, i < r * m₀ → (UpperHalfPlane.qExpansion 1 FS).coeff i = 0 := by
    intro i hi
    rw [hSq, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp2 : p.2 ≤ i := Finset.HasAntidiagonal.antidiagonal.snd_le hp
    rw [coeff_pow_eq_zero_of_lt _ m₀ r hΘS₀ p.2 (lt_of_le_of_lt hp2 hi), mul_zero]
  have hCO : FC =O[UpperHalfPlane.atImInfty]
      fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((r : ℝ) * ((m₀ : ℝ) + δ))) * τ.im) := by
    refine Asymptotics.IsBigO.fun_sum fun x hx => ?_
    rw [Finset.mem_filter] at hx
    rw [hXslash x]
    exact isBigO_mul_pow_exp _ _ (isBoundedAtImInfty_slash G x) _ (hdecay x (hrest x hx.1 hx.2.1 hx.2.2).1
      (hrest x hx.1 hx.2.1 hx.2.2).2) r
  have hC0 : ∀ i : ℕ, (i : ℝ) < r * ((m₀ : ℝ) + δ) → (UpperHalfPlane.qExpansion 1 FC).coeff i = 0 :=
    fun i hi => UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg FC hFCp hFCh hFCb _ hCO i hi

  obtain ⟨E, P, hP, hP1⟩ := ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one a b _ hwt
  let H : ModularForm 𝒮ℒ (12 * (d : ℤ)) := (F.mul E).mcast (by ring)
  have hqH : UpperHalfPlane.qExpansion 1 (⇑H : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ) * UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) := by
    show UpperHalfPlane.qExpansion 1 ⇑((F.mul E).mcast _) = _
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos h1SL]
  have hER : ∀ j : ℕ, (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff j ∈ R := fun j => by
    rw [← hP, PowerSeries.coeff_map]
    exact intCast_mem R _
  have hrm : (r : ℝ) * m₀ ≤ r * ((m₀ : ℝ) + δ) := by nlinarith [hδ.le, (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hHint : ∀ m : ℕ, m ≤ d → (UpperHalfPlane.qExpansion 1 (⇑H : UpperHalfPlane → ℂ)).coeff m ∈ R := by
    intro m hm
    rw [hqH, PowerSeries.coeff_mul]
    refine R.sum_mem fun p hp => R.mul_mem ?_ (hER _)
    have hp1 : p.1 ≤ m := Finset.HasAntidiagonal.antidiagonal.fst_le hp
    have hlt : p.1 < r * m₀ := lt_of_le_of_lt (hp1.trans hm) hd
    have hlt' : (p.1 : ℝ) < r * ((m₀ : ℝ) + δ) := lt_of_lt_of_le (by exact_mod_cast hlt) hrm
    rw [hqF, map_add, map_add, hS0 _ hlt, hC0 _ hlt', add_zero, add_zero]
    exact hA _
  have hHall : ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 (⇑H : UpperHalfPlane → ℂ)).coeff m ∈ R :=
    fun m => ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem d H R hHint m

  have hFall : ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff m ∈ R := by
    have hPu : IsUnit P := by
      rw [PowerSeries.isUnit_iff_constantCoeff, hP1]
      exact isUnit_one
    obtain ⟨Q, hQ⟩ : ∃ Q : PowerSeries ℤ, P * Q = 1 := ⟨↑hPu.unit⁻¹, hPu.mul_val_inv⟩
    have hQm : UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) * Q.map (Int.castRingHom ℂ) = 1 := by
      rw [← hP, ← map_mul, hQ, map_one]
    have e : UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (⇑H : UpperHalfPlane → ℂ) * Q.map (Int.castRingHom ℂ) := by
      rw [hqH, mul_assoc, hQm, mul_one]
    intro m
    rw [e]
    exact coeff_mul_mem hHall (fun j => by rw [PowerSeries.coeff_map]; exact intCast_mem R _) m

  have hFSR : ∀ i : ℕ, (i : ℝ) < r * ((m₀ : ℝ) + δ) → (UpperHalfPlane.qExpansion 1 FS).coeff i ∈ R := by
    intro i hi
    have := congrArg (PowerSeries.coeff i) hqF
    rw [map_add, map_add, hC0 i hi, add_zero] at this
    have e : (UpperHalfPlane.qExpansion 1 FS).coeff i =
        (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff i - (UpperHalfPlane.qExpansion 1 FA).coeff i := by
      rw [this]; ring
    rw [e]
    exact R.sub_mem (hFall i) (hA i)

  obtain ⟨v, hvR, hv⟩ := hΘS₁
  refine PowerSeries.coeff_mem_subring_of_coeff_mul_mem R (UpperHalfPlane.qExpansion 1 gS)
    (UpperHalfPlane.qExpansion 1 θS ^ r) (r * m₀) ⌈(r : ℝ) * ((m₀ : ℝ) + δ)⌉₊ ?_ ?_ ?_ ?_ n ?_
  · exact fun i hi => coeff_pow_eq_zero_of_lt _ m₀ r hΘS₀ i hi
  · refine ⟨v ^ r, R.pow_mem hvR r, ?_⟩
    rw [coeff_pow_mul _ m₀ r hΘS₀, ← mul_pow, hv, one_pow]
  · exact fun i => coeff_pow_mem hΘS r i
  · intro i hi
    rw [← hSq]
    exact hFSR i (Nat.lt_ceil.mp hi)
  · rw [Nat.lt_ceil]
    push_cast
    nlinarith [hrδ]

#print axioms solution

end S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary
end P2MW
export P2MW.S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary (solution)
