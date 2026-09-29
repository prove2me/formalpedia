-- Prove2me | solution 1 for ModularCurve.exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7aa8a405-c2c9-526c-9ee1-6ced7aac9757

import Mathlib
import Theorems.Thm_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace GammaEvenRecip

abbrev GamR (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Δ" => ModularForm.discriminant

def IsRat (P : PowerSeries ℂ) : Prop := ∀ n, ∃ r : ℚ, P.coeff n = (r : ℂ)

theorem map_map' {A B C : Type*} [Semiring A] [Semiring B] [Semiring C] (f : A →+* B) (g : B →+* C)
    (R : PowerSeries A) : (R.map f).map g = R.map (g.comp f) := by
  rw [PowerSeries.map_comp]; rfl

theorem isRat_iff_exists_map {P : PowerSeries ℂ} :
    IsRat P ↔ ∃ R : PowerSeries ℚ, R.map (algebraMap ℚ ℂ) = P := by
  constructor
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  · rintro ⟨R, rfl⟩ n
    exact ⟨PowerSeries.coeff n R, by rw [PowerSeries.coeff_map]; rfl⟩

theorem IsRat.mul {P P' : PowerSeries ℂ} (h : IsRat P) (h' : IsRat P') : IsRat (P * P') := by
  rw [isRat_iff_exists_map] at h h' ⊢
  obtain ⟨R, rfl⟩ := h
  obtain ⟨R', rfl⟩ := h'
  exact ⟨R * R', by rw [map_mul]⟩

theorem IsRat.pow {P : PowerSeries ℂ} (h : IsRat P) (n : ℕ) : IsRat (P ^ n) := by
  rw [isRat_iff_exists_map] at h ⊢
  obtain ⟨R, rfl⟩ := h
  exact ⟨R ^ n, by rw [map_pow]⟩

section Transport

variable (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ)

def TP (P P' : PowerSeries ℂ) : Prop :=
  ∃ X : PowerSeries ↥K, X.map (algebraMap ↥K ℂ) = P ∧ X.map φ = P'

variable {K φ}

theorem tp_iff {P P' : PowerSeries ℂ} :
    TP K φ P P' ↔ ∀ n, ∃ z : ↥K, (z : ℂ) = P.coeff n ∧ P'.coeff n = φ z := by
  constructor
  · rintro ⟨X, hX, hX'⟩ n
    refine ⟨PowerSeries.coeff n X, ?_, ?_⟩
    · rw [← hX, PowerSeries.coeff_map]; rfl
    · rw [← hX', PowerSeries.coeff_map]
  · intro h
    choose z hz hz' using h
    refine ⟨PowerSeries.mk z, ?_, ?_⟩
    · ext n; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]; exact hz n
    · ext n; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]; exact (hz' n).symm

theorem TP.mul {P P' Q Q' : PowerSeries ℂ} (h : TP K φ P P') (h' : TP K φ Q Q') :
    TP K φ (P * Q) (P' * Q') := by
  obtain ⟨X, rfl, rfl⟩ := h
  obtain ⟨Y, rfl, rfl⟩ := h'
  exact ⟨X * Y, by rw [map_mul], by rw [map_mul]⟩

variable (K φ)

theorem phi_comp_algebraMap : φ.comp (algebraMap ℚ ↥K) = algebraMap ℚ ℂ :=
  RingHom.ext fun r => by rw [eq_ratCast, eq_ratCast]

theorem val_comp_algebraMap : (algebraMap ↥K ℂ).comp (algebraMap ℚ ↥K) = algebraMap ℚ ℂ :=
  RingHom.ext fun r => by rw [eq_ratCast, eq_ratCast]

theorem TP.of_isRat {U : PowerSeries ℂ} (hU : IsRat U) : TP K φ U U := by
  obtain ⟨R, rfl⟩ := isRat_iff_exists_map.mp hU
  refine ⟨R.map (algebraMap ℚ ↥K), ?_, ?_⟩
  · rw [map_map', val_comp_algebraMap]
  · rw [map_map', phi_comp_algebraMap]

variable {K φ}

theorem TP.of_mul_unit {P P' U : PowerSeries ℂ} (h : TP K φ (P * U) (P' * U)) (hU : IsRat U)
    (hU0 : PowerSeries.constantCoeff U = 1) : TP K φ P P' := by
  obtain ⟨R, rfl⟩ := isRat_iff_exists_map.mp hU
  have hR0 : PowerSeries.constantCoeff R = 1 := by
    have : algebraMap ℚ ℂ (PowerSeries.constantCoeff R) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hU0,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    exact (algebraMap ℚ ℂ).injective (by rw [this, map_one])
  have hRunit : IsUnit R := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hR0]; exact isUnit_one
  obtain ⟨v, hv⟩ := hRunit
  obtain ⟨X, hX, hX'⟩ := h

  set vK : (PowerSeries ↥K)ˣ := Units.map (PowerSeries.map (algebraMap ℚ ↥K)).toMonoidHom v with hvK
  have hvKval : ((vK : PowerSeries ↥K)).map (algebraMap ↥K ℂ) = R.map (algebraMap ℚ ℂ) := by
    rw [hvK, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, map_map',
      val_comp_algebraMap]
  have hvKphi : ((vK : PowerSeries ↥K)).map φ = R.map (algebraMap ℚ ℂ) := by
    rw [hvK, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, map_map',
      phi_comp_algebraMap]
  have hinv_val : R.map (algebraMap ℚ ℂ) * ((vK⁻¹ : (PowerSeries ↥K)ˣ) : PowerSeries ↥K).map (algebraMap ↥K ℂ)
      = 1 := by
    rw [← hvKval, ← map_mul, Units.mul_inv, map_one]
  have hinv_phi : R.map (algebraMap ℚ ℂ) * ((vK⁻¹ : (PowerSeries ↥K)ˣ) : PowerSeries ↥K).map φ = 1 := by
    rw [← hvKphi, ← map_mul, Units.mul_inv, map_one]
  refine ⟨X * ↑vK⁻¹, ?_, ?_⟩
  · rw [map_mul, hX, mul_assoc, hinv_val, mul_one]
  · rw [map_mul, hX', mul_assoc, hinv_phi, mul_one]

end Transport

section Level

variable {N : ℕ} {k : ℤ}

theorem natCast_mem_strictPeriods (N : ℕ) : (N : ℝ) ∈ (GamR N).strictPeriods := by
  rw [GamR, CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

theorem natCast_pos [NeZero N] : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem conj_mem_Gamma (α : SL(2, ℤ)) {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma N) :
    α * A * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  (CongruenceSubgroup.Gamma_normal N).conj_mem A hA α

theorem isBoundedAtImInfty_slash [NeZero N] (F : ModularForm (GamR N) k) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑F : ℍ → ℂ) ∣[k] α) := by
  rw [ModularForm.SL_slash, ← OnePoint.isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
  apply F.bdd_at_cusps'
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_iff'.mpr ⟨α, rfl⟩

def slashSL [NeZero N] (α : SL(2, ℤ)) (F : ModularForm (GamR N) k) : ModularForm (GamR N) k where
  toFun := (⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : α * A * α⁻¹ ∈ CongruenceSubgroup.Gamma N := conj_mem_Gamma α hA
    have hGL : (α : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((α * A * α⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (α : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    change ((⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑F : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := F.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (GamR N)).mp hc
    have hc' : IsCusp ((α : GL (Fin 2) ℝ) • c) (GamR N) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨α, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (F.bdd_at_cusps' hc')

theorem coe_slashSL [NeZero N] (α : SL(2, ℤ)) (F : ModularForm (GamR N) k) :
    (⇑(slashSL α F) : ℍ → ℂ) = (⇑F : ℍ → ℂ) ∣[k] α := by
  rw [ModularForm.SL_slash]; rfl

def resSL (N : ℕ) {k' : ℤ} (E : ModularForm 𝒮ℒ k') : ModularForm (GamR N) k' where
  toFun := E
  slash_action_eq' A hA := E.slash_action_eq' A (Subgroup.map_le_range _ _ hA)
  holo' := E.holo'
  bdd_at_cusps' hc := E.bdd_at_cusps' (hc.mono (Subgroup.map_le_range _ _))

@[scoped simp] theorem coe_resSL (N : ℕ) {k' : ℤ} (E : ModularForm 𝒮ℒ k') : (⇑(resSL N E) : ℍ → ℂ) = E := rfl

theorem qParam_one_eq_pow (N : ℕ) [NeZero N] (τ : ℍ) :
    Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem qExpansion_coeff_widthN (N : ℕ) [NeZero N] {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := by simpa using hper.nat_mul N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos (N := N))
    (analyticAt_cuspFunction_zero (natCast_pos (N := N)) hperN hg hbd) hsum n]

theorem isRat_widthN_levelOne (N : ℕ) [NeZero N] {k' : ℤ} (E : ModularForm 𝒮ℒ k')
    (hE : IsRat (qExpansion 1 E)) : IsRat (qExpansion N E) := by
  intro n
  rw [qExpansion_coeff_widthN N (ModularFormClass.holo E) (SlashInvariantFormClass.periodic_comp_ofComplex E
    one_mem_strictPeriods_SL) (ModularFormClass.bdd_at_infty E) n]
  split_ifs
  · exact hE _
  · exact ⟨0, by simp⟩

theorem constantCoeff_widthN_levelOne (N : ℕ) [NeZero N] {k' : ℤ} (E : ModularForm 𝒮ℒ k') :
    PowerSeries.constantCoeff (qExpansion N E) = PowerSeries.constantCoeff (qExpansion 1 E) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    qExpansion_coeff_widthN N (ModularFormClass.holo E) (SlashInvariantFormClass.periodic_comp_ofComplex E
      one_mem_strictPeriods_SL) (ModularFormClass.bdd_at_infty E) 0, if_pos (dvd_zero _), Nat.zero_div]

end Level

section Core

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem disc_smul (α : SL(2, ℤ)) (τ : ℍ) :
    Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

theorem levelOne_smul {k' : ℤ} (E : ModularForm 𝒮ℒ k') (α : SL(2, ℤ)) (τ : ℍ) :
    E (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ k' * E τ := by
  have := SlashInvariantForm.slash_action_eqn'' E (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [← ModularGroup.sl_moeb] at this
  exact this

variable (K : IntermediateField ℚ ℂ)
  (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
  (s : ℕ) (hs : Nat.Coprime s N) (φ : ↥K →+* ℂ)
  (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
    φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
  {γ γ' : SL(2, ℤ)}
  (hγγ' : !![(1 : ZMod N), 0; 0, (s : ZMod N)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)
    = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * !![(1 : ZMod N), 0; 0, (s : ZMod N)])
include hK hs hφ hγγ'

theorem tp_slash_mul (F : ModularForm (GamR N) k) (m : ℕ) {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hkE : k + kE = 12 * m) (hF : IsRat (qExpansion N F)) (hE : IsRat (qExpansion 1 E)) :
    TP K φ (qExpansion N (((⇑F : ℍ → ℂ) ∣[k] γ) * ⇑E)) (qExpansion N (((⇑F : ℍ → ℂ) ∣[k] γ') * ⇑E)) := by

  set H : ℍ → ℂ := (⇑F : ℍ → ℂ) * ⇑E with hH
  set G : ℍ → ℂ := fun τ => H τ / (Δ τ) ^ m with hG
  have hΔ : ∀ τ : ℍ, (Δ τ) ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGΔ : G * Δ ^ m = H := by
    funext τ; simp only [Pi.mul_apply, Pi.pow_apply, hG]; field_simp [hΔ τ]
  have hmdH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := F.holo'.mul E.holo'
  have hmdΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
    rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
  have hmdG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    intro τ
    exact (hmdH τ).div ((hmdΔ τ).pow m) (hΔ τ)

  have hcw : ∀ α : SL(2, ℤ), (fun τ => G (α • τ)) * Δ ^ m = ((⇑F : ℍ → ℂ) ∣[k] α) * ⇑E := by
    intro α
    funext τ
    have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
    simp only [Pi.mul_apply, Pi.pow_apply, hG, hH]
    rw [ModularForm.SL_slash_apply, disc_smul, levelOne_smul E, ModularGroup.sl_moeb]
    have hpow : (denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ) ^ m
        = denom (α : GL (Fin 2) ℝ) τ ^ (k + kE) * (Δ τ) ^ m := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, hkE]
    rw [hpow, zpow_add₀ hd, zpow_neg]
    field_simp [hΔ τ, zpow_ne_zero k hd, zpow_ne_zero kE hd]

  have hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ := by
    intro g hg τ
    have h1 := congrFun (hcw g) τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    have h2 : ((⇑F : ℍ → ℂ) ∣[k] g) = ⇑F := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hg)
    rw [h2] at h1
    have h3 : G τ * Δ τ ^ m = F τ * E τ := by
      have := congrFun hGΔ τ; (simp only [Pi.mul_apply, Pi.pow_apply] at this; exact this)
    exact mul_right_cancel₀ (hΔ τ) (h1.trans h3.symm)

  have hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * Δ ^ m) := by
    intro α
    rw [hcw α]
    exact (isBoundedAtImInfty_slash F α).mul (ModularFormClass.bdd_at_infty E)

  have hrat : ∀ n, ∃ r : ℚ, (qExpansion N (G * Δ ^ m)).coeff n = (r : ℂ) := by
    rw [hGΔ, hH]
    have : qExpansion N ((⇑F : ℍ → ℂ) * ⇑E) = qExpansion N ⇑F * qExpansion N ⇑(resSL N E) := by
      rw [← coe_resSL N E, ModularForm.qExpansion_mul_coe natCast_pos (natCast_mem_strictPeriods N) F
        (resSL N E)]
    rw [this]
    exact hF.mul (isRat_widthN_levelOne N E hE)

  rw [tp_iff]
  intro n
  have key := ModularCurve.exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant N m G hmdG
    hinv hbd hrat K hK s hs φ hφ γ γ' hγγ' n
  rw [hcw γ, hcw γ'] at key
  exact key

end Core

section Even

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem isRat_E4 : IsRat (qExpansion 1 (E₄ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

theorem isRat_E6 : IsRat (qExpansion 1 (E₆ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

theorem constantCoeff_E4 : PowerSeries.constantCoeff (qExpansion 1 (E₄ : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₄,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)]

theorem constantCoeff_E6 : PowerSeries.constantCoeff (qExpansion 1 (E₆ : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₆,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)]

def Eaux (a b : ℕ) : ModularForm 𝒮ℒ (a * 4 + b * 6) := (E₄.pow a).mul (E₆.pow b)

theorem qExpansion_Eaux (a b : ℕ) :
    qExpansion 1 (⇑(Eaux a b)) = qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b := by
  rw [Eaux, coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem isRat_Eaux (a b : ℕ) : IsRat (qExpansion 1 (⇑(Eaux a b))) := by
  rw [qExpansion_Eaux]; exact (isRat_E4.pow a).mul (isRat_E6.pow b)

theorem constantCoeff_Eaux (a b : ℕ) : PowerSeries.constantCoeff (qExpansion 1 (⇑(Eaux a b))) = 1 := by
  rw [qExpansion_Eaux, map_mul, map_pow, map_pow, constantCoeff_E4, constantCoeff_E6, one_pow, one_pow,
    one_mul]

theorem exists_weights (hk : Even k) : ∃ (m a b : ℕ), k + (a * 4 + b * 6 : ℕ) = 12 * (m : ℤ) := by
  obtain ⟨j, rfl⟩ := hk
  rcases Int.emod_two_eq_zero_or_one j with hpar | hpar
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 3 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 0, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q + 1 := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 1 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 1, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega

variable (K : IntermediateField ℚ ℂ)
  (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
  (s : ℕ) (hs : Nat.Coprime s N) (φ : ↥K →+* ℂ)
  (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
    φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
  {γ γ' : SL(2, ℤ)}
  (hγγ' : !![(1 : ZMod N), 0; 0, (s : ZMod N)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)
    = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * !![(1 : ZMod N), 0; 0, (s : ZMod N)])
include hK hs hφ hγγ'

theorem tp_slash_of_even (hk : Even k) (F : ModularForm (GamR N) k) (hF : IsRat (qExpansion N F)) :
    TP K φ (qExpansion N ((⇑F : ℍ → ℂ) ∣[k] γ)) (qExpansion N ((⇑F : ℍ → ℂ) ∣[k] γ')) := by
  obtain ⟨m, a, b, hw⟩ := exists_weights hk
  have key := tp_slash_mul K hK s hs φ hφ hγγ' F m (Eaux a b) (by exact_mod_cast hw) hF (isRat_Eaux a b)

  have hprod : ∀ α : SL(2, ℤ), qExpansion N (((⇑F : ℍ → ℂ) ∣[k] α) * ⇑(Eaux a b))
      = qExpansion N ((⇑F : ℍ → ℂ) ∣[k] α) * qExpansion N ⇑(Eaux a b) := by
    intro α
    rw [← coe_slashSL α F, ← coe_resSL N (Eaux a b),
      ModularForm.qExpansion_mul_coe natCast_pos (natCast_mem_strictPeriods N) (slashSL α F)
        (resSL N (Eaux a b))]
  rw [hprod γ, hprod γ'] at key
  refine TP.of_mul_unit key (isRat_widthN_levelOne N (Eaux a b) (isRat_Eaux a b)) ?_
  rw [constantCoeff_widthN_levelOne, constantCoeff_Eaux]

end Even

end GammaEvenRecip
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even.GammaEvenRecip"

theorem solution (N : ℕ) [NeZero N] {k : ℤ} (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion N F).coeff n = (r : ℂ))
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N) (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (γ γ' : SL(2, ℤ))
    (hγγ' : !![(1 : ZMod N), 0; 0, (s : ZMod N)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * !![(1 : ZMod N), 0; 0, (s : ZMod N)])
    (n : ℕ) :
    ∃ z : ↥K, (z : ℂ) = (UpperHalfPlane.qExpansion N ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n ∧
      (UpperHalfPlane.qExpansion N ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ')).coeff n = φ z :=
  GammaEvenRecip.tp_iff.mp (GammaEvenRecip.tp_slash_of_even K hK s hs φ hφ hγγ' hk F hrat) n

end
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even.GammaEvenRecip"

end S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
end P2MW
export P2MW.S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even (solution)
