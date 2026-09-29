-- Prove2me | solution 1 for ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c22415d0-2a46-5181-ad38-0cb3aaeb3ab2

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_WLight_frickeFunction_modularity_package
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_WLight_exists_levelFraction_of_stable_family
import Theorems.Thm_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction
import Theorems.Thm_WLight_frickeFunction_intBaseChange
import Theorems.Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
import Theorems.Thm_WLight_linearIndependent_complex_of_qExpansion_rational
import Theorems.Thm_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff
import Theorems.Thm_ModularForm_exists_gamma1_frickeRational_sigmaTransport
import Theorems.Thm_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace GammaOneGaloisModularEven

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 τ.im_pos.ne'
    subst hs
    simp at h2
    exact ⟨rfl, h2⟩

theorem tauPair_spec (τ : ℍ) : (tauPair τ).ω₁ = (τ : ℂ) ∧ (tauPair τ).ω₂ = 1 := ⟨rfl, rfl⟩

variable (N : ℕ)

def WW (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

def fricke (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ

def jf (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

theorem WW_spec (v : Fin 2 → ZMod N) (τ : ℍ) : WW N v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) := rfl

theorem fricke_spec (v : Fin 2 → ZMod N) (τ : ℍ) : fricke N v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ := rfl

theorem jf_spec (τ : ℍ) : jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl

def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

theorem kN_eq : kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := rfl

def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke N v}

abbrev Idx : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke N (t v.1)

def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

theorem gen_id_eq : gen N id = fun o : Idx N => o.elim jf fun v => fricke N v.1 := rfl

theorem gen_ds_eq (s : ℕ) :
    gen N (ds N s) = fun o : Idx N => o.elim jf fun v => fricke N ![v.1 0, (s : ZMod N) * v.1 1] := rfl

section Cyclo

variable [NeZero N]

theorem isPrimitiveRoot_zetaN : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

scoped instance instIsCyclotomic : IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN N
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

def zetaK : kN N := ⟨zetaN N, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

@[scoped simp] theorem coe_zetaK : ((zetaK N : kN N) : ℂ) = zetaN N := rfl

theorem isPrimitiveRoot_zetaK : IsPrimitiveRoot (zetaK N) N := by
  have h := isPrimitiveRoot_zetaN N
  rw [← coe_zetaK] at h
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h

theorem exists_pow_of_aut (σ : (kN N) ≃ₐ[ℚ] (kN N)) :
    ∃ s : ℕ, s.Coprime N ∧ σ (zetaK N) = zetaK N ^ s := by
  have hμ := isPrimitiveRoot_zetaK N
  refine ⟨((hμ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N).val, ZMod.val_coe_unit_coprime _, ?_⟩
  rw [hμ.autToPow_spec ℚ σ]

def phiOf (σ : (kN N) ≃ₐ[ℚ] (kN N)) : kN N →+* ℂ :=
  (algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom

theorem phiOf_apply (σ : (kN N) ≃ₐ[ℚ] (kN N)) (z : kN N) : phiOf N σ z = ((σ z : kN N) : ℂ) := rfl

theorem phiOf_zeta (σ : (kN N) ≃ₐ[ℚ] (kN N)) {s : ℕ} (hs : σ (zetaK N) = zetaK N ^ s)
    (z : kN N) (hz : (z : ℂ) = zetaN N) : phiOf N σ z = zetaN N ^ s := by
  have : z = zetaK N := Subtype.ext hz
  rw [phiOf_apply, this, hs]
  rfl

theorem phiOf_ratCast (σ : (kN N) ≃ₐ[ℚ] (kN N)) (r : ℚ) (z : kN N) (hz : (z : ℂ) = (r : ℂ)) :
    phiOf N σ z = r := by
  have : z = algebraMap ℚ (kN N) r := by
    apply Subtype.ext; rw [hz]; rfl
  rw [phiOf_apply, this, AlgEquiv.commutes]
  rfl

end Cyclo

section Width

local notation "Δ" => ModularForm.discriminant

theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_pow {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (m : ℕ) :
    Periodic ((g ^ m) ∘ ofComplex) c := by
  induction m with
  | zero => intro z; simp
  | succ m ih => rw [pow_succ]; exact periodic_mul ih h

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

variable (N : ℕ) [NeZero N]

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
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
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

theorem qExpansion_E₄_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

theorem qExpansion_E₆_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

theorem exists_map_of_rat {q : PowerSeries ℂ} (h : ∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)) :
    ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q := by
  choose r hr using h
  exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩

theorem rat_of_exists_map {q : PowerSeries ℂ} (h : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q)
    (n : ℕ) : ∃ r : ℚ, q.coeff n = (r : ℂ) := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩

theorem qExpansion_widthN_rat_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 (⇑F : ℍ → ℂ)).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion N (⇑F : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N (g := (⇑F : ℍ → ℂ)) F.holo' (SlashInvariantFormClass.periodic_comp_ofComplex F
    one_mem_strictPeriods_SL) (ModularFormClass.bdd_at_infty F) n]
  split_ifs with h
  · exact hrat _
  · exact ⟨0, by simp⟩

def E4cube : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

def E6sq : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)

def discForm : ModularForm 𝒮ℒ 12 := (1728 : ℂ)⁻¹ • (E4cube - E6sq)

@[scoped simp] theorem coe_discForm : (⇑discForm : ℍ → ℂ) = Δ := by
  funext z
  rw [discForm, IsGLPos.smul_apply, sub_apply, discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [E4cube, E6sq, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
  ring

theorem qExpansion_disc_rat_one (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑discForm : ℍ → ℂ)).coeff n = (r : ℂ) := by
  obtain ⟨p4, hp4⟩ := exists_map_of_rat qExpansion_E₄_rat
  obtain ⟨p6, hp6⟩ := exists_map_of_rat qExpansion_E₆_rat
  refine rat_of_exists_map ⟨PowerSeries.C (1728 : ℚ)⁻¹ * (p4 ^ 3 - p6 ^ 2), ?_⟩ n
  rw [discForm, IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
  simp only [E4cube, E6sq, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub, map_pow, map_pow, hp4, hp6]
  congr 1
  simp

theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [← coe_discForm]
  exact qExpansion_widthN_rat_of_levelOne N _ qExpansion_disc_rat_one n

variable (K : IntermediateField ℚ ℂ)

structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

theorem RatAt.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem r

theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

theorem RatAt.exists_map {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m) := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h.mem n⟩, ?_⟩
  ext n
  simp

end Width

section Group

variable (N : ℕ)

local notation "Δ" => ModularForm.discriminant

def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN N γ)

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  Subgroup.Normal.conj_mem (Gamma_normal N) g hg α

theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

variable {N}

def cw (G : ℍ → ℂ) (α : SL(2, ℤ)) : ℍ → ℂ := fun τ => G (α • τ)

theorem cw_apply (G : ℍ → ℂ) (α : SL(2, ℤ)) (τ : ℍ) : cw G α τ = G (α • τ) := rfl

theorem cw_mul (G : ℍ → ℂ) (α β : SL(2, ℤ)) : cw G (α * β) = cw (cw G α) β := by
  funext τ; simp [cw, mul_smul]

theorem cw_one (G : ℍ → ℂ) : cw G 1 = G := by funext τ; simp [cw]

theorem cw_eq_slash (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw G α = G ∣[(0 : ℤ)] α := by
  funext τ
  rw [ModularForm.SL_slash_apply, cw_apply, neg_zero, zpow_zero, mul_one]

theorem mdifferentiable_cw {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (α : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G α) := by
  rw [cw_eq_slash, ModularForm.SL_slash]; exact hG.slash _ _

end Group

section Fricke

variable (N : ℕ) [NeZero N]

local notation "Δ" => ModularForm.discriminant

theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke N v) := by
  obtain ⟨-, -, h3, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h3 v hv

theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  intro τ
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ => E₄ τ ^ 3) τ := (E₄.holo' τ).pow 3
  exact h1.div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

variable {N}

def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map (algebraMap (kN N) ℂ) R)

theorem gen_id_mem (o : Idx N) : gen N id o ∈ genSet N := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩

theorem aeval_mem_adjoin (R : MvPolynomial (Idx N) ℂ) :
    MvPolynomial.aeval (gen N id) R ∈ Algebra.adjoin ℂ (genSet N) := by
  induction R using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_id_mem o))

theorem ev_mem_adjoin (R : MvPolynomial (Idx N) (kN N)) : ev id R ∈ Algebra.adjoin ℂ (genSet N) :=
  aeval_mem_adjoin _

theorem adjoin_isDomain {a b : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ (genSet N))
    (hb : b ∈ Algebra.adjoin ℂ (genSet N)) (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N tauPair tauPair_spec (WW N) (WW_spec N)
    (fricke N) (fricke_spec N) jf jf_spec
  exact h6 a b ha hb hab

theorem ev_prod_ne_zero {ι : Type*} (s : Finset ι) (Q : ι → MvPolynomial (Idx N) (kN N))
    (hQ : ∀ i ∈ s, ev id (Q i) ≠ 0) : ev id (∏ i ∈ s, Q i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro h0
      have h0' : ev id (Q a) * ev (N := N) id (∏ i ∈ s, Q i) = 0 := by
        rw [← h0]; simp [ev, map_mul]
      rcases adjoin_isDomain (ev_mem_adjoin _) (ev_mem_adjoin _) h0' with h | h
      · exact hQ a (Finset.mem_insert_self a s) h
      · exact ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi)) h

theorem smul_eq_coe_smul (K : IntermediateField ℚ ℂ) (κ : K) (f : ℍ → ℂ) : κ • f = (κ : ℂ) • f := rfl

theorem exists_rat_combination (K : IntermediateField ℚ ℂ) {n M : ℕ} {Gi : Fin n → ℍ → ℂ}
    {G : ℍ → ℂ} (hGi : ∀ i, RatAt N K M (Gi i)) (hG : RatAt N K M G)
    (hmem : G ∈ Submodule.span ℂ (Set.range Gi)) :
    ∃ κ : Fin n → K, G = ∑ i, (κ i : ℂ) • Gi i := by
  classical
  by_cases hW : G ∈ Submodule.span K (Set.range Gi)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hW
    exact ⟨c, by rw [← hc]; rfl⟩
  exfalso
  obtain ⟨b, hb_sub, hb_span, hb_ind⟩ := exists_linearIndependent K (Set.range Gi)
  have hbfin : b.Finite := (Set.finite_range Gi).subset hb_sub
  have hGb : G ∉ b := fun h => hW (hb_span ▸ Submodule.subset_span h)
  have hGspan : G ∉ Submodule.span K b := by rwa [hb_span]
  have hins : LinearIndepOn K id (insert G b) := LinearIndepOn.id_insert hb_ind hGspan
  set sF : Finset (ℍ → ℂ) := (hbfin.insert G).toFinset with hsF
  have hcoe : (↑sF : Set (ℍ → ℂ)) = insert G b := Set.Finite.coe_toFinset _
  have hdata : ∀ f ∈ sF, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      Function.Periodic ((f * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (f * ModularForm.discriminant ^ M) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f * ModularForm.discriminant ^ M)).coeff n ∈ K := by
    intro f hf
    have hf' : f ∈ insert G b := by rwa [← hcoe, Finset.mem_coe]
    rcases hf' with rfl | hf'
    · exact ⟨hG.mdiff, hG.periodic, hG.bdd, hG.mem⟩
    · obtain ⟨i, rfl⟩ := hb_sub hf'
      exact ⟨(hGi i).mdiff, (hGi i).periodic, (hGi i).bdd, (hGi i).mem⟩
  have hind : LinearIndependent K (fun w : ↥(↑sF : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
    rw [hcoe]; exact hins
  have hC := WLight.linearIndependent_complex_of_qExpansion_rational N K sF M hdata hind
  rw [hcoe] at hC
  have hC' : LinearIndepOn ℂ id (insert G b) := hC
  have hnot := hC'.notMem_span_of_insert hGb
  rw [Set.image_id] at hnot
  apply hnot
  have hle : Submodule.span ℂ (Set.range Gi) ≤ Submodule.span ℂ b := by
    rw [Submodule.span_le]
    intro x hx
    have hxK : x ∈ Submodule.span K b := by rw [hb_span]; exact Submodule.subset_span hx
    exact Submodule.span_subset_span K ℂ b hxK
  exact hle hmem

theorem exists_ev_of_mem_adjoin {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin (kN N) (genSet N)) :
    ∃ R : MvPolynomial (Idx N) (kN N), ev id R = x := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨R₀, rfl⟩ := hx
  have hsec : ∀ y : genSet N, ∃ o : Idx N, gen N id o = y := by
    rintro ⟨y, hy⟩
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩
  choose sec hsec using hsec
  refine ⟨MvPolynomial.rename sec R₀, ?_⟩
  rw [ev, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
  have : (gen N id ∘ sec) = Subtype.val := funext hsec
  rw [this]
  rfl

theorem coeff_map_mem (R : MvPolynomial (Idx N) (kN N)) (m : Idx N →₀ ℕ) :
    (MvPolynomial.map (algebraMap (kN N) ℂ) R).coeff m ∈ kN N := by
  rw [MvPolynomial.coeff_map]; exact (R.coeff m).2

theorem descent {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : RatAt N (kN N) m G) :
    ∃ P Q : MvPolynomial (Idx N) (kN N), ev id Q ≠ 0 ∧ G * ev id Q = ev id P := by
  classical
  set S : Set (ℍ → ℂ) := {F | ∃ α : SL(2, ℤ), F = cw G α} with hS
  have hGS : G ∈ S := ⟨1, (cw_one G).symm⟩
  have hhol : ∀ F ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    rintro F ⟨α, rfl⟩; exact mdifferentiable_cw hG α
  have hpb' : ∀ F ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) := by
    rintro F ⟨α, rfl⟩; exact ⟨m, hpb α⟩
  have hst : ∀ γ : SL(2, ℤ), ∀ F ∈ S, (F ∘ (γ • ·)) ∈ S := by
    rintro γ F ⟨α, rfl⟩
    exact ⟨α * γ, by rw [cw_mul]; rfl⟩
  have hinvS : ∀ F ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    rintro F ⟨α, rfl⟩ γ hγ τ
    simp only [cw_apply]
    have : α • γ • τ = (α * γ * α⁻¹) • α • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (conj_mem_Gamma N α hγ) _
  obtain ⟨a, b, ha, hb, hb0, hGb⟩ := WLight.exists_levelFraction_of_stable_family N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec S hhol hpb' hst hinvS hGS
  have hpbG : ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) :=
    fun γ => ⟨m, hpb γ⟩
  obtain ⟨d, p, hprel⟩ := WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec ha hb hb0 hG hGb hpbG
  obtain ⟨n, lam, Gi, Pi, Qi, di, pi, hGsum, hGimd, hPQ, hpiK, hGirel⟩ :=
    WLight.frickeFunction_intBaseChange N tauPair tauPair_spec (WW N) (WW_spec N) (fricke N)
      (fricke_spec N) jf jf_spec hG ha hb hb0 hGb p hprel
  have hPi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev id R = Pi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).1
  have hQi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev id R = Qi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).2.1
  choose Ph hPh using hPi
  choose Qh hQh using hQi
  have hrati : ∀ i, ∃ mi : ℕ, RatAt N (kN N) mi (Gi i) := by
    intro i
    obtain ⟨mi, h1, h2, h3⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N
      tauPair tauPair_spec (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) rfl
      (hGimd i) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i))
      (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh i)) (coeff_map_mem _) (coeff_map_mem _)
      (by
        have := (hPQ i).2.2.1
        rwa [← hQh i] at this)
      (by
        have := (hPQ i).2.2.2
        rw [← hQh i, ← hPh i] at this
        exact this)
      ⟨di i, pi i, hpiK i, hGirel i⟩
    exact ⟨mi, (hGimd i), h1, h2, h3⟩
  choose mi hmi using hrati
  set M : ℕ := m + ∑ i, mi i with hM
  have hGM : RatAt N (kN N) M G := hrat.of_le (Nat.le_add_right _ _)
  have hGiM : ∀ i, RatAt N (kN N) M (Gi i) := fun i =>
    (hmi i).of_le (le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (mi j)) (Finset.mem_univ i))
      (Nat.le_add_left _ _))
  have hmem : G ∈ Submodule.span ℂ (Set.range Gi) := by
    rw [hGsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨κ, hκ⟩ := exists_rat_combination (kN N) hGiM hGM hmem
  refine ⟨∑ i, MvPolynomial.C (κ i) * Ph i * ∏ j ∈ Finset.univ.erase i, Qh j, ∏ i, Qh i, ?_, ?_⟩
  · exact ev_prod_ne_zero Finset.univ Qh fun i _ => by rw [hQh i]; exact (hPQ i).2.2.1
  · have hev_prod : ∀ (s : Finset (Fin n)), ev id (∏ j ∈ s, Qh j) = ∏ j ∈ s, Qi j := by
      intro s; simp only [ev, map_prod]; exact Finset.prod_congr rfl fun j _ => hQh j
    rw [hκ, hev_prod, Finset.sum_mul]
    simp only [ev, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C, map_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (MvPolynomial.aeval (gen N id)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i)) = Pi i := hPh i
    have h2 : ∀ j, (MvPolynomial.aeval (gen N id)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh j)) = Qi j :=
      hQh
    simp only [h1, h2]
    rw [← Finset.mul_prod_erase Finset.univ Qi (Finset.mem_univ i), ← (hPQ i).2.2.2]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [smul_one_smul, mul_assoc]
    rfl

end Fricke

section Companion

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant
local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem exists_abm {k : ℤ} (hk : Even k) :
    ∃ a b m : ℕ, k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ) := by
  obtain ⟨r, rfl⟩ := hk
  rcases le_or_gt 0 r with hr | hr
  · refine ⟨r.toNat, r.toNat, r.toNat, ?_⟩
    rw [Int.toNat_of_nonneg hr]; ring
  · refine ⟨2 * (-r).toNat, (-r).toNat, (-r).toNat, ?_⟩
    have h : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg (by omega)
    push_cast
    rw [h]; ring

variable (a b : ℕ)

def Ek : ModularForm 𝒮ℒ ((a : ℤ) * 4 + (b : ℤ) * 6) := (E₄.pow a).mul (E₆.pow b)

theorem Ek_apply (τ : ℍ) : Ek a b τ = E₄ τ ^ a * E₆ τ ^ b := by
  simp [Ek, coe_mul, coe_pow]

theorem qExpansion_Ek_rat (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (⇑(Ek a b) : ℍ → ℂ)).coeff n = (r : ℂ) := by
  obtain ⟨p4, hp4⟩ := exists_map_of_rat qExpansion_E₄_rat
  obtain ⟨p6, hp6⟩ := exists_map_of_rat qExpansion_E₆_rat
  refine rat_of_exists_map ⟨p4 ^ a * p6 ^ b, ?_⟩ n
  rw [Ek, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_mul, map_pow, map_pow, hp4, hp6]

theorem exists_Ek_ne_zero : ∃ τ : ℍ, E₄ τ ^ a * E₆ τ ^ b ≠ 0 := by
  have h4 : ∃ τ : ℍ, E₄ τ ≠ 0 := by
    by_contra h
    push Not at h
    have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
    exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this
  have h6 : ∃ τ : ℍ, E₆ τ ≠ 0 := by
    by_contra h
    push Not at h
    have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
    exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this
  obtain ⟨τ₄, hτ₄⟩ := h4
  by_contra h
  push Not at h
  have hprod : ∀ τ : ℍ, E₄ τ = 0 ∨ E₆ τ = 0 := fun τ =>
    (mul_eq_zero.1 (h τ)).imp eq_zero_of_pow_eq_zero eq_zero_of_pow_eq_zero
  have hmul : ∀ τ : ℍ, E₆ τ * E₄ τ = 0 := fun τ => by
    rcases hprod τ with h0 | h0 <;> simp [h0]
  have := eq_zero_of_mul_eq_zero E₆.holo' E₄.holo' hmul hτ₄
  obtain ⟨τ₆, hτ₆⟩ := h6
  exact hτ₆ (by simpa using congrFun this τ₆)

variable {a b} (k : ℤ) (m : ℕ)

def Φ (f : ModularForm (Γ₁ℝ N) k) : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m

theorem Φ_apply (f : ModularForm (Γ₁ℝ N) k) (τ : ℍ) : Φ (a := a) (b := b) k m f τ = f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m := rfl

theorem Φ_mul_disc (f : ModularForm (Γ₁ℝ N) k) (τ : ℍ) :
    f τ * (E₄ τ ^ a * E₆ τ ^ b) = Φ (a := a) (b := b) k m f τ * Δ τ ^ m := by
  rw [Φ_apply, div_mul_cancel₀ _ (pow_ne_zero _ (discriminant_ne_zero τ))]

theorem Φ_mul_disc_fun (f : ModularForm (Γ₁ℝ N) k) :
    Φ (a := a) (b := b) k m f * Δ ^ m = ⇑f * ⇑(Ek a b) := by
  funext τ; simp only [Pi.mul_apply, Pi.pow_apply, ← Φ_mul_disc, Ek_apply]

theorem mdifferentiable_Φ (f : ModularForm (Γ₁ℝ N) k) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Φ (a := a) (b := b) k m f) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ * (E₄ τ ^ a * E₆ τ ^ b)) :=
    f.holo'.mul ((E₄.holo'.pow a).mul (E₆.holo'.pow b))
  intro τ
  exact (h1 τ).div ((mdifferentiable_disc τ).pow m) (pow_ne_zero _ (discriminant_ne_zero τ))

variable (hk : k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ))
include hk

theorem crit_Φ (f : ModularForm (Γ₁ℝ N) k) :
    (∀ A : SL(2, ℤ), IsBoundedAtImInfty ((Φ (a := a) (b := b) k m f ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, Φ (a := a) (b := b) k m f (γ • τ) = Φ (a := a) (b := b) k m f τ := by
  obtain ⟨-, -, h₃, h₄⟩ := (ModularForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Gamma1 N) k a b m hk
    (Φ (a := a) (b := b) k m f) (mdifferentiable_Φ k m f)).1 ⟨f, Φ_mul_disc k m f⟩
  exact ⟨h₃, h₄⟩

omit hk in

theorem ratAt_Φ (f : ModularForm (Γ₁ℝ N) k) (c : ℕ → kN N)
    (hf : ∀ n : ℕ, (qExpansion 1 (⇑f)).coeff n = (c n : ℂ)) :
    RatAt N (kN N) m (Φ (a := a) (b := b) k m f) := by
  have hperf : Periodic ((⇑f : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N)
  have hperE : Periodic ((⇑(Ek a b) : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (Ek a b) one_mem_strictPeriods_SL
  have hbdf : IsBoundedAtImInfty (⇑f : ℍ → ℂ) := ModularFormClass.bdd_at_infty f
  have hbdE : IsBoundedAtImInfty (⇑(Ek a b) : ℍ → ℂ) := ModularFormClass.bdd_at_infty (Ek a b)
  refine ⟨mdifferentiable_Φ k m f, ?_, ?_, ?_⟩
  · rw [Φ_mul_disc_fun]
    exact periodic_mul (periodic_ofComplex_natCast hperf N) (periodic_ofComplex_natCast hperE N)
  · rw [Φ_mul_disc_fun]; exact hbdf.mul hbdE
  · intro n
    rw [Φ_mul_disc_fun, qExpansion_mul (analyticAt_cuspFunction_zero (natCast_pos N)
      (periodic_ofComplex_natCast hperf N) f.holo' hbdf) (analyticAt_cuspFunction_zero (natCast_pos N)
      (periodic_ofComplex_natCast hperE N) (Ek a b).holo' hbdE), PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem ?_ ?_
    · rw [qExpansion_coeff_widthN N (g := (⇑f : ℍ → ℂ)) f.holo' hperf hbdf]
      split_ifs
      · rw [hf]; exact SetLike.coe_mem _
      · exact zero_mem _
    · obtain ⟨r, hr⟩ := qExpansion_widthN_rat_of_levelOne N (Ek a b) (qExpansion_Ek_rat a b) ij.2
      rw [hr]; exact ratCast_mem r

end Companion

section Main

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant
local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem exists_multSeries (σ : (kN N) ≃ₐ[ℚ] (kN N)) (a b d : ℕ) :
    ∃ e : PowerSeries (kN N),
      e.map (algebraMap (kN N) ℂ) = qExpansion N (⇑(Ek a b) * Δ ^ d) ∧
      e.map (phiOf N σ) = qExpansion N (⇑(Ek a b) * Δ ^ d) ∧
      qExpansion N (⇑(Ek a b) * Δ ^ d) ≠ 0 := by

  let F : ModularForm 𝒮ℒ (((a : ℤ) * 4 + (b : ℤ) * 6) + (d : ℤ) * 12) := (Ek a b).mul (discForm.pow d)
  have hF : (⇑F : ℍ → ℂ) = ⇑(Ek a b) * Δ ^ d := by
    simp only [F, coe_mul, coe_pow, coe_discForm]
  have hrat1 : ∀ n, ∃ r : ℚ, (qExpansion 1 (⇑F : ℍ → ℂ)).coeff n = (r : ℂ) := by
    obtain ⟨p, hp⟩ := exists_map_of_rat (qExpansion_Ek_rat a b)
    obtain ⟨q, hq⟩ := exists_map_of_rat qExpansion_disc_rat_one
    refine rat_of_exists_map ⟨p * q ^ d, ?_⟩
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_mul, map_pow, hp, hq]
  have hratN : ∀ n, ∃ r : ℚ, (qExpansion N (⇑F : ℍ → ℂ)).coeff n = (r : ℂ) :=
    qExpansion_widthN_rat_of_levelOne N F hrat1
  choose r hr using hratN
  refine ⟨PowerSeries.mk fun n => ⟨(r n : ℂ), ratCast_mem (r n)⟩, ?_, ?_, ?_⟩
  · rw [← hF]; ext n; simp [hr n]
  · rw [← hF]; ext n
    rw [PowerSeries.coeff_map, hr n, PowerSeries.coeff_mk, phiOf_ratCast N σ (r n) _ rfl]
  · rw [← hF]
    have hperN : Periodic ((⇑F : ℍ → ℂ) ∘ ofComplex) N :=
      periodic_ofComplex_natCast (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL) N
    rw [Ne, qExpansion_eq_zero_iff (natCast_pos N) hperN (f := (⇑F : ℍ → ℂ)) F.holo'
      (ModularFormClass.bdd_at_infty F)]
    intro h0
    obtain ⟨τ, hτ⟩ := exists_Ek_ne_zero a b
    have := congrFun h0 τ
    rw [hF] at this
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hτ (by rw [← Ek_apply]; exact h)
    · exact pow_ne_zero _ (discriminant_ne_zero τ) h

theorem main (k : ℤ) (hk : Even k) (σ : (kN N) ≃ₐ[ℚ] (kN N)) (f : ModularForm (Γ₁ℝ N) k) (c : ℕ → kN N)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n = (c n : ℂ)) :
    ∃ f' : ModularForm (Γ₁ℝ N) k, ∀ n : ℕ, ModularFormClass.qCoeff f' n = ((σ (c n) : kN N) : ℂ) := by
  classical
  have hf' : ∀ n : ℕ, (qExpansion 1 (⇑f)).coeff n = (c n : ℂ) := hf
  obtain ⟨a, b, m, habm⟩ := exists_abm hk

  set G : ℍ → ℂ := Φ (a := a) (b := b) k m f with hGdef
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := mdifferentiable_Φ k m f
  obtain ⟨h₃, h₄⟩ := crit_Φ k m habm f
  have hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ :=
    fun g hg τ => h₄ g (Gamma_le_Gamma1 N hg) τ
  have hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m) := fun α => h₃ α
  have hrat : RatAt N (kN N) m G := ratAt_Φ k m f c hf'

  obtain ⟨P, Q, hQ0, hGQ⟩ := descent hG hinv hpb hrat

  obtain ⟨s, hs, hσ⟩ := exists_pow_of_aut N σ
  have hφ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      phiOf N σ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s :=
    fun z hz => phiOf_zeta N σ hσ z hz

  have hQ0' : MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N v.1)
      (Q.map (algebraMap (kN N) ℂ)) ≠ 0 := hQ0
  have hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
      MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N v.1) (Q.map (algebraMap (kN N) ℂ)) τ =
      Δ τ ^ m * MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N v.1)
        (P.map (algebraMap (kN N) ℂ)) τ := by
    intro τ
    have h1 := congrFun hGQ τ
    simp only [Pi.mul_apply] at h1
    change f τ * (E₄ τ ^ a * E₆ τ ^ b) * ev id Q τ = Δ τ ^ m * ev id P τ
    rw [Φ_mul_disc k m f τ, ← h1]
    ring

  obtain ⟨f', hQ'0, hid'⟩ := ModularForm.exists_gamma1_frickeRational_sigmaTransport N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) s hs (phiOf N σ) hφ k a b m
    habm f P Q hQ0' hid

  obtain ⟨-, G', hG', hG'Q, m₁, hTdata⟩ :=
    ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient N tauPair tauPair_spec (WW N)
      (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) s hs (phiOf N σ) hφ G hG P Q hQ0'
      hGQ
  obtain ⟨⟨hper, hbd, hmem⟩, ⟨hper', hbd', hmem'⟩, hcoef⟩ := hTdata (m₁ + m) (Nat.le_add_right _ _)

  set Q' : ℍ → ℂ := MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N ![v.1 0, (s : ZMod N) * v.1 1])
    (Q.map (phiOf N σ)) with hQ'def
  set P' : ℍ → ℂ := MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke N ![v.1 0, (s : ZMod N) * v.1 1])
    (P.map (phiOf N σ)) with hP'def
  have hQ'hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q' := by
    rw [hQ'def]
    induction (Q.map (phiOf N σ)) using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p o hp =>
        rw [map_mul, MvPolynomial.aeval_X]
        refine hp.mul ?_
        cases o with
        | none => exact mdifferentiable_jf
        | some v =>
            refine mdifferentiable_fricke N ?_
            intro h
            apply v.2
            have h0 : v.1 0 = 0 := by simpa using congrFun h 0
            have h1 : (s : ZMod N) * v.1 1 = 0 := by simpa using congrFun h 1
            have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
            have h1' : v.1 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
            funext i; fin_cases i <;> simp [h0, h1']
  have hG₁Q : Φ (a := a) (b := b) k m f' * Q' = P' := by
    funext τ
    have h1 := hid' τ
    simp only [Pi.mul_apply]
    apply mul_left_cancel₀ (pow_ne_zero m (discriminant_ne_zero τ))
    rw [← h1, Φ_mul_disc k m f' τ]
    ring
  have hG₁eq : Φ (a := a) (b := b) k m f' = G' := by
    have hdiff : ∀ τ : ℍ, (Φ (a := a) (b := b) k m f' - G') τ * Q' τ = 0 := by
      intro τ
      have e1 := congrFun hG₁Q τ
      have e2 := congrFun hG'Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, Q' τ₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hQ'0 (funext hall)
    have := eq_zero_of_mul_eq_zero ((mdifferentiable_Φ k m f').sub hG') hQ'hol hdiff hτ₀
    exact sub_eq_zero.1 this

  have hRGM : RatAt N (kN N) (m₁ + m) G := ⟨hG, hper, hbd, hmem⟩
  have hRG'M : RatAt N (kN N) (m₁ + m) G' := ⟨hG', hper', hbd', hmem'⟩
  obtain ⟨p₁, hpι⟩ := hRGM.exists_map
  have hpφ : p₁.map (phiOf N σ) = qExpansion N (G' * Δ ^ (m₁ + m)) := by
    ext n
    rw [PowerSeries.coeff_map]
    symm
    apply hcoef
    rw [← hpι, PowerSeries.coeff_map]
    rfl

  have hsplit : ∀ (g : ModularForm (Γ₁ℝ N) k), Φ (a := a) (b := b) k m g * Δ ^ (m₁ + m) =
      ⇑g * (⇑(Ek a b) * Δ ^ m₁) := by
    intro g
    rw [add_comm, pow_add, ← mul_assoc, Φ_mul_disc_fun]; ring
  obtain ⟨e, heι, heφ, he0⟩ := exists_multSeries (N := N) σ a b m₁

  have hperf : ∀ g : ModularForm (Γ₁ℝ N) k, Periodic ((⇑g : ℍ → ℂ) ∘ ofComplex) 1 := fun g =>
    SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods N)
  have hanf : ∀ g : ModularForm (Γ₁ℝ N) k, AnalyticAt ℂ (cuspFunction N (⇑g)) 0 := fun g =>
    analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast (hperf g) N) g.holo'
      (ModularFormClass.bdd_at_infty g)
  let F : ModularForm 𝒮ℒ (((a : ℤ) * 4 + (b : ℤ) * 6) + (m₁ : ℤ) * 12) := (Ek a b).mul (discForm.pow m₁)
  have hFcoe : (⇑F : ℍ → ℂ) = ⇑(Ek a b) * Δ ^ m₁ := by
    simp only [F, coe_mul, coe_pow, coe_discForm]
  have hanE : AnalyticAt ℂ (cuspFunction N (⇑(Ek a b) * Δ ^ m₁)) 0 := by
    rw [← hFcoe]
    exact analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast
      (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL) N) (f := (⇑F : ℍ → ℂ))
      F.holo' (ModularFormClass.bdd_at_infty F)

  set Sf : PowerSeries (kN N) := PowerSeries.mk fun n => if (N : ℕ) ∣ n then c (n / N) else 0 with hSf
  have hSfι : Sf.map (algebraMap (kN N) ℂ) = qExpansion N (⇑f) := by
    ext n
    rw [PowerSeries.coeff_map, hSf, PowerSeries.coeff_mk,
      qExpansion_coeff_widthN N (g := (⇑f : ℍ → ℂ)) f.holo' (hperf f) (ModularFormClass.bdd_at_infty f)]
    split_ifs with h
    · rw [hf']; rfl
    · simp

  have hprod : Sf * e = p₁ := by
    apply PowerSeries.map_injective (algebraMap (kN N) ℂ) Subtype.val_injective
    rw [map_mul, hSfι, heι, hpι, hsplit f, qExpansion_mul (hanf f) hanE]

  have hf'exp : qExpansion N (⇑f') = Sf.map (phiOf N σ) := by
    have h1 : qExpansion N (⇑f') * qExpansion N (⇑(Ek a b) * Δ ^ m₁) =
        Sf.map (phiOf N σ) * qExpansion N (⇑(Ek a b) * Δ ^ m₁) := by
      rw [← qExpansion_mul (hanf f') hanE, ← hsplit f', hG₁eq, ← hpφ, ← heφ, ← map_mul, hprod]
    exact mul_right_cancel₀ he0 h1
  refine ⟨f', fun n => ?_⟩
  have hw := qExpansion_coeff_widthN N (g := (⇑f' : ℍ → ℂ)) f'.holo' (hperf f')
    (ModularFormClass.bdd_at_infty f') (N * n)
  rw [if_pos (dvd_mul_right N n), Nat.mul_div_cancel_left _ (NeZero.pos N)] at hw
  change (qExpansion 1 (⇑f')).coeff n = _
  rw [← hw, hf'exp, PowerSeries.coeff_map, hSf, PowerSeries.coeff_mk,
    if_pos (dvd_mul_right N n), Nat.mul_div_cancel_left _ (NeZero.pos N), phiOf_apply]

end Main

end GammaOneGaloisModularEven
p2m_reactivate "P2MW.S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.GammaOneGaloisModularEven"

end
p2m_reactivate "P2MW.S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.GammaOneGaloisModularEven"

theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (σ : ↥K ≃ₐ[ℚ] ↥K) (f : ModularForm (CongruenceSubgroup.Gamma1 N) k) (c : ℕ → ↥K)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    ∃ f' : ModularForm (CongruenceSubgroup.Gamma1 N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := by
  subst hK
  exact GammaOneGaloisModularEven.main (N := N) k hk σ f c hf

end S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
end P2MW
export P2MW.S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even (solution)
