-- Prove2me | solution 1 for ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/75da4665-a06d-50a9-9b7d-1b4244c7a69a

import Mathlib
import Theorems.Thm_WLight_frickeFunction_modularity_package
import Theorems.Thm_WLight_levelN_structure_package
import Theorems.Thm_WLight_exists_levelFraction_of_stable_family
import Theorems.Thm_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction
import Theorems.Thm_WLight_frickeFunction_intBaseChange
import Theorems.Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
import Theorems.Thm_WLight_linearIndependent_complex_of_qExpansion_rational
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace SRecip

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

def zetaK : kN N := ⟨zetaN N, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

@[scoped simp] theorem coe_zetaK : ((zetaK N : kN N) : ℂ) = zetaN N := rfl

theorem zetaN_pow : zetaN N ^ N = 1 := (isPrimitiveRoot_zetaN N).pow_eq_one

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

theorem exists_ne_zero {v : ℍ → ℂ} (hv : v ≠ 0) : ∃ τ, v τ ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (funext h)

theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

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

theorem periodic_disc (N : ℕ) : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) N :=
  periodic_ofComplex_natCast periodic_disc_one N

theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_sub {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g - g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢; rw [h1, h2]

theorem periodic_pow {g : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c) (m : ℕ) :
    Periodic ((g ^ m) ∘ ofComplex) c := by
  induction m with
  | zero => intro z; simp
  | succ m ih => rw [pow_succ]; exact periodic_mul ih h

theorem bdd_pow {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (n : ℕ) : IsBoundedAtImInfty (f ^ n) := by
  induction n with
  | zero => (have h__af := (Filter.const_boundedAtFilter atImInfty (1 : ℂ)); simp at h__af; exact h__af)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

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

theorem qExpansion_disc_pow_rat (r : ℕ) (n : ℕ) :
    ∃ q : ℚ, (qExpansion N ((Δ : ℍ → ℂ) ^ r)).coeff n = (q : ℂ) := by
  have hF : (⇑(discForm.pow r) : ℍ → ℂ) = Δ ^ r := by rw [coe_pow, coe_discForm]
  rw [← hF]
  refine qExpansion_widthN_rat_of_levelOne N _ (fun n => ?_) n
  obtain ⟨p, hp⟩ := exists_map_of_rat qExpansion_disc_rat_one
  refine rat_of_exists_map ⟨p ^ r, ?_⟩ n
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_pow, hp]

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

theorem analyticAt_disc_pow (r : ℕ) : AnalyticAt ℂ (cuspFunction N ((Δ : ℍ → ℂ) ^ r)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_pow (periodic_disc N) r)
    (mdifferentiable_disc.pow r) (bdd_pow isBoundedAtImInfty_disc r)

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

theorem redN_eq (γ : SL(2, ℤ)) :
    redN N γ = (Int.castRingHom (ZMod N)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN N γ i j = ((γ i j : ℤ) : ZMod N) := rfl

theorem redN_mul (γ γ' : SL(2, ℤ)) : redN N (γ * γ') = redN N γ * redN N γ' := by
  rw [redN_eq, redN_eq, redN_eq, Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem redN_one : redN N 1 = 1 := by
  rw [redN, Matrix.SpecialLinearGroup.coe_one]; simp

theorem redN_det (γ : SL(2, ℤ)) : (redN N γ).det = 1 := by
  rw [redN_eq, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

theorem vm_mul (γ γ' : SL(2, ℤ)) (v : Fin 2 → ZMod N) : vm N (γ * γ') v = vm N γ' (vm N γ v) := by
  simp only [vm, redN_mul, Matrix.vecMul_vecMul]

theorem vm_one (v : Fin 2 → ZMod N) : vm N 1 v = v := by simp [vm, redN_one]

theorem vm_ne_zero (γ : SL(2, ℤ)) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : vm N γ v ≠ 0 := by
  intro h
  apply hv
  have : vm N γ⁻¹ (vm N γ v) = v := by rw [← vm_mul, mul_inv_cancel, vm_one]
  rw [← this, h, vm, Matrix.zero_vecMul]

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  Subgroup.Normal.conj_mem (Gamma_normal N) g hg α

theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

def idxMap (α : SL(2, ℤ)) : Idx N → Idx N :=
  fun o => o.map fun v => ⟨vm N α v.1, vm_ne_zero N α v.2⟩

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

def cwAlgHom (α : SL(2, ℤ)) : (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) where
  toFun G := cw G α
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem cw_mul_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G * G') α = cw G α * cw G' α := rfl

theorem cw_ne_zero {b : ℍ → ℂ} (hb : b ≠ 0) (γ : SL(2, ℤ)) : cw b γ ≠ 0 := by
  intro h
  apply hb
  have : cw (cw b γ) γ⁻¹ = b := by rw [← cw_mul, mul_inv_cancel, cw_one]
  rw [← this, h]; rfl

theorem cw_aeval {ι : Type} (g : ι → ℍ → ℂ) (R : MvPolynomial ι ℂ) (α : SL(2, ℤ)) :
    cw (MvPolynomial.aeval g R) α = MvPolynomial.aeval (fun i => cw (g i) α) R := by
  have := MvPolynomial.comp_aeval g (cwAlgHom α)
  have h__af := (congrArg (fun F => F R) this)
  simp at h__af
  exact h__af

theorem periodic_cw {G : ℍ → ℂ} (β : SL(2, ℤ)) (N : ℕ)
    (hinv : ∀ τ : ℍ, G ((β * ModularGroup.T ^ (N : ℤ) * β⁻¹) • τ) = G τ) :
    Periodic ((cw G β) ∘ ofComplex) N := by
  intro w
  by_cases hw : 0 < im w
  · have hwN : 0 < im (w + N) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hwN, ofComplex_apply_of_im_pos hw, cw_apply]
    have hpt : (⟨w + N, hwN⟩ : ℍ) = ModularGroup.T ^ (N : ℤ) • (⟨w, hw⟩ : ℍ) := by
      rw [modular_T_zpow_smul]
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    rw [hpt]
    have := hinv (β • (⟨w, hw⟩ : ℍ))
    rw [← this]
    congr 1
    simp only [mul_smul, inv_smul_smul]
  · have hw' : im w ≤ 0 := not_lt.mp hw
    have hwN : im (w + N) ≤ 0 := by simpa using hw'
    simp only [comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos hwN hw']

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

theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) : fricke N v (γ • τ) = fricke N (vm N γ v) τ := by
  obtain ⟨h1, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h1 v γ τ

theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

theorem jf_smul (α : SL(2, ℤ)) (τ : ℍ) : jf (α • τ) = jf τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : Δ τ ≠ 0 := discriminant_ne_zero τ
  rw [jf, jf, disc_smul, E₄_smul]
  field_simp

variable {N}

theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : ds N s v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa [ds] using congrFun h 0
  have h1 : (s : ZMod N) * v 1 = 0 := by simpa [ds] using congrFun h 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : v 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  funext i; fin_cases i <;> simp [h0, h1']

def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map ψ R)

abbrev ev₀ (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ := ev id (algebraMap (kN N) ℂ) R

theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : kN N →+* ℂ) (R S : MvPolynomial (Idx N) (kN N)) :
    ev t ψ (R * S) = ev t ψ R * ev t ψ S := by
  simp [ev]

theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen N t o) := by
  cases o with
  | none => exact mdifferentiable_jf
  | some v => exact mdifferentiable_fricke N (ht v.1 v.2)

theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ev t ψ R) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (mdifferentiable_gen t ht o)

theorem cw_gen {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm N α (t v) = t (vm N α' v)) (o : Idx N) :
    cw (gen N t o) α = gen N t (idxMap N α' o) := by
  cases o with
  | none => funext τ; exact jf_smul α τ
  | some v => funext τ; rw [cw_apply, gen, gen, Option.elim, fricke_smul, h]; rfl

theorem cw_ev {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm N α (t v) = t (vm N α' v)) (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)) :
    cw (ev t ψ R) α = ev t ψ (MvPolynomial.rename (idxMap N α') R) := by
  rw [ev, ev, cw_aeval, MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  have : (fun i => cw (gen N t i) α) = gen N t ∘ idxMap N α' := funext fun o => cw_gen h o
  rw [this]

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

theorem ev_mem_adjoin (R : MvPolynomial (Idx N) (kN N)) : ev₀ R ∈ Algebra.adjoin ℂ (genSet N) :=
  aeval_mem_adjoin _

theorem adjoin_isDomain {a b : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ (genSet N))
    (hb : b ∈ Algebra.adjoin ℂ (genSet N)) (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨-, -, -, -, -, h6⟩ := WLight.levelN_structure_package N tauPair tauPair_spec (WW N) (WW_spec N)
    (fricke N) (fricke_spec N) jf jf_spec
  exact h6 a b ha hb hab

theorem ev_prod_ne_zero {ι : Type*} (s : Finset ι) (Q : ι → MvPolynomial (Idx N) (kN N))
    (hQ : ∀ i ∈ s, ev₀ (Q i) ≠ 0) : ev₀ (∏ i ∈ s, Q i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro h0
      have h0' : ev₀ (Q a) * ev₀ (N := N) (∏ i ∈ s, Q i) = 0 := by
        rw [← h0]; simp [ev, map_mul]
      rcases adjoin_isDomain (ev_mem_adjoin _) (ev_mem_adjoin _) h0' with h | h
      · exact hQ a (Finset.mem_insert_self a s) h
      · exact ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi)) h

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
    ∃ R : MvPolynomial (Idx N) (kN N), ev₀ R = x := by
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
  rw [ev₀, ev, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
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
    ∃ P Q : MvPolynomial (Idx N) (kN N), ev₀ Q ≠ 0 ∧ G * ev₀ Q = ev₀ P := by
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
  have hPi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev₀ R = Pi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).1
  have hQi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev₀ R = Qi i := fun i =>
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
  · have hev_prod : ∀ (s : Finset (Fin n)), ev₀ (∏ j ∈ s, Qh j) = ∏ j ∈ s, Qi j := by
      intro s; simp only [ev₀, ev, map_prod]; exact Finset.prod_congr rfl fun j _ => hQh j
    rw [hκ, hev_prod, Finset.sum_mul]
    simp only [ev₀, ev, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C, map_prod]
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

section Transport

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant

def TD (φ : kN N →+* ℂ) (m₀ : ℕ) (u u' : ℍ → ℂ) : Prop := ∀ M : ℕ, m₀ ≤ M →
  (Function.Periodic ((u * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n ∈ kN N) ∧
  (Function.Periodic ((u' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u' * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n ∈ kN N) ∧
  ∀ (n : ℕ) (z : kN N),
    (z : ℂ) = (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n →
    (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n = φ z

theorem transportT {s : ℕ} (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (P Q : MvPolynomial (Idx N) (kN N))
    (hQ0 : ev₀ Q ≠ 0) (huQ : u * ev₀ Q = ev₀ P) :
    ev (ds N s) φ Q ≠ 0 ∧ ∃ u' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u' ∧
      u' * ev (ds N s) φ Q = ev (ds N s) φ P ∧ ∃ m₀ : ℕ, TD φ m₀ u u' :=
  ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient N tauPair tauPair_spec (WW N)
    (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) s hs φ hφ u hu P Q hQ0 huQ

theorem eq_of_TD {φ : kN N →+* ℂ} {u F₁ F₂ : ℍ → ℂ} (h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₁)
    (h₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₂)
    {m₁ m₂ : ℕ} (hT₁ : TD φ m₁ u F₁) (hT₂ : TD φ m₂ u F₂) : F₁ = F₂ := by
  set M : ℕ := m₁ + m₂ with hM
  obtain ⟨⟨-, -, hmem⟩, ⟨hper₁, hbd₁, -⟩, hco₁⟩ := hT₁ M (Nat.le_add_right _ _)
  obtain ⟨-, ⟨hper₂, hbd₂, -⟩, hco₂⟩ := hT₂ M (Nat.le_add_left _ _)
  have hexp : qExpansion N (F₁ * Δ ^ M) = qExpansion N (F₂ * Δ ^ M) := by
    ext n
    obtain ⟨z, hz⟩ : ∃ z : kN N, (z : ℂ) = (qExpansion N (u * Δ ^ M)).coeff n := ⟨⟨_, hmem n⟩, rfl⟩
    rw [hco₁ n z hz, hco₂ n z hz]
  have hmd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₁ * Δ ^ M) := h₁.mul (mdifferentiable_disc.pow M)
  have hmd₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₂ * Δ ^ M) := h₂.mul (mdifferentiable_disc.pow M)
  have han₁ := analyticAt_cuspFunction_zero (natCast_pos N) hper₁ hmd₁ hbd₁
  have han₂ := analyticAt_cuspFunction_zero (natCast_pos N) hper₂ hmd₂ hbd₂
  have hzero : qExpansion N (F₁ * Δ ^ M - F₂ * Δ ^ M) = 0 := by
    rw [qExpansion_sub han₁ han₂, hexp, sub_self]
  rw [qExpansion_eq_zero_iff (natCast_pos N) (periodic_sub hper₁ hper₂) (hmd₁.sub hmd₂) (hbd₁.sub hbd₂)]
    at hzero
  funext τ
  have := congrFun hzero τ
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
  have hΔ : Δ τ ^ M ≠ 0 := pow_ne_zero _ (disc_ne_zero τ)
  have : (F₁ τ - F₂ τ) * Δ τ ^ M = 0 := by rw [sub_mul]; exact this
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hΔ)

theorem TD_self {φ : kN N →+* ℂ} {m : ℕ} {u : ℍ → ℂ} (hu : RatAt N ⊥ m u) : TD φ m u u := by
  intro M hM
  have hM' : RatAt N ⊥ M u := hu.of_le hM
  have hK : ∀ n, (qExpansion N (u * Δ ^ M)).coeff n ∈ kN N := by
    intro n
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (hM'.mem n)
    rw [← hr]; exact ratCast_mem r
  refine ⟨⟨hM'.periodic, hM'.bdd, hK⟩, ⟨hM'.periodic, hM'.bdd, hK⟩, fun n z hz => ?_⟩
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (hM'.mem n)
  have hzr : z = (r : kN N) := by
    apply Subtype.ext
    rw [hz, ← hr]
    simp
  rw [hzr, map_ratCast, ← hr]
  rfl

theorem exists_of_mul_eq {K : Type*} [Field K] (ι φ : K →+* ℂ)
    {B A : PowerSeries K} (hB : B ≠ 0) {ξ₁ ξ₂ : PowerSeries ℂ}
    (h1 : ξ₁ * B.map ι = A.map ι) (h2 : ξ₂ * B.map φ = A.map φ) :
    ∃ X : PowerSeries K, X.map ι = ξ₁ ∧ X.map φ = ξ₂ := by
  classical
  set v : ℕ := B.order.toNat with hv
  set U : PowerSeries K := B.divXPowOrder with hU
  have hBU : PowerSeries.X ^ v * U = B := PowerSeries.X_pow_order_mul_divXPowOrder
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU, PowerSeries.constantCoeff_divXPowOrder]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.coeff_order hB)
  obtain ⟨u, hu⟩ := hUunit
  have hAι : A.map ι = PowerSeries.X ^ v * (ξ₁ * U.map ι) := by
    rw [← h1, ← hBU]
    simp only [map_mul, map_pow, PowerSeries.map_X]
    ring
  have hAdvd : PowerSeries.X ^ v ∣ A := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hcoef : PowerSeries.coeff n (A.map ι) = 0 := by
      rw [hAι, PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hn)]
    rw [PowerSeries.coeff_map] at hcoef
    exact ι.injective (by rw [hcoef, map_zero])
  obtain ⟨A', hA'⟩ := hAdvd
  have hXv : (PowerSeries.X : PowerSeries ℂ) ^ v ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  have key : ∀ (ψ : K →+* ℂ) (ξ : PowerSeries ℂ), ξ * B.map ψ = A.map ψ → ξ * U.map ψ = A'.map ψ := by
    intro ψ ξ h
    rw [← hBU, hA'] at h
    simp only [map_mul, map_pow, PowerSeries.map_X] at h
    have : (PowerSeries.X : PowerSeries ℂ) ^ v * (ξ * U.map ψ) = PowerSeries.X ^ v * A'.map ψ := by
      rw [← h]; ring
    exact mul_left_cancel₀ hXv this
  refine ⟨A' * ↑u⁻¹, ?_, ?_⟩
  · have hk := key ι ξ₁ h1
    have hUι : U.map ι ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map ι).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUι
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]
  · have hk := key φ ξ₂ h2
    have hUφ : U.map φ ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map φ).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUφ
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]

theorem exists_discPowSeries (φ : kN N →+* ℂ) (r : ℕ) :
    ∃ δ : PowerSeries (kN N), δ.map (algebraMap (kN N) ℂ) = qExpansion N ((Δ : ℍ → ℂ) ^ r) ∧
      δ.map φ = qExpansion N ((Δ : ℍ → ℂ) ^ r) ∧ δ ≠ 0 := by
  choose q hq using qExpansion_disc_pow_rat N r
  refine ⟨PowerSeries.mk fun n => ((q n : ℚ) : kN N), ?_, ?_, ?_⟩
  · ext n; simp [hq n]
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_ratCast, hq n]
  · intro h0
    have h1 : qExpansion N ((Δ : ℍ → ℂ) ^ r) = 0 := by
      ext n
      have := congrArg (PowerSeries.coeff n) h0
      simp only [PowerSeries.coeff_mk, map_zero, Rat.cast_eq_zero] at this
      rw [hq n, this]; simp
    rw [qExpansion_eq_zero_iff (natCast_pos N) (periodic_pow (periodic_disc N) r)
      (mdifferentiable_disc.pow r) (bdd_pow isBoundedAtImInfty_disc r)] at h1
    exact disc_pow_ne_zero r UpperHalfPlane.I (by rw [h1]; rfl)

end Transport

section Matrices

variable {N : ℕ} [NeZero N]

theorem redN_S : redN N ModularGroup.S = !![0, -1; 1, 0] := by
  rw [redN, ModularGroup.coe_S]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem, ModularGroup.coe_T_zpow]
  simp

theorem exists_diag_lift {c : ℕ} (hc : c.Coprime N) :
    ∃ γ₀ : SL(2, ℤ), redN N γ₀ = !![(((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (c : ZMod N)] := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime c hc with hu
  set t : ZMod N := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) with ht
  have htc : t * (c : ZMod N) = 1 := Units.inv_mul u
  set M' : Matrix (Fin 2) (Fin 2) (ZMod N) := !![t, 0; 0, (c : ZMod N)] with hM'
  have hdet : M'.det = 1 := by rw [hM', Matrix.det_fin_two_of]; rw [htc]; ring
  obtain ⟨A', hA'⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod N ⟨M', hdet⟩
  refine ⟨A', ?_⟩
  have := congrArg (fun y : SL(2, ZMod N) => (y : Matrix (Fin 2) (Fin 2) (ZMod N))) hA'
  simpa [redN_eq] using this

theorem vm_S_diag {c : ℕ} (hc : c.Coprime N) {γ₀ : SL(2, ℤ)}
    (hγ₀ : redN N γ₀ = !![(((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (c : ZMod N)])
    (v : Fin 2 → ZMod N) :
    vm N (ModularGroup.S * γ₀) (ds N c v) = ds N c (vm N ModularGroup.S v) := by
  set t : ZMod N := (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N) with ht
  have htc : t * (c : ZMod N) = 1 := Units.inv_mul (ZMod.unitOfCoprime c hc)
  funext i
  simp only [vm, redN_mul, redN_S, hγ₀, ds]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    rw [mul_comm ((c : ZMod N))  , mul_assoc, mul_comm (c : ZMod N) t, htc, mul_one]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, mul_comm]

theorem conj_mem_Gamma1 {c : ℕ} (hc : c.Coprime N) {γ₀ : SL(2, ℤ)}
    (hγ₀ : redN N γ₀ = !![(((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (c : ZMod N)])
    {γ : SL(2, ℤ)} (hb : ((γ 0 1 : ℤ) : ZMod N) = 0) (hd : ((γ 1 1 : ℤ) : ZMod N) = c) :
    ModularGroup.S * γ * γ₀⁻¹ * ModularGroup.S⁻¹ ∈ Gamma1 N := by
  set t : ZMod N := (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N) with ht
  have htc : t * (c : ZMod N) = 1 := Units.inv_mul (ZMod.unitOfCoprime c hc)
  have hct : (c : ZMod N) * t = 1 := Units.mul_inv (ZMod.unitOfCoprime c hc)

  have hγ₀inv : redN N γ₀⁻¹ = !![(c : ZMod N), 0; 0, t] := by
    rw [redN, Matrix.SpecialLinearGroup.coe_inv]
    have : (γ₀ : Matrix (Fin 2) (Fin 2) ℤ).adjugate.map ((↑) : ℤ → ZMod N) = (redN N γ₀).adjugate := by
      rw [redN_eq]
      exact RingHom.map_adjugate (Int.castRingHom (ZMod N)) _
    rw [this, hγ₀, Matrix.adjugate_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hSinv : redN N ModularGroup.S⁻¹ = !![0, 1; -1, 0] := by
    rw [redN, Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, Matrix.adjugate_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp

  set a : ZMod N := ((γ 0 0 : ℤ) : ZMod N) with ha
  set x : ZMod N := ((γ 1 0 : ℤ) : ZMod N) with hx
  have hγred : redN N γ = !![a, 0; x, (c : ZMod N)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [redN_apply, ha, hx, hb, hd]
  have hac : a * (c : ZMod N) = 1 := by
    have := redN_det N γ
    rw [hγred, Matrix.det_fin_two_of] at this
    simpa using this
  have hred : redN N (ModularGroup.S * γ * γ₀⁻¹ * ModularGroup.S⁻¹) = !![1, -(x * (c : ZMod N)); 0, 1] := by
    rw [redN_mul, redN_mul, redN_mul, redN_S, hγred, hγ₀inv, hSinv]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hct, hac, mul_comm]
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun (congrFun hred 0) 0
    rw [redN_apply] at this; simpa using this
  · have := congrFun (congrFun hred 1) 1
    rw [redN_apply] at this; simpa using this
  · have := congrFun (congrFun hred 1) 0
    rw [redN_apply] at this; simpa using this

end Matrices

section Bridge

variable {N : ℕ} [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem exists_zeta_lift (ι : ℚbar →+* ℂ) : ∃ ζ₁ : ℚbar, ζ₁ ^ N = 1 ∧ ι ζ₁ = zetaN N := by
  have hNpos : 0 < N := NeZero.pos N
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : ℚbar, IsPrimitiveRoot ζ₀ N := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N ℚbar)
      (Polynomial.degree_cyclotomic_pos N ℚbar hNpos).ne'
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).mp hz⟩
  have hι : IsPrimitiveRoot (ι ζ₀) N := hζ₀.map_of_injective ι.injective
  obtain ⟨i, -, hi⟩ := hι.eq_pow_of_pow_eq_one (zetaN_pow N)
  exact ⟨ζ₀ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

theorem exists_bridge (ι : ℚbar →+* ℂ) :
    ∃ ψ : kN N →+* ℚbar, ∀ x : kN N, ι (ψ x) = x := by
  let ι' : ℚbar →ₐ[ℚ] ℂ := ι.toRatAlgHom
  obtain ⟨ζ₁, -, hζ₁⟩ := exists_zeta_lift (N := N) ι
  have hle : (kN N).toSubalgebra ≤ ι'.range := by
    have h1 : kN N ≤ ι'.fieldRange := by
      rw [kN, IntermediateField.adjoin_simple_le_iff]
      exact ⟨ζ₁, hζ₁⟩
    exact h1
  let e := AlgEquiv.ofInjectiveField ι'
  refine ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion hle)).toRingHom, fun x => ?_⟩
  have h2 : ι' (e.symm (Subalgebra.inclusion hle x)) = ((Subalgebra.inclusion hle x : ι'.range) : ℂ) := by
    have := AlgEquiv.ofInjective_apply ι' ι'.toRingHom.injective (e.symm (Subalgebra.inclusion hle x))
    rw [← this]
    simp [e, AlgEquiv.ofInjectiveField]
  exact h2

end Bridge

section Main

variable {N : ℕ} [NeZero N]

local notation "Δ" => ModularForm.discriminant
local notation "ℚbar" => AlgebraicClosure ℚ

theorem hbd_cw {m : ℕ} {G : ℍ → ℂ}
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m)) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty (cw G α * Δ ^ m) := hbd α

theorem ratAt_bot {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ)) :
    RatAt N ⊥ m G := by
  have hper1 : Periodic ((G * Δ ^ m) ∘ ofComplex) 1 := by
    have hG1 : Periodic ((cw G 1) ∘ ofComplex) (1 : ℕ) := by
      refine periodic_cw 1 1 fun τ => ?_
      simp only [one_mul, inv_one, mul_one, Nat.cast_one, zpow_one]
      exact hinv _ (by rw [Gamma1_mem]; simp [ModularGroup.coe_T]) τ
    rw [cw_one, Nat.cast_one] at hG1
    exact periodic_mul hG1 (periodic_pow periodic_disc_one m)
  have hbd1 : IsBoundedAtImInfty (G * Δ ^ m) := by
    have := hbd 1
    simpa using this
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G * Δ ^ m) := hG.mul (mdifferentiable_disc.pow m)
  refine ⟨hG, periodic_ofComplex_natCast hper1 N, hbd1, fun n => ?_⟩
  rw [qExpansion_coeff_widthN N hmd hper1 hbd1 n, IntermediateField.mem_bot]
  split_ifs with h
  · obtain ⟨r, hr⟩ := hrat (n / N)
    exact ⟨r, hr.symm⟩
  · exact ⟨0, by simp⟩

theorem ratAt_kN_of_bot {m : ℕ} {G : ℍ → ℂ} (h : RatAt N ⊥ m G) : RatAt N (kN N) m G :=
  ⟨h.mdiff, h.periodic, h.bdd, fun n => by
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (h.mem n)
    rw [← hr]; exact ratCast_mem r⟩

theorem main (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ))
    (ι : ℚbar →+* ℂ) :
    ∃ a : ℕ → ℚbar,
      (∀ n : ℕ, (qExpansion N (cw G ModularGroup.S * Δ ^ m)).coeff n = ι (a n)) ∧
      ∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (c : ℕ), (∀ ζ : ℚbar, ζ ^ N = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c →
          ∀ n : ℕ, (qExpansion N (cw G (ModularGroup.S * γ) * Δ ^ m)).coeff n = ι (σ (a n)) := by
  classical

  have hRb : RatAt N ⊥ m G := ratAt_bot hG hinv hbd hrat
  have hR : RatAt N (kN N) m G := ratAt_kN_of_bot hRb
  have hinvΓ : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ :=
    fun g hg τ => hinv g (Gamma_le_Gamma1 N hg) τ
  obtain ⟨P, Q, hQ0, hGQ⟩ := descent hG hinvΓ (hbd_cw hbd) hR

  set S := ModularGroup.S with hSdef
  set G₁ : ℍ → ℂ := cw G S with hG₁def
  set P₁ : MvPolynomial (Idx N) (kN N) := MvPolynomial.rename (idxMap N S) P with hP₁
  set Q₁ : MvPolynomial (Idx N) (kN N) := MvPolynomial.rename (idxMap N S) Q with hQ₁
  have hcwS : ∀ (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)),
      cw (ev id ψ R) S = ev id ψ (MvPolynomial.rename (idxMap N S) R) :=
    fun ψ R => cw_ev (t := id) (α := S) (α' := S) (fun v => rfl) ψ R
  have hcwS₀ : ∀ R : MvPolynomial (Idx N) (kN N), cw (ev₀ R) S = ev₀ (MvPolynomial.rename (idxMap N S) R) :=
    fun R => hcwS _ R
  have hG₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁ := mdifferentiable_cw hG S
  have hQ₁0 : ev₀ Q₁ ≠ 0 := by rw [hQ₁, ← hcwS₀]; exact cw_ne_zero hQ0 S
  have hG₁Q : G₁ * ev₀ Q₁ = ev₀ P₁ := by
    rw [hQ₁, hP₁, ← hcwS₀, ← hcwS₀, hG₁def, ← cw_mul_fun, hGQ]

  have hperSγ : ∀ γ : SL(2, ℤ), Periodic ((cw G (S * γ) * Δ ^ m) ∘ ofComplex) N := by
    intro γ
    refine periodic_mul (periodic_cw (S * γ) N fun τ => hinvΓ _ ?_ τ) (periodic_pow (periodic_disc N) m)
    exact conj_mem_Gamma N (S * γ) (T_pow_mem_Gamma N)

  have hφ₁ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      (algebraMap (kN N) ℂ) z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ 1 := by
    intro z hz; rw [pow_one]; exact hz
  obtain ⟨-, u₁, -, -, m₁, hTD₁⟩ := transportT (Nat.coprime_one_left N) (algebraMap (kN N) ℂ) hφ₁ hG₁ P₁ Q₁
    hQ₁0 hG₁Q
  obtain ⟨⟨hper₁, hbd₁, hmem₁⟩, -, -⟩ := hTD₁ (m₁ + m) (Nat.le_add_right _ _)
  have hR₁M : RatAt N (kN N) (m₁ + m) G₁ := ⟨hG₁, hper₁, hbd₁, hmem₁⟩
  obtain ⟨p₁, hp₁⟩ := hR₁M.exists_map

  have hper₁m : Periodic ((G₁ * Δ ^ m) ∘ ofComplex) N := by
    have := hperSγ 1; rwa [mul_one] at this
  have hbd₁m : IsBoundedAtImInfty (G₁ * Δ ^ m) := by
    have := hbd S; exact this
  have han₁m : AnalyticAt ℂ (cuspFunction N (G₁ * Δ ^ m)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hper₁m (hG₁.mul (mdifferentiable_disc.pow m)) hbd₁m
  obtain ⟨δ, hδι, -, hδ0⟩ := exists_discPowSeries (N := N) (algebraMap (kN N) ℂ) m₁
  have hsplit : ∀ (r : ℕ) (w : ℍ → ℂ), w * Δ ^ (r + m) = w * Δ ^ m * Δ ^ r := by
    intro r w; rw [add_comm, pow_add, mul_assoc]
  have hmul₁ : qExpansion N (G₁ * Δ ^ m) * δ.map (algebraMap (kN N) ℂ) = p₁.map (algebraMap (kN N) ℂ) := by
    rw [hδι, hp₁, hsplit m₁, qExpansion_mul han₁m (analyticAt_disc_pow m₁)]
  obtain ⟨A, hAι, -⟩ := exists_of_mul_eq (algebraMap (kN N) ℂ) (algebraMap (kN N) ℂ) hδ0 hmul₁ hmul₁

  obtain ⟨ψ, hψ⟩ := exists_bridge (N := N) ι
  refine ⟨fun n => ψ (PowerSeries.coeff n A), fun n => ?_, ?_⟩
  · rw [hψ, ← hAι, PowerSeries.coeff_map]; rfl

  intro σ c hσ γ hγb hγd n

  obtain ⟨ζ₁, hζ₁N, hζ₁⟩ := exists_zeta_lift (N := N) ι
  have hprim₁ : IsPrimitiveRoot ζ₁ N := by
    have h := isPrimitiveRoot_zetaN N
    rw [← hζ₁] at h
    exact h.of_map_of_injective ι.injective
  have hc : c.Coprime N := by
    have h1 : IsPrimitiveRoot (σ ζ₁) N := hprim₁.map_of_injective σ.injective
    rw [hσ ζ₁ hζ₁N] at h1
    exact (hprim₁.pow_iff_coprime (NeZero.pos N) c).mp h1
  set φ : kN N →+* ℂ := ι.comp ((σ : ℚbar ≃ₐ[ℚ] ℚbar).toRingEquiv.toRingHom.comp ψ) with hφdef
  have hφapp : ∀ z : kN N, φ z = ι (σ (ψ z)) := fun z => rfl
  have hψζ : ψ (zetaK N) = ζ₁ := ι.injective (by rw [hψ, coe_zetaK, hζ₁])
  have hφ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ c := by
    intro z hz
    have hz' : z = zetaK N := Subtype.ext hz
    rw [hφapp, hz', hψζ, hσ ζ₁ hζ₁N, map_pow, hζ₁]; rfl

  obtain ⟨-, G', hG', hG'Q, m₂, hTD₂⟩ := transportT hc φ hφ hG P Q hQ0 hGQ
  have hGG' : G' = G := eq_of_TD hG' hG hTD₂ (TD_self (φ := φ) hRb)
  rw [hGG'] at hG'Q

  obtain ⟨γ₀, hγ₀⟩ := exists_diag_lift (N := N) hc
  have hcw₀ : ∀ R : MvPolynomial (Idx N) (kN N),
      cw (ev (ds N c) φ R) (S * γ₀) = ev (ds N c) φ (MvPolynomial.rename (idxMap N S) R) :=
    fun R => cw_ev (t := ds N c) (α := S * γ₀) (α' := S) (vm_S_diag hc hγ₀) φ R
  have hSγ₀Q : cw G (S * γ₀) * ev (ds N c) φ Q₁ = ev (ds N c) φ P₁ := by
    rw [hQ₁, hP₁, ← hcw₀, ← hcw₀, ← cw_mul_fun, hG'Q]

  obtain ⟨hQ₁c0, G₁', hG₁', hG₁'Q, m₃, hTD₃⟩ := transportT hc φ hφ hG₁ P₁ Q₁ hQ₁0 hG₁Q
  have hident : G₁' = cw G (S * γ₀) := by
    have hdiff : ∀ τ : ℍ, (G₁' - cw G (S * γ₀)) τ * ev (ds N c) φ Q₁ τ = 0 := by
      intro τ
      have e1 := congrFun hG₁'Q τ
      have e2 := congrFun hSγ₀Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero hQ₁c0
    have := eq_zero_of_mul_eq_zero (hG₁'.sub (mdifferentiable_cw hG _))
      (mdifferentiable_ev (ds N c) (fun v hv => ds_ne_zero hc hv) φ Q₁) hdiff hτ₀
    exact sub_eq_zero.1 this

  have hγγ₀ : cw G (S * γ) = cw G (S * γ₀) := by
    funext τ
    simp only [cw_apply]
    have hmem := conj_mem_Gamma1 hc hγ₀ hγb hγd
    have : (S * γ) • τ = (S * γ * γ₀⁻¹ * S⁻¹) • (S * γ₀) • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this, hinv _ hmem]

  set M : ℕ := m₃ + m with hM
  obtain ⟨⟨hperM, hbdM, hmemM⟩, ⟨hperM', hbdM', -⟩, hcoM⟩ := hTD₃ M (Nat.le_add_right _ _)
  have hR₁' : RatAt N (kN N) M G₁ := ⟨hG₁, hperM, hbdM, hmemM⟩
  obtain ⟨p, hpι⟩ := hR₁'.exists_map
  have hpφ : p.map φ = qExpansion N (G₁' * Δ ^ M) := by
    ext k
    rw [PowerSeries.coeff_map]
    symm
    apply hcoM
    rw [← hpι, PowerSeries.coeff_map]
    rfl
  obtain ⟨δ', hδ'ι, hδ'φ, hδ'0⟩ := exists_discPowSeries (N := N) φ m₃

  have hAδ : A * δ' = p := by
    apply PowerSeries.map_injective (algebraMap (kN N) ℂ) Subtype.val_injective
    rw [map_mul, hAι, hδ'ι, hpι, hM, hsplit m₃, qExpansion_mul han₁m (analyticAt_disc_pow m₃)]

  have hperγ : Periodic ((cw G (S * γ) * Δ ^ m) ∘ ofComplex) N := hperSγ γ
  have hbdγ : IsBoundedAtImInfty (cw G (S * γ) * Δ ^ m) := hbd (S * γ)
  have hanγ : AnalyticAt ℂ (cuspFunction N (cw G (S * γ) * Δ ^ m)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hperγ ((mdifferentiable_cw hG _).mul
      (mdifferentiable_disc.pow m)) hbdγ
  have hkey : qExpansion N (cw G (S * γ) * Δ ^ m) * qExpansion N ((Δ : ℍ → ℂ) ^ m₃) =
      A.map φ * qExpansion N ((Δ : ℍ → ℂ) ^ m₃) := by
    rw [← qExpansion_mul hanγ (analyticAt_disc_pow m₃), ← hsplit m₃, hγγ₀, ← hident, ← hM, ← hpφ, ← hAδ,
      map_mul, hδ'φ]
  have hΔM0 : qExpansion N ((Δ : ℍ → ℂ) ^ m₃) ≠ 0 := by
    rw [← hδ'ι]
    intro h0
    apply hδ'0
    apply PowerSeries.map_injective (algebraMap (kN N) ℂ) Subtype.val_injective
    rw [h0, map_zero]
  have hfin := mul_right_cancel₀ hΔM0 hkey
  rw [hfin, PowerSeries.coeff_map, hφapp]

end Main

end SRecip
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.SRecip"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.SRecip"

open scoped MatrixGroups Manifold in
theorem solution (N : ℕ) [NeZero N] (m : ℕ)
    (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion N
        ((fun τ : UpperHalfPlane => G (ModularGroup.S • τ)) * ModularForm.discriminant ^ m)).coeff n =
          ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N
            ((fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ)) *
              ModularForm.discriminant ^ m)).coeff n = ι (σ (a n)) := by
  obtain ⟨a, ha, hb⟩ := SRecip.main m G hG hinv hbd hrat ι
  refine ⟨a, ha, fun σ c hσ γ hγb hγd n => ?_⟩
  have := hb σ c hσ γ hγb hγd n
  have hfun : (fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ)) = SRecip.cw G (ModularGroup.S * γ) := by
    funext τ; simp [SRecip.cw, mul_smul]
  rw [hfun]
  exact this

end S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion
end P2MW
export P2MW.S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion (solution)
