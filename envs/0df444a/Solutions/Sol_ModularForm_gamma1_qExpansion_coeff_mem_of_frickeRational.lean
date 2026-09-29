-- Prove2me | solution 1 for ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bb1dc1ba-7302-505f-904b-1284bc51e5db

import Mathlib
import Theorems.Thm_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient
import Theorems.Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeToInfinity

local notation "Δ" => ModularForm.discriminant

theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL

theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) :=
  ModularFormClass.bdd_at_infty CuspForm.discriminant

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

variable (N : ℕ) [NeZero N]

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
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

theorem qExpansion_coeff_one_eq_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion 1 g).coeff n = (qExpansion N g).coeff (N * n) := by
  rw [qExpansion_coeff_widthN N hg hper hbd, if_pos (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)]

theorem ratCast_mem (K : IntermediateField ℚ ℂ) (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

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

theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, IsGLPos.smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using qExpansion_E₄_rat
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using qExpansion_E₆_rat
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc n]
  split_ifs with h
  · exact qExpansion_disc_rat_one _
  · exact ⟨0, by simp⟩

section PowerSeriesK

variable (K : IntermediateField ℚ ℂ)

def CoeffIn (p : PowerSeries ℂ) : Prop := ∀ n, p.coeff n ∈ K

variable {K}

theorem CoeffIn.exists_map {p : PowerSeries ℂ} (h : CoeffIn K p) :
    ∃ p₀ : PowerSeries K, p₀.map (algebraMap K ℂ) = p := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h n⟩, ?_⟩
  ext n
  simp

theorem coeffIn_map (p₀ : PowerSeries K) : CoeffIn K (p₀.map (algebraMap K ℂ)) := fun n => by
  rw [PowerSeries.coeff_map]; exact (p₀.coeff n).2

theorem CoeffIn.mul {p q : PowerSeries ℂ} (hp : CoeffIn K p) (hq : CoeffIn K q) : CoeffIn K (p * q) := by
  obtain ⟨p₀, rfl⟩ := hp.exists_map
  obtain ⟨q₀, rfl⟩ := hq.exists_map
  rw [← map_mul]; exact coeffIn_map q₀ |> fun _ => coeffIn_map (p₀ * q₀)

theorem CoeffIn.pow {p : PowerSeries ℂ} (hp : CoeffIn K p) (n : ℕ) : CoeffIn K (p ^ n) := by
  obtain ⟨p₀, rfl⟩ := hp.exists_map
  rw [← map_pow]; exact coeffIn_map _

theorem coeffIn_of_rat {p : PowerSeries ℂ} (h : ∀ n, ∃ r : ℚ, p.coeff n = (r : ℂ)) : CoeffIn K p := by
  intro n; obtain ⟨r, hr⟩ := h n; rw [hr]; exact ratCast_mem K r

theorem CoeffIn.of_mul_X_pow {p : PowerSeries ℂ} {r : ℕ} (h : CoeffIn K (p * PowerSeries.X ^ r)) :
    CoeffIn K p := by
  intro n
  have := h (n + r)
  rwa [PowerSeries.coeff_mul_X_pow] at this

theorem CoeffIn.of_mul_unit {p V : PowerSeries ℂ} (hpV : CoeffIn K (p * V)) (hV : CoeffIn K V)
    (hV0 : PowerSeries.constantCoeff V = 1) : CoeffIn K p := by
  obtain ⟨V₀, hV₀⟩ := hV.exists_map
  obtain ⟨T₀, hT₀⟩ := hpV.exists_map
  have hunit : IsUnit V₀ := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h1 : algebraMap K ℂ (PowerSeries.constantCoeff V₀) = 1 := by
      rw [← hV0, ← hV₀, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    have : PowerSeries.constantCoeff V₀ = 1 := by
      apply (algebraMap K ℂ).injective
      rw [h1, map_one]
    rw [this]; exact isUnit_one
  obtain ⟨u, hu⟩ := hunit
  have hVne : V ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [hV0, map_zero] at this
    exact one_ne_zero this
  have key : p = (T₀ * ↑u⁻¹).map (algebraMap K ℂ) := by
    apply mul_right_cancel₀ hVne
    rw [← hT₀]
    conv_rhs => rw [← hV₀, ← hu, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  rw [key]; exact coeffIn_map _

end PowerSeriesK

theorem exists_mvPolynomial_map {ι : Type*} (K : IntermediateField ℚ ℂ) (R : MvPolynomial ι ℂ)
    (h : ∀ mo, R.coeff mo ∈ K) : ∃ R₀ : MvPolynomial ι K, R₀.map (algebraMap K ℂ) = R := by
  classical
  refine ⟨∑ mo ∈ R.support, MvPolynomial.monomial mo ⟨R.coeff mo, h mo⟩, ?_⟩
  rw [map_sum]
  ext mo'
  simp only [MvPolynomial.map_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff] at hm; exact hm.symm

section Main

variable {N}
variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})

local notation "Γ₁ℝ" M => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_Gamma1 (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

theorem step_up {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {M : ℕ}
    (h : Periodic ((G * Δ ^ M) ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ M) ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ M)).coeff n ∈ K) :
    Periodic ((G * Δ ^ (M + 1)) ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ (M + 1)) ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ (M + 1))).coeff n ∈ K := by
  obtain ⟨hper, hbdd, hmem⟩ := h
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G * Δ ^ M) := hG.mul (mdifferentiable_disc.pow M)
  have hΔN : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) N := periodic_ofComplex_natCast periodic_disc_one N
  have heq : G * Δ ^ (M + 1) = (G * Δ ^ M) * Δ := by rw [pow_succ, ← mul_assoc]
  rw [heq]
  refine ⟨periodic_mul hper hΔN, hbdd.mul isBoundedAtImInfty_disc, fun n => ?_⟩
  rw [qExpansion_mul (analyticAt_cuspFunction_zero (natCast_pos N) hper hmd hbdd)
    (analyticAt_cuspFunction_zero (natCast_pos N) hΔN mdifferentiable_disc isBoundedAtImInfty_disc),
    PowerSeries.coeff_mul]
  refine sum_mem fun ij _ => mul_mem (hmem _) ?_
  obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
  rw [hr]; exact ratCast_mem K r

theorem step_up_le {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {M M' : ℕ} (hMM' : M ≤ M')
    (h : Periodic ((G * Δ ^ M) ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ M) ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ M)).coeff n ∈ K) :
    Periodic ((G * Δ ^ M') ∘ ofComplex) N ∧ IsBoundedAtImInfty (G * Δ ^ M') ∧
      ∀ n : ℕ, (qExpansion N (G * Δ ^ M')).coeff n ∈ K := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMM'
  induction d with
  | zero => simpa using h
  | succ d ih => exact step_up K hG (ih (Nat.le_add_right M d))

include hL hW hfricke hjf hK in
theorem main (k : ℤ) (a b m : ℕ)
    (f : ModularForm (Γ₁ℝ N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ mo, P.coeff mo ∈ K) (hQK : ∀ mo, Q.coeff mo ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) P τ)
    (n : ℕ) :
    (qExpansion 1 ⇑f).coeff n ∈ K := by
  classical
  set gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
    fun o => o.elim jf fun v => fricke v.1 with hgen

  let G : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m
  have hΔm : ∀ τ : ℍ, Δ τ ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    have hnum : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ * (E₄ τ ^ a * E₆ τ ^ b)) :=
      f.holo'.mul ((E₄.holo'.pow a).mul (E₆.holo'.pow b))
    have hinv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => (Δ τ ^ m)⁻¹) := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have h1 := UpperHalfPlane.mdifferentiable_iff.1 (mdifferentiable_disc.pow m)
      have h2 : DifferentiableOn ℂ (fun z : ℂ => ((((Δ : ℍ → ℂ) ^ m) ∘ ofComplex) z)⁻¹) {z | 0 < z.im} :=
        h1.inv fun z hz => by
          simp only [comp_apply, Pi.pow_apply]
          exact pow_ne_zero _ (discriminant_ne_zero _)
      exact h2.congr fun z _ => by simp [comp_apply]
    have : G = fun τ => (f τ * (E₄ τ ^ a * E₆ τ ^ b)) * (Δ τ ^ m)⁻¹ := by
      funext τ; simp only [G, div_eq_mul_inv]
    rw [this]
    exact hnum.mul hinv
  have hGQ : G * MvPolynomial.aeval gen Q = MvPolynomial.aeval gen P := by
    funext τ
    simp only [Pi.mul_apply, G]
    rw [div_mul_eq_mul_div, div_eq_iff (hΔm τ), hid τ, mul_comm]

  obtain ⟨P₀, hP₀⟩ := exists_mvPolynomial_map K P hPK
  obtain ⟨Q₀, hQ₀⟩ := exists_mvPolynomial_map K Q hQK
  have hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0 :=
    WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke hfricke jf hjf K hK
      G hGhol P₀ Q₀ (by rw [hQ₀]; exact hQ0) (by rw [hQ₀, hP₀]; exact hGQ)
  obtain ⟨M₀, hM₀⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N L hL W hW
    fricke hfricke jf hjf K hK hGhol P Q hPK hQK hQ0 hGQ hint

  set M₁ : ℕ := M₀ + m with hM₁
  obtain ⟨hperN, hbddN, hmemN⟩ := step_up_le K hGhol (Nat.le_add_right M₀ m) hM₀

  let Emf : ModularForm 𝒮ℒ (a * 4 + b * 6 + M₀ * 12) :=
    ((E₄.pow a).mul (E₆.pow b)).mul ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow M₀)
  have hEmf : (⇑Emf : ℍ → ℂ) = fun τ => E₄ τ ^ a * E₆ τ ^ b * Δ τ ^ M₀ := by
    funext τ; simp [Emf]
  have hgeq : G * Δ ^ M₁ = (⇑f : ℍ → ℂ) * ⇑Emf := by
    funext τ
    have hΔ' := hΔm τ
    simp only [Pi.mul_apply, Pi.pow_apply, hEmf, G, hM₁, pow_add]
    field_simp
  have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) * ⇑Emf) := f.holo'.mul Emf.holo'
  have hgper : Periodic (((⇑f : ℍ → ℂ) * ⇑Emf) ∘ ofComplex) 1 :=
    periodic_mul (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma1 N))
      (SlashInvariantFormClass.periodic_comp_ofComplex Emf one_mem_strictPeriods_SL)
  have hgbdd : IsBoundedAtImInfty ((⇑f : ℍ → ℂ) * ⇑Emf) :=
    (ModularFormClass.bdd_at_infty f).mul (ModularFormClass.bdd_at_infty Emf)

  have hS : CoeffIn K (qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑Emf)) := by
    intro j
    rw [qExpansion_coeff_one_eq_widthN N hghol hgper hgbdd, ← hgeq]
    exact hmemN _

  have hprod : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑Emf) = qExpansion 1 ⇑f * qExpansion 1 ⇑Emf :=
    qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma1 N))
      (ModularFormClass.analyticAt_cuspFunction_zero Emf one_pos one_mem_strictPeriods_SL)

  set qΔ : PowerSeries ℂ := qExpansion 1 (Δ : ℍ → ℂ) with hqΔ
  set D₀ : PowerSeries ℂ := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) qΔ with hD₀
  have hqΔ0 : PowerSeries.constantCoeff qΔ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hqΔ]
    exact CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  have hqΔeq : qΔ = D₀ * PowerSeries.X := by
    conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const qΔ, hqΔ0, map_zero, add_zero]
  have hD₀0 : PowerSeries.constantCoeff D₀ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hD₀, PowerSeries.coeff_mk, zero_add, hqΔ]
    exact discriminant_qExpansion_coeff_one
  have hD₀K : CoeffIn K D₀ := by
    intro j
    rw [hD₀, PowerSeries.coeff_mk, hqΔ]
    obtain ⟨r, hr⟩ := qExpansion_disc_rat_one (j + 1)
    rw [hr]; exact ratCast_mem K r
  set V : PowerSeries ℂ := qExpansion 1 (E₄ : ℍ → ℂ) ^ a * qExpansion 1 (E₆ : ℍ → ℂ) ^ b * D₀ ^ M₀
    with hV
  have hEmf_q : qExpansion 1 ⇑Emf = V * PowerSeries.X ^ M₀ := by
    have h1 : qExpansion 1 ⇑Emf = qExpansion 1 (E₄ : ℍ → ℂ) ^ a * qExpansion 1 (E₆ : ℍ → ℂ) ^ b *
        qΔ ^ M₀ := by
      simp only [Emf, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hqΔ]
      rfl
    rw [h1, hqΔeq, mul_pow, hV]
    ring
  have hVK : CoeffIn K V := by
    rw [hV]
    exact ((coeffIn_of_rat qExpansion_E₄_rat).pow a).mul ((coeffIn_of_rat qExpansion_E₆_rat).pow b)
      |>.mul (hD₀K.pow M₀)
  have hV0 : PowerSeries.constantCoeff V = 1 := by
    have h4 : PowerSeries.constantCoeff (qExpansion 1 (E₄ : ℍ → ℂ)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₄]
      exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
    have h6 : PowerSeries.constantCoeff (qExpansion 1 (E₆ : ℍ → ℂ)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₆]
      exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨3, rfl⟩
    rw [hV, map_mul, map_mul, map_pow, map_pow, map_pow, h4, h6, hD₀0]
    simp

  have hT : CoeffIn K (qExpansion 1 ⇑f * V) := by
    apply CoeffIn.of_mul_X_pow (r := M₀)
    rw [mul_assoc, ← hEmf_q, ← hprod]
    exact hS
  exact CoeffIn.of_mul_unit hT hVK hV0 n

end Main

end FrickeToInfinity

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem solution
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (k : ℤ) (a b m : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ mo, P.coeff mo ∈ K) (hQK : ∀ mo, Q.coeff mo ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) P τ)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 ⇑f).coeff n ∈ K :=
  FrickeToInfinity.main L hL W hW fricke hfricke jf hjf K hK k a b m f P Q hPK hQK hQ0 hid n

end S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational
end P2MW
export P2MW.S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational (solution)
