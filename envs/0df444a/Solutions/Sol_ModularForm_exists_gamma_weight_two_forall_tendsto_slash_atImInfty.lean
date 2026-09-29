-- Prove2me | solution 1 for ModularForm.exists_gamma_weight_two_forall_tendsto_slash_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d07e7b97-3c58-5047-915e-1afe8a03dac0

import Mathlib
import Theorems.Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
import Theorems.Thm_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty

set_option autoImplicit false

open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix Real
p2m_open "UpperHalfPlane~I"
open Complex Filter CongruenceSubgroup

noncomputable section

namespace EIS2K5

variable {N : ℕ}

abbrev redN (N : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))

theorem redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN N γ i j = ((γ i j : ℤ) : ZMod N) := rfl

theorem redN_mul (γ δ : SL(2, ℤ)) : redN N (γ * δ) = redN N γ * redN N δ := by
  simp [redN, Matrix.SpecialLinearGroup.coe_mul]

theorem redN_one : redN N 1 = 1 := by simp [redN]

theorem vecMul_redN_mul (b : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    b ᵥ* redN N (γ * δ) = (b ᵥ* redN N γ) ᵥ* redN N δ := by
  rw [redN_mul, Matrix.vecMul_vecMul]

theorem vecMul_redN_one (b : Fin 2 → ZMod N) : b ᵥ* redN N 1 = b := by rw [redN_one, Matrix.vecMul_one]

theorem vecMul_redN_mul_inv (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : (b ᵥ* redN N γ) ᵥ* redN N γ⁻¹ = b := by
  rw [← vecMul_redN_mul, mul_inv_cancel, vecMul_redN_one]

theorem vecMul_redN_inv_mul (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : (b ᵥ* redN N γ⁻¹) ᵥ* redN N γ = b := by
  rw [← vecMul_redN_mul, inv_mul_cancel, vecMul_redN_one]

theorem redN_of_mem_Gamma {γ : SL(2, ℤ)} (hγ : γ ∈ Γ(N)) : redN N γ = 1 := by
  rw [redN, Gamma_mem'.mp hγ]; rfl

theorem redN_T_zpow (m : ℤ) : redN N (ModularGroup.T ^ m) = !![1, (m : ZMod N); 0, 1] := by
  ext i j
  rw [redN_apply, show ((ModularGroup.T ^ m : SL(2, ℤ)) i j : ℤ) = (!![(1 : ℤ), m; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j from by
    rw [← ModularGroup.coe_T_zpow]]
  fin_cases i <;> fin_cases j <;> simp

theorem redN_neg (γ : SL(2, ℤ)) : redN N (-γ) = -redN N γ := by
  ext i j; simp [Matrix.SpecialLinearGroup.coe_neg]

theorem vecMul_zero_s (s : ZMod N) (M : Matrix (Fin 2) (Fin 2) (ZMod N)) : ![0, s] ᵥ* M = ![s * M 1 0, s * M 1 1] := by
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_zero_s_T_zpow (s : ZMod N) (m : ℤ) : ![0, s] ᵥ* redN N (ModularGroup.T ^ m) = ![0, s] := by
  rw [redN_T_zpow, vecMul_zero_s]
  simp

theorem exists_mem_Gamma_of_vecMul_eq (δ : SL(2, ℤ)) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (h : ![0, 1] ᵥ* redN N δ = ![0, (s : ZMod N)]) :
    ∃ (ε : SL(2, ℤ)) (κ : SL(2, ℤ)) (j : ℤ), (ε = 1 ∨ ε = -1) ∧ κ ∈ Γ(N) ∧ δ = ε * κ * ModularGroup.T ^ j := by
  obtain ⟨ε, hε, δ', hδ', h10, h11⟩ : ∃ (ε : SL(2, ℤ)), (ε = 1 ∨ ε = -1) ∧ ∃ δ' : SL(2, ℤ), δ = ε * δ' ∧
      ((δ' 1 0 : ℤ) : ZMod N) = 0 ∧ ((δ' 1 1 : ℤ) : ZMod N) = 1 := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [vecMul_zero_s] at h0 h1
    simp only [one_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, redN_apply] at h0 h1
    rcases hs with rfl | rfl
    · refine ⟨1, Or.inl rfl, δ, by rw [one_mul], h0, ?_⟩
      simpa using h1
    · refine ⟨-1, Or.inr rfl, -δ, by simp, ?_, ?_⟩
      · simp [Matrix.SpecialLinearGroup.coe_neg, h0]
      · simp [Matrix.SpecialLinearGroup.coe_neg, h1]
  have hδ'0 : δ' ∈ Gamma0 N := by rw [Gamma0_mem]; exact h10
  have h00 : ((δ' 0 0 : ℤ) : ZMod N) = 1 := by
    have hmem : (⟨δ', hδ'0⟩ : Gamma0 N) ∈ Gamma1' N := by
      rw [Gamma1_mem']
      change ((δ' 1 1 : ℤ) : ZMod N) = 1
      exact h11
    exact ((Gamma1_to_Gamma0_mem ⟨δ', hδ'0⟩).mp hmem).1
  set b : ℤ := δ' 0 1 with hb
  refine ⟨ε, δ' * ModularGroup.T ^ (-b), b, hε, ?_, ?_⟩
  · rw [Gamma_mem]
    have hc : ((ModularGroup.T ^ (-b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -b; 0, 1] := ModularGroup.coe_T_zpow _
    have hm : ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![1, -b; 0, 1] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hc]
    have e00 : ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) 0 0 : ℤ) = δ' 0 0 := by
      change ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = _
      rw [hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    have e01 : ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) 0 1 : ℤ) = -(δ' 0 0 * b) + δ' 0 1 := by
      change ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = _
      rw [hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    have e10 : ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) 1 0 : ℤ) = δ' 1 0 := by
      change ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
      rw [hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    have e11 : ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) 1 1 : ℤ) = -(δ' 1 0 * b) + δ' 1 1 := by
      change ((δ' * ModularGroup.T ^ (-b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = _
      rw [hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e00]; exact h00
    · rw [e01]; push_cast; rw [h00, hb]; ring
    · rw [e10]; exact h10
    · rw [e11]; push_cast; rw [h10, h11]; ring
  · rw [hδ', zpow_neg]; group

section W

variable (N) [NeZero N]

lemma indep_tau (τ : ℍ) : LinearIndependent ℝ ![(τ : ℂ), 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.smul_im, UpperHalfPlane.coe_im, smul_eq_mul, Complex.one_im, mul_zero,
    add_zero, Complex.zero_im] at him
  have hs : s = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact h'
    · exact absurd h' τ.im_ne_zero
  subst hs
  have hre := congrArg Complex.re h
  simp only [zero_smul, zero_add, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one, Complex.zero_re] at hre
  exact ⟨rfl, hre⟩

def Lτ (τ : ℍ) : PeriodPair := ⟨(τ : ℂ), 1, indep_tau τ⟩

lemma hLτ : ∀ τ : ℍ, (Lτ τ).ω₁ = (τ : ℂ) ∧ (Lτ τ).ω₂ = 1 := fun _ => ⟨rfl, rfl⟩

def W (b : Fin 2 → ZMod N) : ℍ → ℂ := fun τ => (Lτ τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)

def f (t : ZMod N) : ℂ := (π : ℂ) ^ 2 / Complex.sin (π * t.val / N) ^ 2

def g (b : Fin 2 → ZMod N) : ℂ := if b 0 = 0 then f N (b 1) else 0

def cst (b : Fin 2 → ZMod N) : ℂ := -((π : ℂ) ^ 2 / 3) + g N b

variable {N}

theorem card_W (b : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) 2, ⇑F = W N b) ∧
    (∀ γ : SL(2, ℤ), W N b ∣[(2 : ℤ)] γ = W N (b ᵥ* redN N γ)) ∧
    (b ≠ 0 → Tendsto (W N b) atImInfty (𝓝 (cst N b))) := by
  have h := PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty (Lτ) hLτ N b
  simp only at h
  exact h

def MF (b : Fin 2 → ZMod N) : ModularForm Γ(N) 2 := (card_W b).1.choose

theorem coe_MF (b : Fin 2 → ZMod N) : ⇑(MF b) = W N b := (card_W b).1.choose_spec

theorem W_slash (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : W N b ∣[(2 : ℤ)] γ = W N (b ᵥ* redN N γ) := (card_W b).2.1 γ

theorem tendsto_W {b : Fin 2 → ZMod N} (hb : b ≠ 0) : Tendsto (W N b) atImInfty (𝓝 (cst N b)) := (card_W b).2.2 hb

omit [NeZero N] in
theorem W_zero : W N 0 = 0 := by
  funext τ
  simp [W, PeriodPair.weierstrassP_zero]

omit [NeZero N] in
theorem vecMul_ne_zero {b : Fin 2 → ZMod N} (hb : b ≠ 0) (γ : SL(2, ℤ)) : b ᵥ* redN N γ ≠ 0 := by
  intro h
  apply hb
  have := congrArg (fun c => c ᵥ* redN N γ⁻¹) h
  simpa only [vecMul_redN_mul_inv, Matrix.zero_vecMul] using this

end W

section CT

variable [NeZero N]

def e (N : ℕ) : Fin 2 → ZMod N := ![0, 1]

def u (N : ℕ) (σ : SL(2, ℤ)) : Fin 2 → ZMod N := e N ᵥ* redN N σ⁻¹

omit [NeZero N] in
theorem smul_e (t : ZMod N) : t • e N = ![0, t] := by
  funext i; fin_cases i <;> simp [e]

omit [NeZero N] in
theorem eq_vec (c : Fin 2 → ZMod N) : c = ![c 0, c 1] := by
  funext i; fin_cases i <;> simp

omit [NeZero N] in
theorem u_vecMul (σ ρ : SL(2, ℤ)) : u N σ ᵥ* redN N ρ = e N ᵥ* redN N (σ⁻¹ * ρ) := by
  rw [u, vecMul_redN_mul]

def vecMulEquiv (σ : SL(2, ℤ)) : (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) where
  toFun b := b ᵥ* redN N σ
  invFun b := b ᵥ* redN N σ⁻¹
  left_inv b := vecMul_redN_mul_inv b σ
  right_inv b := vecMul_redN_inv_mul b σ

theorem sum_vecMul_eq (F : (Fin 2 → ZMod N) → ℂ) (σ : SL(2, ℤ)) :
    ∑ b, F (b ᵥ* redN N σ) = ∑ b, F b :=
  Fintype.sum_equiv (vecMulEquiv σ) _ _ fun _ => rfl

theorem sum_g_vecMul (d : (Fin 2 → ZMod N) → ℂ) (σ : SL(2, ℤ)) :
    ∑ b, d b * g N (b ᵥ* redN N σ) = ∑ t : ZMod N, f N t * d (t • u N σ) := by

  have h1 : ∑ b, d b * g N (b ᵥ* redN N σ) = ∑ c, d (c ᵥ* redN N σ⁻¹) * g N c := by
    rw [← sum_vecMul_eq (fun c => d (c ᵥ* redN N σ⁻¹) * g N c) σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [vecMul_redN_mul_inv]
  rw [h1]

  rw [← Fintype.sum_equiv (finTwoArrowEquiv (ZMod N)).symm
    (fun p => d (![p.1, p.2] ᵥ* redN N σ⁻¹) * g N ![p.1, p.2]) (fun c => d (c ᵥ* redN N σ⁻¹) * g N c)
    (fun p => rfl), Fintype.sum_prod_type]
  simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod N)]
  simp only [Finset.mem_univ, if_true]
  rw [mul_comm, u, ← Matrix.smul_vecMul, smul_e]

end CT

section Delta

variable [NeZero N] (hK : (ZMod N)ˣ → ℂ)

def d₀ (b : Fin 2 → ZMod N) : ℂ := if h : b 0 = 0 ∧ IsUnit (b 1) then hK h.2.unit else 0

def n (N : ℕ) (σ ρ : SL(2, ℤ)) : ℕ := (if u N σ ᵥ* redN N ρ = e N then 1 else 0) + (if u N σ ᵥ* redN N ρ = -e N then 1 else 0)

theorem sum_dite_isUnit (F : (ZMod N)ˣ → ℂ) (G : ZMod N → ℂ) :
    ∑ t : ZMod N, G t * (if h : IsUnit t then F h.unit else 0) = ∑ t : (ZMod N)ˣ, G t * F t := by
  classical
  have hmap : (Finset.univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩
      = Finset.univ.filter fun j : ZMod N => IsUnit j := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, Finset.mem_filter]
    exact ⟨fun ⟨w, hw⟩ => ⟨w, hw⟩, fun ⟨w, hw⟩ => ⟨w, hw⟩⟩
  symm
  calc ∑ t : (ZMod N)ˣ, G t * F t
      = ∑ j ∈ (Finset.univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩,
          G j * (if h : IsUnit j then F h.unit else 0) := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [Function.Embedding.coeFn_mk, Units.isUnit, dif_pos, IsUnit.unit_of_val_units]
    _ = ∑ j ∈ Finset.univ.filter (fun j : ZMod N => IsUnit j), G j * (if h : IsUnit j then F h.unit else 0) := by
        rw [hmap]
    _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hj <;> simp

variable {hK}

theorem sum_d₀ (hK_spec : ∀ s : (ZMod N)ˣ,
      ∑ t : (ZMod N)ˣ, f N (t : ZMod N) * hK (t * s) = (if s = 1 then 1 else 0) + (if s = -1 then 1 else 0))
    (σ ρ : SL(2, ℤ)) :
    ∑ b, d₀ hK (b ᵥ* redN N ρ) * g N (b ᵥ* redN N σ) = (n N σ ρ : ℂ) := by
  classical

  have h1 : ∑ b, d₀ hK (b ᵥ* redN N ρ) * g N (b ᵥ* redN N σ) = ∑ c, d₀ hK c * g N (c ᵥ* redN N (ρ⁻¹ * σ)) := by
    rw [← sum_vecMul_eq (fun c => d₀ hK c * g N (c ᵥ* redN N (ρ⁻¹ * σ))) ρ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← vecMul_redN_mul, mul_inv_cancel_left]
  rw [h1, sum_g_vecMul]
  have hU : u N (ρ⁻¹ * σ) = u N σ ᵥ* redN N ρ := by
    rw [u_vecMul, u, mul_inv_rev, inv_inv]
  rw [hU]
  set U : Fin 2 → ZMod N := u N σ ᵥ* redN N ρ with hUdef
  by_cases h0 : U 0 = 0
  ·
    have hdet : (redN N (σ⁻¹ * ρ)).det = 1 := Matrix.SpecialLinearGroup.det_coe _
    have hU' : U = ![redN N (σ⁻¹ * ρ) 1 0, redN N (σ⁻¹ * ρ) 1 1] := by
      rw [hUdef, u_vecMul, e, vecMul_zero_s]; simp
    have hU0 : redN N (σ⁻¹ * ρ) 1 0 = 0 := by
      have := congrFun hU' 0; simp only [Matrix.cons_val_zero] at this; rw [← this]; exact h0
    have hunit : IsUnit (U 1) := by
      rw [Matrix.det_fin_two, hU0, mul_zero, sub_zero] at hdet
      have hU1 : U 1 = redN N (σ⁻¹ * ρ) 1 1 := by
        have := congrFun hU' 1; simpa using this
      rw [hU1]
      exact IsUnit.of_mul_eq_one_right _ hdet
    set s : (ZMod N)ˣ := hunit.unit with hs
    have hUs : U = ![0, (s : ZMod N)] := by
      rw [eq_vec U, h0, hs, IsUnit.unit_spec]

    have hd : ∀ t : ZMod N, d₀ hK (t • U) = if h : IsUnit t then hK (h.unit * s) else 0 := by
      intro t
      have ht : t • U = ![0, t * s] := by
        rw [hUs]; funext i; fin_cases i <;> simp
      rw [d₀, ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
      by_cases htu : IsUnit t
      · have htsu : IsUnit (t * (s : ZMod N)) := htu.mul s.isUnit
        rw [dif_pos htsu, dif_pos htu]
        congr 1
        ext
        simp [IsUnit.unit_spec]
      · have htsu : ¬ IsUnit (t * (s : ZMod N)) := by
          intro h'
          apply htu
          simpa using h'.mul s⁻¹.isUnit
        rw [dif_neg htsu, dif_neg htu]
    simp_rw [hd]
    rw [sum_dite_isUnit (fun w => hK (w * s)) (f N), hK_spec s]

    have he1 : (U = e N) ↔ s = 1 := by
      rw [hUs, e]
      constructor
      · intro h'
        have := congrFun h' 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
        exact Units.val_eq_one.mp this
      · intro h'; rw [h']; simp
    have he2 : (U = -e N) ↔ s = -1 := by
      rw [hUs, e]
      constructor
      · intro h'
        have := congrFun h' 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.neg_apply] at this
        exact Units.val_injective (by simpa using this)
      · intro h'; rw [h']; funext i; fin_cases i <;> simp
    rw [n, if_congr he1 rfl rfl, if_congr he2 rfl rfl]
    push_cast
    rfl
  ·
    have hd : ∀ t : ZMod N, d₀ hK (t • U) = 0 := by
      intro t
      rw [d₀, dif_neg]
      rintro ⟨ht0, ht1⟩
      simp only [Pi.smul_apply, smul_eq_mul] at ht0 ht1
      have htu : IsUnit t := isUnit_of_mul_isUnit_left ht1
      exact h0 ((htu.mul_right_eq_zero).mp ht0)
    simp_rw [hd, mul_zero, Finset.sum_const_zero]
    have hne1 : U ≠ e N := by
      intro h'; apply h0; rw [h', e]; simp
    have hne2 : U ≠ -e N := by
      intro h'; apply h0; rw [h', e]; simp
    rw [n, if_neg hne1, if_neg hne2]
    simp

theorem apply_eq_of_n_ne_zero (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ(N) → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hneg : ∀ σ : SL(2, ℤ), v (-σ) = v σ) {σ ρ : SL(2, ℤ)} (h : n N σ ρ ≠ 0) : v ρ = v σ := by

  obtain ⟨t, ht, hvec⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ ![0, 1] ᵥ* redN N (σ⁻¹ * ρ) = ![0, (t : ZMod N)] := by
    rw [n] at h
    have hU : u N σ ᵥ* redN N ρ = ![0, 1] ᵥ* redN N (σ⁻¹ * ρ) := by rw [u_vecMul, e]
    by_cases h1 : u N σ ᵥ* redN N ρ = e N
    · exact ⟨1, Or.inl rfl, by rw [← hU, h1, e]; simp⟩
    · by_cases h2 : u N σ ᵥ* redN N ρ = -e N
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [← hU, h2, e]
        funext i; fin_cases i <;> simp
      · rw [if_neg h1, if_neg h2] at h; exact absurd rfl h
  obtain ⟨ε, κ, j, hε, hκ, hδ⟩ := exists_mem_Gamma_of_vecMul_eq (σ⁻¹ * ρ) t ht hvec
  have hρ : ρ = ε * ((σ * κ * σ⁻¹) * σ * ModularGroup.T ^ j) := by
    have hεcomm : σ * ε = ε * σ := by rcases hε with rfl | rfl <;> simp
    calc ρ = σ * (σ⁻¹ * ρ) := by group
      _ = σ * (ε * κ * ModularGroup.T ^ j) := by rw [hδ]
      _ = (σ * ε) * κ * ModularGroup.T ^ j := by group
      _ = (ε * σ) * κ * ModularGroup.T ^ j := by rw [hεcomm]
      _ = ε * ((σ * κ * σ⁻¹) * σ * ModularGroup.T ^ j) := by group
  have hconj : σ * κ * σ⁻¹ ∈ Γ(N) := (Gamma_normal N).conj_mem _ hκ σ
  rw [hρ]
  rcases hε with rfl | rfl
  · rw [one_mul, hv σ _ hconj j]
  · rw [neg_one_mul, hneg, hv σ _ hconj j]

end Delta

section Count

variable [NeZero N]

scoped instance normalGamma (N : ℕ) : (Γ(N)).Normal := Gamma_normal N

scoped instance fintypeQuot (N : ℕ) [NeZero N] : Fintype (SL(2, ℤ) ⧸ Γ(N)) := Subgroup.fintypeQuotientOfFiniteIndex

def ρq (q : SL(2, ℤ) ⧸ Γ(N)) : SL(2, ℤ) := q.out⁻¹

def Mcount (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) : ℕ := ∑ q : SL(2, ℤ) ⧸ Γ(N), n N σ (ρq q)

omit [NeZero N] in
theorem n_eq_n_one (σ ρ : SL(2, ℤ)) : n N σ ρ = n N 1 (σ⁻¹ * ρ) := by
  simp only [n, u_vecMul, inv_one, one_mul]

omit [NeZero N] in
theorem n_one_mul_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Γ(N)) (ρ : SL(2, ℤ)) : n N 1 (γ * ρ) = n N 1 ρ := by
  simp only [n, u_vecMul, inv_one, one_mul, redN_mul, redN_of_mem_Gamma hγ, one_mul]

theorem ρq_mul_mk (q : SL(2, ℤ) ⧸ Γ(N)) (σ : SL(2, ℤ)) :
    ∃ γ : SL(2, ℤ), γ ∈ Γ(N) ∧ ρq (q * QuotientGroup.mk σ) = γ * (σ⁻¹ * ρq q) := by
  have hq : q * (QuotientGroup.mk σ : SL(2, ℤ) ⧸ Γ(N)) = QuotientGroup.mk (q.out * σ) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.mk_mul]
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (Γ(N)) (q.out * σ)
  refine ⟨(γ : SL(2, ℤ))⁻¹, Subgroup.inv_mem _ γ.2, ?_⟩
  rw [ρq, ρq, hq, hγ]
  group

theorem Mcount_eq (σ : SL(2, ℤ)) : Mcount N σ = Mcount N 1 := by
  unfold Mcount
  have h1 : ∀ q : SL(2, ℤ) ⧸ Γ(N), n N σ (ρq q) = n N 1 (ρq (q * QuotientGroup.mk σ)) := by
    intro q
    obtain ⟨γ, hγ, hq⟩ := ρq_mul_mk q σ
    rw [hq, n_one_mul_of_mem hγ, n_eq_n_one]
  simp_rw [h1]
  have h2 : ∀ q : SL(2, ℤ) ⧸ Γ(N), n N 1 (ρq q) = n N 1 (1⁻¹ * ρq q) := fun q => by rw [inv_one, one_mul]
  simp_rw [h2, ← n_eq_n_one]
  exact Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk σ : SL(2, ℤ) ⧸ Γ(N))) _ _ fun q => rfl

theorem Mcount_pos : 0 < Mcount N 1 := by
  unfold Mcount
  have hq : 0 < n N 1 (ρq (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ(N))) := by
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (Γ(N)) (1 : SL(2, ℤ))
    rw [ρq, hγ, one_mul, show ((γ : SL(2, ℤ))⁻¹) = (γ : SL(2, ℤ))⁻¹ * 1 by rw [mul_one],
      n_one_mul_of_mem (Subgroup.inv_mem _ γ.2)]
    simp [n, u, e, redN_one]
  exact lt_of_lt_of_le hq (Finset.single_le_sum (f := fun q => n N 1 (ρq q)) (fun q _ => Nat.zero_le _) (Finset.mem_univ _))

end Count

section Main

variable [NeZero N]

theorem finset_sum_slash {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) (k : ℤ) :
    (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, F i ∣[k] γ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, SlashAction.add_slash, ih]

theorem eq_zero_of_one (hN : N = 1) (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ(N) → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ Γ(N), v q.out⁻¹ = 0) (σ : SL(2, ℤ)) : v σ = 0 := by
  subst hN
  have hall : ∀ x y : SL(2, ℤ), v x = v y := by
    intro x y
    have hmem : x * y⁻¹ ∈ Γ(1) := by rw [Gamma_one_top]; trivial
    have := hv y (x * y⁻¹) hmem 0
    simpa using this
  rw [finsum_eq_sum_of_fintype] at hsum
  have hc : ∑ q : SL(2, ℤ) ⧸ Γ(1), v q.out⁻¹ = ∑ q : SL(2, ℤ) ⧸ Γ(1), v σ :=
    Finset.sum_congr rfl fun q _ => hall _ _
  rw [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (Fintype.card (SL(2, ℤ) ⧸ Γ(1)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp hsum).resolve_left hcard

theorem main (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Γ(N) → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hneg : ∀ σ : SL(2, ℤ), v (-σ) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ Γ(N), v q.out⁻¹ = 0) :
    ∃ f : ModularForm Γ(N) 2, ∀ σ : SL(2, ℤ),
      Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) atImInfty (𝓝 (v σ)) := by
  classical
  by_cases hN1 : N = 1
  · refine ⟨0, fun σ => ?_⟩
    rw [eq_zero_of_one hN1 v hv hsum σ]
    have : (⇑(0 : ModularForm Γ(N) 2)) ∣[(2 : ℤ)] σ = 0 := by
      rw [ModularForm.coe_zero]; exact SlashAction.zero_slash _ _
    rw [this]
    exact tendsto_const_nhds
  have hN2 : 2 ≤ N := by
    have := NeZero.pos N
    omega
  obtain ⟨hK, hK_spec⟩ := ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq N hN2

  set Mc : ℂ := (Mcount N 1 : ℂ) with hMc
  have hMc0 : Mc ≠ 0 := by rw [hMc]; exact_mod_cast (Mcount_pos (N := N)).ne'
  have hsum' : ∑ q : SL(2, ℤ) ⧸ Γ(N), v (ρq q) = 0 := by
    rw [finsum_eq_sum_of_fintype] at hsum; exact hsum
  let c : (Fin 2 → ZMod N) → ℂ := fun b =>
    Mc⁻¹ * ∑ q : SL(2, ℤ) ⧸ Γ(N), v (ρq q) * (d₀ hK (b ᵥ* redN N (ρq q)) - d₀ hK b)
  have hc0 : c 0 = 0 := by
    simp only [c, Matrix.zero_vecMul, sub_self, mul_zero, Finset.sum_const_zero]

  have hcsum : ∑ b, c b = 0 := by
    simp only [c, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ q : SL(2, ℤ) ⧸ Γ(N),
        ∑ b : Fin 2 → ZMod N, v (ρq q) * (d₀ hK (b ᵥ* redN N (ρq q)) - d₀ hK b) = 0 := by
      intro q
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_vecMul_eq (d₀ hK) (ρq q), sub_self, mul_zero]
    simp only [this, Finset.sum_const_zero, mul_zero]

  have hcg : ∀ σ : SL(2, ℤ), ∑ b, c b * g N (b ᵥ* redN N σ) = v σ := by
    intro σ
    have h1 : ∑ b, c b * g N (b ᵥ* redN N σ)
        = Mc⁻¹ * ∑ q : SL(2, ℤ) ⧸ Γ(N), v (ρq q) * ((n N σ (ρq q) : ℂ) - (n N σ 1 : ℂ)) := by
      have h2 : ∀ q : SL(2, ℤ) ⧸ Γ(N),
          ∑ b, v (ρq q) * (d₀ hK (b ᵥ* redN N (ρq q)) - d₀ hK b) * g N (b ᵥ* redN N σ)
            = v (ρq q) * ((n N σ (ρq q) : ℂ) - (n N σ 1 : ℂ)) := by
        intro q
        rw [← sum_d₀ hK_spec σ (ρq q), ← sum_d₀ hK_spec σ 1, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [vecMul_redN_one]; ring
      simp only [c]
      simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => h2 q
    rw [h1, Finset.sum_congr rfl fun q _ => mul_sub (v (ρq q)) _ _, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hsum', zero_mul, sub_zero]
    have h3 : ∀ q : SL(2, ℤ) ⧸ Γ(N), v (ρq q) * (n N σ (ρq q) : ℂ) = v σ * (n N σ (ρq q) : ℂ) := by
      intro q
      by_cases hq : n N σ (ρq q) = 0
      · rw [hq]; simp
      · rw [apply_eq_of_n_ne_zero v hv hneg hq]
    rw [Finset.sum_congr rfl fun q _ => h3 q, ← Finset.mul_sum]
    have h4 : (∑ q : SL(2, ℤ) ⧸ Γ(N), (n N σ (ρq q) : ℂ)) = Mc := by
      rw [hMc, ← Mcount_eq σ, Mcount, Nat.cast_sum]
    rw [h4]
    field_simp

  let fMF : ModularForm Γ(N) 2 := ∑ b : Fin 2 → ZMod N, c b • MF b
  refine ⟨fMF, fun σ => ?_⟩
  have hcoe : (⇑fMF : ℍ → ℂ) = ∑ b : Fin 2 → ZMod N, c b • W N b := by
    simp only [fMF]
    rw [show (⇑(∑ b : Fin 2 → ZMod N, c b • MF b) : ℍ → ℂ)
      = ∑ b : Fin 2 → ZMod N, (⇑(c b • MF (N := N) b) : ℍ → ℂ) from ?_]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [ModularForm.IsGLPos.coe_smul, coe_MF]
    · induction (Finset.univ : Finset (Fin 2 → ZMod N)) using Finset.induction_on with
      | empty => simp
      | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ModularForm.coe_add, ih]
  have hslash : (⇑fMF) ∣[(2 : ℤ)] σ = ∑ b : Fin 2 → ZMod N, c b • W N (b ᵥ* redN N σ) := by
    rw [hcoe, finset_sum_slash]
    exact Finset.sum_congr rfl fun b _ => by rw [ModularForm.SL_smul_slash, W_slash]
  have hlim : Tendsto (fun τ => ((⇑fMF) ∣[(2 : ℤ)] σ) τ) atImInfty
      (𝓝 (∑ b : Fin 2 → ZMod N, c b * cst N (b ᵥ* redN N σ))) := by
    rw [hslash]
    have : (fun τ => (∑ b : Fin 2 → ZMod N, c b • W N (b ᵥ* redN N σ)) τ)
        = fun τ => ∑ b : Fin 2 → ZMod N, c b * W N (b ᵥ* redN N σ) τ := by
      funext τ; simp [Finset.sum_apply]
    rw [this]
    refine tendsto_finsetSum _ fun b _ => ?_
    by_cases hb : b = 0
    · subst hb
      rw [hc0]
      simp only [zero_mul]
      exact tendsto_const_nhds
    · exact (tendsto_W (vecMul_ne_zero hb σ)).const_mul (c b)
  have hval : (∑ b : Fin 2 → ZMod N, c b * cst N (b ᵥ* redN N σ)) = v σ := by
    simp only [cst, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hcsum, zero_mul, zero_add]
    exact hcg σ
  rw [hval] at hlim
  exact hlim

end Main

end EIS2K5
p2m_reactivate "P2MW.S_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty.EIS2K5"

end
p2m_reactivate "P2MW.S_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty.EIS2K5"

theorem solution (N : ℕ) [NeZero N] (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hneg : ∀ σ : SL(2, ℤ), v (-σ) = v σ)
    (hsum : ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma N) 2, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[(2 : ℤ)] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) :=
  EIS2K5.main v hv hneg hsum

end S_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty
end P2MW
export P2MW.S_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty (solution)
