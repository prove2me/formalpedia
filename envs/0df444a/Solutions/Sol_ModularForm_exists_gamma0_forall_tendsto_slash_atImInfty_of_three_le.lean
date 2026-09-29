-- Prove2me | solution 1 for ModularForm.exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/55b407b4-4cfe-5abf-9d36-41b04b1004f6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Manifold Matrix

namespace A2EIS

open UpperHalfPlane EisensteinSeries CongruenceSubgroup Filter ModularForm

variable {N : ℕ} {k : ℤ}

abbrev redN (N : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) := ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))

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

theorem redN_T_zpow (m : ℤ) : redN N (ModularGroup.T ^ m) = !![1, (m : ZMod N); 0, 1] := by
  ext i j
  rw [redN_apply, show ((ModularGroup.T ^ m : SL(2, ℤ)) i j : ℤ) = (!![(1 : ℤ), m; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j from by
    rw [← ModularGroup.coe_T_zpow]]
  fin_cases i <;> fin_cases j <;> simp

theorem vecMul_zero_s (s : ZMod N) (M : Matrix (Fin 2) (Fin 2) (ZMod N)) : ![0, s] ᵥ* M = ![s * M 1 0, s * M 1 1] := by
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_zero_s_T_zpow (s : ZMod N) (m : ℤ) : ![0, s] ᵥ* redN N (ModularGroup.T ^ m) = ![0, s] := by
  rw [redN_T_zpow, vecMul_zero_s]
  simp

noncomputable def cst (k : ℤ) (a : Fin 2 → ZMod N) : ℂ :=
  (if a = ![0, 1] then 1 else 0) + (if a = ![0, -1] then ((-1 : ℂ)) ^ (-k) else 0)

noncomputable def lim (k : ℤ) (v : Fin 2 → ℤ) : ℂ := if v 0 = 0 then ((v 1 : ℂ)) ^ (-k) else 0

theorem tendsto_eisSummand (hk : 3 ≤ k) (v : Fin 2 → ℤ) :
    Tendsto (fun z : ℍ => eisSummand k v z) atImInfty (𝓝 (lim k v)) := by
  by_cases hv : v 0 = 0
  · have : (fun z : ℍ => eisSummand k v z) = fun _ => ((v 1 : ℂ)) ^ (-k) := by
      funext z; simp [eisSummand, hv]
    rw [this, lim, if_pos hv]
    exact tendsto_const_nhds
  · rw [lim, if_neg hv]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hk0 : -k < 0 := by omega
    have h1 : Tendsto (fun z : ℍ => (z.im : ℝ) ^ (-k)) atImInfty (𝓝 0) := by
      rw [atImInfty]
      exact (tendsto_zpow_atTop_zero hk0).comp tendsto_comap
    refine squeeze_zero (fun z => norm_nonneg _) (fun z => ?_) h1
    rw [eisSummand, norm_zpow]
    have hv1 : (1 : ℝ) ≤ |(v 0 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hv
    have him : (z.im : ℝ) ≤ ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ := by
      calc (z.im : ℝ) ≤ |(v 0 : ℝ)| * z.im := le_mul_of_one_le_left z.im_pos.le hv1
        _ = |((v 0 : ℂ) * (z : ℂ) + v 1).im| := by
            simp [Complex.add_im, Complex.mul_im, abs_mul, abs_of_pos z.im_pos]
        _ ≤ ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ := Complex.abs_im_le_norm _
    have hk' : 0 ≤ k := by omega
    rw [zpow_neg, zpow_neg]
    exact inv_anti₀ (zpow_pos z.im_pos k) (zpow_le_zpow_left₀ hk' z.im_pos.le him)

def stripFilter (N : ℕ) : Filter ℍ := atImInfty ⊓ 𝓟 (verticalStrip N 1)

theorem stripFilter_le (N : ℕ) : stripFilter N ≤ atImInfty := inf_le_left

theorem tendsto_eisensteinSeries_strip [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    Tendsto (eisensteinSeries a k) (stripFilter N) (𝓝 (∑' x : gammaSet N 1 a, lim k x)) := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have hkr : (0 : ℝ) ≤ k := by positivity
  set r₀ : ℝ := r ⟨⟨N, 1⟩, one_pos⟩ with hr₀
  refine tendsto_tsum_of_dominated_convergence (𝓕 := stripFilter N)
    (f := fun (z : ℍ) (x : gammaSet N 1 a) => eisSummand k x z)
    (bound := fun x : gammaSet N 1 a => r₀ ^ (-(k : ℝ)) * ‖(x : Fin 2 → ℤ)‖ ^ (-(k : ℝ))) ?_ ?_ ?_
  · exact ((summable_one_div_norm_rpow hk').mul_left (r₀ ^ (-(k : ℝ)))).subtype _
  · intro x
    exact (tendsto_eisSummand hk x).mono_left (stripFilter_le N)
  · have hmem : ∀ᶠ z in stripFilter N, z ∈ verticalStrip (N : ℝ) 1 :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [hmem] with z hz x
    rw [eisSummand, norm_zpow]
    exact_mod_cast summand_bound_of_mem_verticalStrip hkr (x : Fin 2 → ℤ) one_pos hz

theorem mem_gammaSet_iff_of_apply_zero {v : Fin 2 → ℤ} (hv : v 0 = 0) (a : Fin 2 → ZMod N) :
    v ∈ gammaSet N 1 a ↔ (v = ![0, 1] ∨ v = ![0, -1]) ∧ (↑) ∘ v = a := by
  constructor
  · rintro ⟨ha, hg⟩
    refine ⟨?_, ha⟩
    rw [hv, Int.gcd_zero_left] at hg
    have h1 : v 1 = 1 ∨ v 1 = -1 := by
      rcases Int.natAbs_eq (v 1) with h | h <;> [left; right] <;> rw [h, hg] <;> simp
    rcases h1 with h1 | h1
    · left; funext i; fin_cases i <;> simp [hv, h1]
    · right; funext i; fin_cases i <;> simp [hv, h1]
  · rintro ⟨h, ha⟩
    refine ⟨ha, ?_⟩
    rcases h with rfl | rfl <;> simp

theorem tsum_lim [NeZero N] (a : Fin 2 → ZMod N) : ∑' x : gammaSet N 1 a, lim k x = cst k a := by
  classical
  rw [tsum_subtype (gammaSet N 1 a) (lim k)]
  have hsupp : ∀ v : Fin 2 → ℤ, v ∉ ({![0, 1], ![0, -1]} : Finset (Fin 2 → ℤ)) →
      Set.indicator (gammaSet N 1 a) (lim k) v = 0 := by
    intro v hv
    by_cases hmem : v ∈ gammaSet N 1 a
    · rw [Set.indicator_of_mem hmem, lim]
      by_cases h0 : v 0 = 0
      · exfalso
        have := ((mem_gammaSet_iff_of_apply_zero h0 a).mp hmem).1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        exact hv this
      · rw [if_neg h0]
    · exact Set.indicator_of_notMem hmem _
  rw [tsum_eq_sum (s := ({![0, 1], ![0, -1]} : Finset (Fin 2 → ℤ))) (fun v hv => hsupp v hv)]
  have hne : (![0, 1] : Fin 2 → ℤ) ≠ ![0, -1] := by
    intro h; have := congrFun h 1; simp at this
  rw [Finset.sum_pair hne, cst]
  congr 1
  · by_cases h : (![0, 1] : Fin 2 → ℤ) ∈ gammaSet N 1 a
    · rw [Set.indicator_of_mem h, lim]
      have ha : a = ![0, 1] := by
        have := ((mem_gammaSet_iff_of_apply_zero (by simp) a).mp h).2
        rw [← this]; funext i; fin_cases i <;> simp
      simp [ha]
    · rw [Set.indicator_of_notMem h]
      have ha : a ≠ ![0, 1] := by
        intro ha; apply h
        exact (mem_gammaSet_iff_of_apply_zero (by simp) a).mpr ⟨Or.inl rfl, by rw [ha]; funext i; fin_cases i <;> simp⟩
      rw [if_neg ha]
  · by_cases h : (![0, -1] : Fin 2 → ℤ) ∈ gammaSet N 1 a
    · rw [Set.indicator_of_mem h, lim]
      have ha : a = ![0, -1] := by
        have := ((mem_gammaSet_iff_of_apply_zero (by simp) a).mp h).2
        rw [← this]; funext i; fin_cases i <;> simp
      simp [ha]
    · rw [Set.indicator_of_notMem h]
      have ha : a ≠ ![0, -1] := by
        intro ha; apply h
        exact (mem_gammaSet_iff_of_apply_zero (by simp) a).mpr ⟨Or.inr rfl, by rw [ha]; funext i; fin_cases i <;> simp⟩
      rw [if_neg ha]

theorem eisensteinSeries_T_zpow_smul [NeZero N] (a : Fin 2 → ZMod N) (m : ℤ) (z : ℍ) :
    eisensteinSeries a k (ModularGroup.T ^ ((N : ℤ) * m) • z) = eisensteinSeries a k z := by
  have h1 := congrFun (eisensteinSeries_slash_apply a k (ModularGroup.T ^ ((N : ℤ) * m))) z
  rw [SL_slash_apply, ModularGroup.denom_apply] at h1
  have hd : ((((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) 1 0 : ℤ) : ℂ)) * (z : ℂ)
      + (((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) 1 1 : ℤ) : ℂ) = 1 := by
    have hc : ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ) * m; 0, 1] :=
      ModularGroup.coe_T_zpow _
    rw [show ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) 1 0 : ℤ) = 0 from by
        rw [show ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) 1 0 : ℤ) = ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, hc]; rfl,
      show ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) 1 1 : ℤ) = 1 from by
        rw [show ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) 1 1 : ℤ) = ((ModularGroup.T ^ ((N : ℤ) * m) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl, hc]; rfl]
    simp
  rw [hd, one_zpow, mul_one] at h1
  have ha : a ᵥ* redN N (ModularGroup.T ^ ((N : ℤ) * m)) = a := by
    rw [redN_T_zpow]
    have : (((N : ℤ) * m : ℤ) : ZMod N) = 0 := by push_cast; simp
    rw [this]
    have : (!![(1 : ZMod N), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this, Matrix.vecMul_one]
  exact h1.trans (congrFun (congrArg (fun b => eisensteinSeries b k) ha) z)

theorem tendsto_eisensteinSeries [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    Tendsto (eisensteinSeries a k) atImInfty (𝓝 (cst k a)) := by
  have hstrip := tendsto_eisensteinSeries_strip hk a
  rw [tsum_lim] at hstrip

  choose n hn using fun z : ℍ => ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N)
  set red : ℍ → ℍ := fun z => ModularGroup.T ^ ((N : ℤ) * n z) • z with hred
  have hE : ∀ z, eisensteinSeries a k (red z) = eisensteinSeries a k z := fun z =>
    eisensteinSeries_T_zpow_smul a (n z) z
  have htend : Tendsto red atImInfty (stripFilter N) := by
    rw [stripFilter, tendsto_inf]
    constructor
    · rw [atImInfty, tendsto_comap_iff]
      have : UpperHalfPlane.im ∘ red = UpperHalfPlane.im := by
        funext z
        simp only [Function.comp_apply, hred, modular_T_zpow_smul, vadd_im]
      rw [this]
      exact tendsto_comap
    · rw [tendsto_principal]
      have hev : ∀ᶠ z : ℍ in atImInfty, (1 : ℝ) ≤ z.im := (atImInfty_mem _).mpr ⟨1, fun z hz => hz⟩
      filter_upwards [hev] with z hz
      exact verticalStrip_anti_right (N : ℝ) hz (hn z)
  exact (hstrip.comp htend).congr fun z => hE z

section Sym

theorem finset_sum_slash {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, F i) ∣[k] γ = ∑ i ∈ s, F i ∣[k] γ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, SlashAction.add_slash, ih]

theorem isBoundedAtImInfty_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsBoundedAtImInfty (F i)) : IsBoundedAtImInfty (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperHalfPlane.zero_form_isBoundedAtImInfty
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem mdifferentiable_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F i)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (c := (0 : ℂ)))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable (O : Finset (Fin 2 → ZMod N))

noncomputable def FO (k : ℤ) (O : Finset (Fin 2 → ZMod N)) : ℍ → ℂ := ∑ b ∈ O, eisensteinSeries b k

theorem FO_slash (γ : SL(2, ℤ)) : FO k O ∣[k] γ = ∑ b ∈ O, eisensteinSeries (b ᵥ* redN N γ) k := by
  rw [FO, finset_sum_slash]
  exact Finset.sum_congr rfl fun b _ => eisensteinSeries_slash_apply b k γ

def IsStable (O : Finset (Fin 2 → ZMod N)) : Prop := ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ b ∈ O, b ᵥ* redN N γ ∈ O

variable {O}

theorem FO_slash_of_mem (hO : IsStable O) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : FO k O ∣[k] γ = FO k O := by
  rw [FO_slash, FO]
  exact Finset.sum_nbij' (fun b => b ᵥ* redN N γ) (fun b => b ᵥ* redN N γ⁻¹) (fun b hb => hO γ hγ b hb)
    (fun b hb => hO γ⁻¹ (Subgroup.inv_mem _ hγ) b hb) (fun b _ => vecMul_redN_mul_inv b γ)
    (fun b _ => vecMul_redN_inv_mul b γ) (fun b _ => rfl)

theorem mdifferentiable_FO (hk : 3 ≤ k) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (FO k O) :=
  mdifferentiable_finset_sum O _ fun b _ => eisensteinSeriesSIF_mdifferentiable hk b

theorem isBoundedAtImInfty_FO_slash [NeZero N] (hk : 3 ≤ k) (γ : SL(2, ℤ)) : IsBoundedAtImInfty (FO k O ∣[k] γ) := by
  rw [FO_slash]
  refine isBoundedAtImInfty_finset_sum O _ fun b _ => ?_
  have h := isBoundedAtImInfty_eisensteinSeriesSIF b hk γ
  rw [show (⇑(eisensteinSeriesSIF b k) : ℍ → ℂ) = eisensteinSeries b k from rfl, eisensteinSeries_slash_apply] at h
  exact h

noncomputable def eisO [NeZero N] (hk : 3 ≤ k) (hO : IsStable O) : ModularForm (Gamma0 N) k where
  toFun := FO k O
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have h := FO_slash_of_mem (k := k) hO hγ
    rw [SL_slash] at h
    exact h
  holo' := mdifferentiable_FO hk
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    exact isBoundedAtImInfty_FO_slash hk γ

@[scoped simp] theorem coe_eisO [NeZero N] (hk : 3 ≤ k) (hO : IsStable O) : (⇑(eisO hk hO) : ℍ → ℂ) = FO k O := rfl

theorem tendsto_FO_slash [NeZero N] (hk : 3 ≤ k) (σ : SL(2, ℤ)) :
    Tendsto (fun z => (FO k O ∣[k] σ) z) atImInfty (𝓝 (∑ b ∈ O, cst k (b ᵥ* redN N σ))) := by
  rw [FO_slash]
  have : (fun z => (∑ b ∈ O, eisensteinSeries (b ᵥ* redN N σ) k) z)
      = fun z => ∑ b ∈ O, eisensteinSeries (b ᵥ* redN N σ) k z := by
    funext z; simp [Finset.sum_apply]
  rw [this]
  exact tendsto_finsetSum O fun b _ => tendsto_eisensteinSeries hk (b ᵥ* redN N σ)

end Sym

section Orbit

variable (N)

def Rel (σ σ' : SL(2, ℤ)) : Prop := ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧ ∃ j : ℤ, σ' = γ * σ * ModularGroup.T ^ j

theorem Rel.refl (σ : SL(2, ℤ)) : Rel N σ σ := ⟨1, Subgroup.one_mem _, 0, by simp⟩

variable {N}

theorem Rel.symm {σ σ' : SL(2, ℤ)} (h : Rel N σ σ') : Rel N σ' σ := by
  obtain ⟨γ, hγ, j, rfl⟩ := h
  exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, -j, by rw [zpow_neg]; group⟩

theorem Rel.trans {σ σ' σ'' : SL(2, ℤ)} (h : Rel N σ σ') (h' : Rel N σ' σ'') : Rel N σ σ'' := by
  obtain ⟨γ, hγ, j, rfl⟩ := h
  obtain ⟨γ', hγ', j', rfl⟩ := h'
  exact ⟨γ' * γ, Subgroup.mul_mem _ hγ' hγ, j + j', by rw [zpow_add]; group⟩

variable (N)

noncomputable def orb [NeZero N] (σ₀ : SL(2, ℤ)) : Finset (Fin 2 → ZMod N) := by
  classical
  exact Finset.univ.filter fun b => ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧
    (b = ![0, 1] ᵥ* redN N (σ₀⁻¹ * γ) ∨ b = ![0, -1] ᵥ* redN N (σ₀⁻¹ * γ))

variable {N} [NeZero N]

theorem mem_orb {σ₀ : SL(2, ℤ)} {b : Fin 2 → ZMod N} :
    b ∈ orb N σ₀ ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧
      (b = ![0, 1] ᵥ* redN N (σ₀⁻¹ * γ) ∨ b = ![0, -1] ᵥ* redN N (σ₀⁻¹ * γ)) := by
  classical
  simp [orb]

theorem isStable_orb (σ₀ : SL(2, ℤ)) : IsStable (orb N σ₀) := by
  intro γ hγ b hb
  rw [mem_orb] at hb ⊢
  obtain ⟨γ', hγ', h⟩ := hb
  refine ⟨γ' * γ, Subgroup.mul_mem _ hγ' hγ, ?_⟩
  rcases h with rfl | rfl
  · left; rw [← vecMul_redN_mul, mul_assoc]
  · right; rw [← vecMul_redN_mul, mul_assoc]

def cstN (a : Fin 2 → ZMod N) : ℕ := (if a = ![0, 1] then 1 else 0) + (if a = ![0, -1] then 1 else 0)

omit [NeZero N] in
theorem cst_eq_cstN (hke : Even k) (a : Fin 2 → ZMod N) : cst k a = (cstN a : ℂ) := by
  rw [cst, cstN, (even_neg.mpr hke).neg_one_zpow]
  push_cast
  rfl

omit [NeZero N] in
theorem cstN_ne_zero_iff (a : Fin 2 → ZMod N) : cstN a ≠ 0 ↔ a = ![0, 1] ∨ a = ![0, -1] := by
  unfold cstN
  by_cases h1 : a = ![0, 1] <;> by_cases h2 : a = ![0, -1] <;> simp [h1, h2]

omit [NeZero N] in
theorem cstN_vecMul_T_zpow (a : Fin 2 → ZMod N) (j : ℤ) : cstN (a ᵥ* redN N (ModularGroup.T ^ j)) = cstN a := by
  have key : ∀ s : ZMod N, a ᵥ* redN N (ModularGroup.T ^ j) = ![0, s] ↔ a = ![0, s] := by
    intro s
    constructor
    · intro h
      have := congrArg (fun c => c ᵥ* redN N (ModularGroup.T ^ j)⁻¹) h
      rw [vecMul_redN_mul_inv, ← zpow_neg, vecMul_zero_s_T_zpow] at this
      exact this
    · rintro rfl; exact vecMul_zero_s_T_zpow s j
  unfold cstN
  simp only [key 1, key (-1)]

noncomputable def mult (σ₀ σ : SL(2, ℤ)) : ℕ := ∑ b ∈ orb N σ₀, cstN (b ᵥ* redN N σ)

theorem mult_mul_T_zpow (σ₀ σ : SL(2, ℤ)) (j : ℤ) : mult (N := N) σ₀ (σ * ModularGroup.T ^ j) = mult (N := N) σ₀ σ := by
  unfold mult
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [vecMul_redN_mul, cstN_vecMul_T_zpow]

theorem mult_mul_left (σ₀ σ : SL(2, ℤ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    mult (N := N) σ₀ (γ * σ) = mult (N := N) σ₀ σ := by
  unfold mult
  refine Finset.sum_nbij' (fun b => b ᵥ* redN N γ) (fun b => b ᵥ* redN N γ⁻¹) (fun b hb => isStable_orb σ₀ γ hγ b hb)
    (fun b hb => isStable_orb σ₀ γ⁻¹ (Subgroup.inv_mem _ hγ) b hb) (fun b _ => vecMul_redN_mul_inv b γ)
    (fun b _ => vecMul_redN_inv_mul b γ) (fun b _ => ?_)
  rw [vecMul_redN_mul]

theorem mult_eq_of_rel (σ₀ : SL(2, ℤ)) {σ σ' : SL(2, ℤ)} (h : Rel N σ σ') : mult (N := N) σ₀ σ' = mult (N := N) σ₀ σ := by
  obtain ⟨γ, hγ, j, rfl⟩ := h
  rw [mult_mul_T_zpow, mult_mul_left σ₀ σ hγ]

theorem mult_self_ne_zero (σ₀ : SL(2, ℤ)) : mult (N := N) σ₀ σ₀ ≠ 0 := by
  intro h
  rw [mult, Finset.sum_eq_zero_iff] at h
  have hb : ![0, 1] ᵥ* redN N σ₀⁻¹ ∈ orb N σ₀ :=
    mem_orb.mpr ⟨1, Subgroup.one_mem _, Or.inl (by rw [mul_one])⟩
  have := h _ hb
  rw [vecMul_redN_inv_mul] at this
  simp [cstN] at this

omit [NeZero N] in

theorem redN_neg (γ : SL(2, ℤ)) : redN N (-γ) = -redN N γ := by
  ext i j; simp [Matrix.SpecialLinearGroup.coe_neg]

omit [NeZero N] in

theorem exists_mem_Gamma_of_vecMul_eq (δ : SL(2, ℤ)) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (h : ![0, 1] ᵥ* redN N δ = ![0, (s : ZMod N)]) :
    ∃ (ε : SL(2, ℤ)) (κ : SL(2, ℤ)) (j : ℤ), (ε = 1 ∨ ε = -1) ∧ κ ∈ Gamma N ∧ δ = ε * κ * ModularGroup.T ^ j := by

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

theorem rel_of_mult_ne_zero {σ₀ σ : SL(2, ℤ)} (h : mult (N := N) σ₀ σ ≠ 0) : Rel N σ₀ σ := by
  rw [mult] at h
  obtain ⟨b, hb, hbσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [cstN_ne_zero_iff] at hbσ
  rw [mem_orb] at hb
  obtain ⟨γ, hγ, hbε⟩ := hb

  set δ : SL(2, ℤ) := σ₀⁻¹ * γ * σ with hδ
  obtain ⟨t, ht, hvec⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ ![0, 1] ᵥ* redN N δ = ![0, (t : ZMod N)] := by
    have hε : ∀ (e : ZMod N), ![0, e] = e • (![0, 1] : Fin 2 → ZMod N) := by
      intro e; funext i; fin_cases i <;> simp

    have hb1 : ∀ e : ZMod N, (![0, e] ᵥ* redN N (σ₀⁻¹ * γ)) ᵥ* redN N σ = e • (![0, 1] ᵥ* redN N δ) := by
      intro e
      rw [← vecMul_redN_mul, hδ, hε e, Matrix.smul_vecMul]
    rcases hbε with rfl | rfl <;> rcases hbσ with hs | hs
    · refine ⟨1, Or.inl rfl, ?_⟩
      have := hb1 1; rw [one_smul] at this; rw [← this, hs]; simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have := hb1 1; rw [one_smul] at this; rw [← this, hs]; simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have := hb1 (-1)
      rw [hs] at this
      have h2 := congrArg (fun c => (-1 : ZMod N) • c) this
      simp only [smul_smul, mul_neg, mul_one, neg_neg, one_smul] at h2
      rw [← h2]; funext i; fin_cases i <;> simp
    · refine ⟨1, Or.inl rfl, ?_⟩
      have := hb1 (-1)
      rw [hs] at this
      have h2 := congrArg (fun c => (-1 : ZMod N) • c) this
      simp only [smul_smul, mul_neg, mul_one, neg_neg, one_smul] at h2
      rw [← h2]; funext i; fin_cases i <;> simp
  obtain ⟨ε, κ, j, hε, hκ, hδε⟩ := exists_mem_Gamma_of_vecMul_eq δ t ht hvec

  have hεmem : ε ∈ Gamma0 N := by
    rcases hε with rfl | rfl
    · exact Subgroup.one_mem _
    · rw [Gamma0_mem]; simp
  have hεcomm : σ₀ * ε = ε * σ₀ := by rcases hε with rfl | rfl <;> simp
  have hconj : σ₀ * κ * σ₀⁻¹ ∈ Gamma0 N := by
    have : σ₀ * κ * σ₀⁻¹ ∈ Gamma N := (Gamma_normal N).conj_mem _ hκ σ₀
    rw [Gamma_mem] at this; rw [Gamma0_mem]; exact this.2.2.1
  refine ⟨γ⁻¹ * ε * (σ₀ * κ * σ₀⁻¹), Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hεmem) hconj, j, ?_⟩
  have hσ : σ = γ⁻¹ * σ₀ * δ := by rw [hδ]; group
  rw [hσ, hδε]
  calc γ⁻¹ * σ₀ * (ε * κ * ModularGroup.T ^ j) = γ⁻¹ * (σ₀ * ε) * κ * ModularGroup.T ^ j := by group
    _ = γ⁻¹ * (ε * σ₀) * κ * ModularGroup.T ^ j := by rw [hεcomm]
    _ = γ⁻¹ * ε * (σ₀ * κ * σ₀⁻¹) * σ₀ * ModularGroup.T ^ j := by group

end Orbit

section Main

variable (N) [NeZero N]

noncomputable def rep (q : SL(2, ℤ) ⧸ Gamma0 N) : SL(2, ℤ) := q.out⁻¹

omit [NeZero N] in
theorem rel_rep_mk_inv (σ : SL(2, ℤ)) : Rel N (rep N (QuotientGroup.mk σ⁻¹ : SL(2, ℤ) ⧸ Gamma0 N)) σ := by
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 N) σ⁻¹
  refine ⟨(γ : SL(2, ℤ)), γ.2, 0, ?_⟩
  rw [rep, hγ, zpow_zero, mul_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

variable {N}

theorem main (hk : 3 ≤ k) (hke : Even k) (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ) :
    ∃ f : ModularForm (Gamma0 N) k, ∀ σ : SL(2, ℤ),
      Tendsto (fun τ => ((⇑f) ∣[k] σ) τ) atImInfty (𝓝 (v σ)) := by
  classical
  letI := (Gamma0 N).fintypeQuotientOfFiniteIndex

  let cls : SL(2, ℤ) → Finset (SL(2, ℤ) ⧸ Gamma0 N) := fun σ => Finset.univ.filter fun q => Rel N (rep N q) σ
  have hcls_eq : ∀ {σ σ' : SL(2, ℤ)}, Rel N σ σ' → cls σ = cls σ' := by
    intro σ σ' h
    ext q
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hq => hq.trans h, fun hq => hq.trans h.symm⟩
  have hcls_pos : ∀ σ : SL(2, ℤ), 0 < (cls σ).card := by
    intro σ
    refine Finset.card_pos.mpr ⟨QuotientGroup.mk σ⁻¹, ?_⟩
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    exact rel_rep_mk_inv N σ

  let c : SL(2, ℤ) ⧸ Gamma0 N → ℂ := fun q =>
    v (rep N q) / ((mult (N := N) (rep N q) (rep N q) : ℂ) * ((cls (rep N q)).card : ℂ))
  let f : ModularForm (Gamma0 N) k := ∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q • eisO (N := N) hk (isStable_orb (rep N q))
  refine ⟨f, fun σ => ?_⟩

  have hcoe : (⇑f : ℍ → ℂ) = ∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q • FO k (orb N (rep N q)) := by
    simp only [f]
    rw [show (⇑(∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q • eisO (N := N) hk (isStable_orb (rep N q))) : ℍ → ℂ)
      = ∑ q : SL(2, ℤ) ⧸ Gamma0 N, (⇑(c q • eisO (N := N) hk (isStable_orb (rep N q))) : ℍ → ℂ) from ?_]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [ModularForm.IsGLPos.coe_smul, coe_eisO]
    · induction (Finset.univ : Finset (SL(2, ℤ) ⧸ Gamma0 N)) using Finset.induction_on with
      | empty => simp
      | insert q s hq ih => rw [Finset.sum_insert hq, Finset.sum_insert hq, ModularForm.coe_add, ih]
  have hslash : (⇑f) ∣[k] σ = ∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q • (FO k (orb N (rep N q)) ∣[k] σ) := by
    rw [hcoe, finset_sum_slash]
    exact Finset.sum_congr rfl fun q _ => by rw [ModularForm.SL_smul_slash]

  have hlim : Tendsto (fun τ => ((⇑f) ∣[k] σ) τ) atImInfty
      (𝓝 (∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q * (mult (N := N) (rep N q) σ : ℂ))) := by
    rw [hslash]
    have : (fun τ => (∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q • (FO k (orb N (rep N q)) ∣[k] σ)) τ)
        = fun τ => ∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q * (FO k (orb N (rep N q)) ∣[k] σ) τ := by
      funext τ; simp [Finset.sum_apply]
    rw [this]
    refine tendsto_finsetSum _ fun q _ => ?_
    have h := (tendsto_FO_slash hk (O := orb N (rep N q)) σ).const_mul (c q)
    have hval : (∑ b ∈ orb N (rep N q), cst k (b ᵥ* redN N σ)) = (mult (N := N) (rep N q) σ : ℂ) := by
      rw [mult, Nat.cast_sum]
      exact Finset.sum_congr rfl fun b _ => cst_eq_cstN hke _
    rw [hval] at h
    exact h

  have hsum : (∑ q : SL(2, ℤ) ⧸ Gamma0 N, c q * (mult (N := N) (rep N q) σ : ℂ)) = v σ := by
    have hzero : ∀ q ∈ (Finset.univ : Finset (SL(2, ℤ) ⧸ Gamma0 N)), q ∉ cls σ → c q * (mult (N := N) (rep N q) σ : ℂ) = 0 := by
      intro q _ hq
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have : mult (N := N) (rep N q) σ = 0 := by
        by_contra hne; exact hq (rel_of_mult_ne_zero hne)
      rw [this, Nat.cast_zero, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ (cls σ)) hzero]
    have hterm : ∀ q ∈ cls σ, c q * (mult (N := N) (rep N q) σ : ℂ) = v σ / ((cls σ).card : ℂ) := by
      intro q hq
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hq

      have h1 : mult (N := N) (rep N q) σ = mult (N := N) (rep N q) (rep N q) := mult_eq_of_rel _ hq
      have h2 : v (rep N q) = v σ := by
        obtain ⟨γ, hγ, j, hσ⟩ := hq
        rw [hσ, hv _ γ hγ j]
      have h3 : cls (rep N q) = cls σ := hcls_eq hq
      have hm : (mult (N := N) (rep N q) (rep N q) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (mult_self_ne_zero _)
      simp only [c, h1, h2, h3]
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hc0 : ((cls σ).card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hcls_pos σ).ne'
    field_simp
  rw [hsum] at hlim
  exact hlim

end Main

end A2EIS
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le.A2EIS"

theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (hk : 3 ≤ k) (hke : Even k) (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) k, ∀ σ : SL(2, ℤ),
      Filter.Tendsto (fun τ => ((⇑f) ∣[k] σ) τ) UpperHalfPlane.atImInfty (𝓝 (v σ)) :=
  A2EIS.main hk hke v hv

end S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le
end P2MW
export P2MW.S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le (solution)
