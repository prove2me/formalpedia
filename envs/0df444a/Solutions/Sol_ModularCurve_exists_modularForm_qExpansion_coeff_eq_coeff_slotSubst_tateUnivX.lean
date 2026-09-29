-- Prove2me | solution 1 for ModularCurve.exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f8eeabf2-f095-5efc-801b-5e94e7e2d1c7

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
import Theorems.Thm_WLight_weierstrassP_qExpansion_package
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "UpperHalfPlane~I"
open Complex ModularForm CongruenceSubgroup Matrix ConjAct
open scoped MatrixGroups ModularForm Real Topology Pointwise

namespace NonToricDivision

abbrev levelGroup (N : ℕ) : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 (N ^ 2)

scoped instance (N : ℕ) [NeZero N] : (levelGroup N).FiniteIndex := by
  unfold levelGroup; infer_instance

theorem T_mem_levelGroup (N : ℕ) : ModularGroup.T ∈ levelGroup N := by
  refine ⟨?_, ?_⟩
  · simp [Gamma1_mem, ModularGroup.T]
  · simp [Gamma0_mem, ModularGroup.T]

def diagInt (N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1]

theorem diagInt_map_eq {N : ℕ} (hN : N ≠ 0) :
    (diagInt N).map (algebraMap ℤ ℝ) =
      ((heckeDiagMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hN]; unfold diagInt
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_cocycle {N : ℕ} [NeZero N] {γ : SL(2, ℤ)} (hγ : γ ∈ levelGroup N) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma N ∧
      diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagInt N := by
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  obtain ⟨ha, hd, -⟩ := h1
  have hc : ((N ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp h0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha'
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb'
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc'
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd'
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha', hb', hc', hd']; exact Matrix.eta_fin_two _
  obtain ⟨c₀, hc₀⟩ := hc
  push_cast at hc₀
  have hdet' : Matrix.det !![a, (N : ℤ) * b; (N : ℤ) * c₀, d] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + b * hc₀
  refine ⟨⟨_, hdet'⟩, ?_, ?_⟩
  · rw [Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ((a : ℤ) : ZMod N) = 1; exact ha
    · show (((N : ℤ) * b : ℤ) : ZMod N) = 0; push_cast; rw [ZMod.natCast_self, zero_mul]
    · show (((N : ℤ) * c₀ : ℤ) : ZMod N) = 0; push_cast; rw [ZMod.natCast_self, zero_mul]
    · show ((d : ℤ) : ZMod N) = 1; exact hd
  · show diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, (N : ℤ) * b; (N : ℤ) * c₀, d] * diagInt N
    rw [hγmat]; unfold diagInt
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show ((N : ℤ) * a + 0 * c : ℤ) = a * (N : ℤ) + (N : ℤ) * b * 0; ring
    · show ((N : ℤ) * b + 0 * d : ℤ) = a * 0 + (N : ℤ) * b * 1; ring
    · show (0 * a + 1 * c : ℤ) = (N : ℤ) * c₀ * (N : ℤ) + d * 0; linear_combination hc₀
    · show (0 * b + 1 * d : ℤ) = (N : ℤ) * c₀ * 0 + d * 1; ring

theorem heckeDiagMatrix_mul_eq {N : ℕ} (hN : N ≠ 0) {γ γ' : SL(2, ℤ)}
    (hconj : diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagInt N) :
    heckeDiagMatrix N * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix N := by
  have mapGL_coe_eq : ∀ s : SL(2, ℤ),
      ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := fun _ => rfl
  have map_int_mul_eq : ∀ A B : Matrix (Fin 2) (Fin 2) ℤ,
      (A * B).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * B.map (algebraMap ℤ ℝ) := by
    intro A B
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← diagInt_map_eq hN, mapGL_coe_eq, mapGL_coe_eq,
    ← map_int_mul_eq, ← map_int_mul_eq, hconj]

theorem levelGroup_le_conj (N : ℕ) [NeZero N] :
    ((levelGroup N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (heckeDiagMatrix N)⁻¹ • ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  intro A hA
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hA
  obtain ⟨γ', hγ', hconj⟩ := exists_cocycle hγ
  have hGL := heckeDiagMatrix_mul_eq (NeZero.ne N) hconj
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  have : heckeDiagMatrix N * Matrix.SpecialLinearGroup.mapGL ℝ γ * (heckeDiagMatrix N)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ γ' := by
    rw [hGL, mul_inv_cancel_right]
  rw [this]
  exact Subgroup.mem_map.mpr ⟨γ', hγ', rfl⟩

def stdPair (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have him := congrArg Complex.im hst
    simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_eq_mul, mul_zero, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im] at him
    have hs : s = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h τ.im_pos.ne'
    subst hs
    have hre := congrArg Complex.re hst
    simp at hre
    exact ⟨rfl, hre⟩

theorem stdPair_spec (τ : ℍ) : (stdPair τ).ω₁ = (τ : ℂ) ∧ (stdPair τ).ω₂ = 1 := ⟨rfl, rfl⟩

local notation "Γᴸ(" N ")" => ((levelGroup N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def rawW (N a b : ℕ) (τ : ℍ) : ℂ :=
  (stdPair τ).weierstrassP ((((![(b : ZMod N), (a : ZMod N)] : Fin 2 → ZMod N) 0).val * (τ : ℂ) +
    ((![(b : ZMod N), (a : ZMod N)] : Fin 2 → ZMod N) 1).val) / N)

theorem rawW_eq (N a b : ℕ) [NeZero N] (ha : a < N) (hb : b < N) (τ : ℍ) :
    rawW N a b τ = (stdPair τ).weierstrassP (((b : ℂ) * (τ : ℂ) + a) / N) := by
  simp only [rawW, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb]

theorem exists_modularForm_gamma (N a b : ℕ) [NeZero N] :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      ⇑F = rawW N a b := by
  obtain ⟨h1, -, -⟩ :=
    PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty stdPair stdPair_spec N
      ![(b : ZMod N), (a : ZMod N)]
  exact h1

theorem exists_modularForm_levelGroup (N a b : ℕ) [NeZero N] (ha : a < N) (hb : b < N) :
    ∃ F : ModularForm Γᴸ(N) 2, ∀ τ : ℍ,
      F τ = ((2 * π * I) ^ 2)⁻¹ *
        (stdPair (heckeDiagMatrix N • τ)).weierstrassP
          (((b : ℂ) * ((heckeDiagMatrix N • τ : ℍ) : ℂ) + a) / N) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨F₀, hF₀⟩ := exists_modularForm_gamma N a b
  let F₁ := ModularForm.translate F₀ (heckeDiagMatrix N)
  let F₂ : ModularForm Γᴸ(N) 2 := ModularCurve.restrictForm (levelGroup_le_conj N) F₁
  refine ⟨(((2 * π * I) ^ 2)⁻¹ * (N : ℂ)⁻¹) • F₂, fun τ => ?_⟩
  rw [ModularForm.IsGLPos.smul_apply, smul_eq_mul]
  have h2 : F₂ τ = ((⇑F₀ : ℍ → ℂ) ∣[(2 : ℤ)] heckeDiagMatrix N) τ := rfl
  rw [h2, slash_heckeDiagMatrix_apply 2 hN, hF₀, rawW_eq N a b ha hb]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have : ((N : ℂ) ^ ((2 : ℤ) - 1)) = N := by norm_num
  rw [this]
  field_simp

theorem exists_modularForm_pointwise (N a b : ℕ) [NeZero N] (ha : a < N) (hb0 : 0 < b)
    (hb : b < N) :
    ∃ F : ModularForm Γᴸ(N) 2, ∀ τ : ℍ,
      F τ =
        cexp (2 * π * I / N) ^ a * cexp (2 * π * I * (τ : ℂ)) ^ b /
            (1 - cexp (2 * π * I / N) ^ a * cexp (2 * π * I * (τ : ℂ)) ^ b) ^ 2 +
          1 / 12 +
          ∑' p : ℕ+ × ℕ+, ((p.2 : ℕ) : ℂ) *
            (cexp (2 * π * I / N) ^ (a * (p.2 : ℕ)) *
                cexp (2 * π * I * (τ : ℂ)) ^ (((p.1 : ℕ) * N + b) * (p.2 : ℕ)) +
              (cexp (2 * π * I / N))⁻¹ ^ (a * (p.2 : ℕ)) *
                cexp (2 * π * I * (τ : ℂ)) ^ (((p.1 : ℕ) * N - b) * (p.2 : ℕ)) -
              2 * cexp (2 * π * I * (τ : ℂ)) ^ ((p.1 : ℕ) * N * (p.2 : ℕ))) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨F, hF⟩ := exists_modularForm_levelGroup N a b ha hb
  obtain ⟨-, -, -, hpkg, -⟩ := WLight.weierstrassP_qExpansion_package
  obtain ⟨hpt, -⟩ := hpkg stdPair stdPair_spec N b a hb ha (Or.inl hb0.ne')
  refine ⟨F, fun τ => ?_⟩
  rw [hF τ, hpt (heckeDiagMatrix N • τ)]
  have hτ : cexp (2 * π * I * ((heckeDiagMatrix N • τ : ℍ) : ℂ) / N) = cexp (2 * π * I * (τ : ℂ)) := by
    rw [coe_heckeDiagMatrix_smul hN]
    congr 1
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp
  rw [hτ]
  have h2pi : ((2 * π * I) ^ 2 : ℂ) ≠ 0 := by
    apply pow_ne_zero; simp [Real.pi_ne_zero, I_ne_zero]
  rw [← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]

section Regroup

variable {κ : Type*}

theorem hasSum_regroup (w : κ → ℂ) (e : κ → ℕ) (q : ℂ) (S : ℕ → Finset κ)
    (hS : ∀ n k, k ∈ S n ↔ e k = n) (hsum : Summable fun k => w k * q ^ e k) :
    HasSum (fun n => (∑ k ∈ S n, w k) * q ^ n) (∑' k, w k * q ^ e k) := by
  set f : κ → ℂ := fun k => w k * q ^ e k with hf_def
  have hf : HasSum f (∑' k, f k) := hsum.hasSum
  have hσ : HasSum (f ∘ Equiv.sigmaFiberEquiv e) (∑' k, f k) :=
    (Equiv.sigmaFiberEquiv e).hasSum_iff.mpr hf
  refine hσ.sigma fun n => ?_
  letI : Fintype {k // e k = n} :=
    Fintype.ofFinset (S n) (fun k => hS n k)
  have h1 : HasSum (fun c : {k // e k = n} => (f ∘ Equiv.sigmaFiberEquiv e) ⟨n, c⟩)
      (∑ c : {k // e k = n}, f c.1) := hasSum_fintype _
  convert h1 using 1
  rw [← Finset.sum_subtype (S n) (fun k => hS n k) f, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  show w k * q ^ n = w k * q ^ e k
  rw [(hS n k).mp hk]

end Regroup

section Summable

theorem summable_double (y q : ℂ) (hy : ‖y‖ ≤ 1) (hq : ‖q‖ < 1) (E : ℕ × ℕ → ℕ)
    (hE : ∀ p, p.1 + p.2 + 1 ≤ E p) :
    Summable fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℂ) * y ^ (p.2 + 1) * q ^ E p := by
  set r : ℝ := ‖q‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := hq

  have hgeo : Summable fun i : ℕ => r ^ i := summable_geometric_of_lt_one hr0 hr1
  have hlin : Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) * r ^ (j + 1) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by rwa [Real.norm_of_nonneg hr0])
    simp only [pow_one] at h
    exact (summable_nat_add_iff 1).mpr h
  have hdom : Summable fun p : ℕ × ℕ => r ^ p.1 * (((p.2 + 1 : ℕ) : ℝ) * r ^ (p.2 + 1)) :=
    hgeo.mul_of_nonneg hlin (fun i => pow_nonneg hr0 i)
      (fun j => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _))
  refine Summable.of_norm_bounded hdom fun p => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, ← hr]
  have hy' : ‖y‖ ^ (p.2 + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hy
  have hrE : r ^ E p ≤ r ^ (p.1 + (p.2 + 1)) :=
    pow_le_pow_of_le_one hr0 hr1.le (by have := hE p; omega)
  calc ((p.2 + 1 : ℕ) : ℝ) * ‖y‖ ^ (p.2 + 1) * r ^ E p
      ≤ ((p.2 + 1 : ℕ) : ℝ) * 1 * r ^ (p.1 + (p.2 + 1)) := by
        gcongr
    _ = r ^ p.1 * (((p.2 + 1 : ℕ) : ℝ) * r ^ (p.2 + 1)) := by rw [pow_add]; ring

end Summable

section Fibres

variable (N b n : ℕ)

def window (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p => (p.1 + 1) * (p.2 + 1) ≤ n

theorem mem_window {n : ℕ} {p : ℕ × ℕ} : p ∈ window n ↔ (p.1 + 1) * (p.2 + 1) ≤ n := by
  simp only [window, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩ <;> nlinarith

theorem sum_divisors_eq_sum_window (Φ : ℕ → ℕ → ℂ) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, Φ M e =
      ∑ p ∈ window n, Φ ((p.1 + 1) * (p.2 + 1)) (p.2 + 1) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => (x.1 / x.2 - 1, x.2 - 1))
    (fun p => ⟨(p.1 + 1) * (p.2 + 1), p.2 + 1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨hM, ⟨k, rfl⟩, hM0⟩ := hx
    have he : 0 < e := Nat.pos_of_ne_zero (fun h => hM0 (by simp [h]))
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => hM0 (by simp [h]))
    rw [mem_window]
    simp only [Nat.mul_div_cancel_left k he, Nat.sub_add_cancel hk, Nat.sub_add_cancel he]
    rw [mul_comm]; omega
  · rintro ⟨i, j⟩ hp
    rw [mem_window] at hp
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors]
    exact ⟨Nat.lt_succ_of_le hp, Dvd.intro_left _ rfl, by positivity⟩
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨hM, ⟨k, rfl⟩, hM0⟩ := hx
    have he : 0 < e := Nat.pos_of_ne_zero (fun h => hM0 (by simp [h]))
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => hM0 (by simp [h]))
    simp only [Nat.mul_div_cancel_left k he, Nat.sub_add_cancel hk, Nat.sub_add_cancel he]
    rw [mul_comm]
  · rintro ⟨i, j⟩ hp
    simp only [Nat.mul_div_cancel _ (Nat.succ_pos j), Nat.add_sub_cancel]
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨hM, ⟨k, rfl⟩, hM0⟩ := hx
    have he : 0 < e := Nat.pos_of_ne_zero (fun h => hM0 (by simp [h]))
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => hM0 (by simp [h]))
    simp only [Nat.mul_div_cancel_left k he, Nat.sub_add_cancel hk, Nat.sub_add_cancel he]
    rw [mul_comm]

def E₁ (p : ℕ × ℕ) : ℕ := ((p.1 + 1) * N + b) * (p.2 + 1)
def E₂ (p : ℕ × ℕ) : ℕ := ((p.1 + 1) * N - b) * (p.2 + 1)
def E₃ (p : ℕ × ℕ) : ℕ := (p.1 + 1) * N * (p.2 + 1)

def S₁ : Finset (ℕ × ℕ) := (window n).filter fun p => E₁ N b p = n
def S₂ : Finset (ℕ × ℕ) := (window n).filter fun p => E₂ N b p = n
def S₃ : Finset (ℕ × ℕ) := (window n).filter fun p => E₃ N p = n

variable {N b n}

theorem one_le_N [NeZero N] : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

theorem E₁_eq (p : ℕ × ℕ) : E₁ N b p = N * ((p.1 + 1) * (p.2 + 1)) + b * (p.2 + 1) := by
  unfold E₁; ring

theorem E₃_eq (p : ℕ × ℕ) : E₃ N p = N * ((p.1 + 1) * (p.2 + 1)) := by
  unfold E₃; ring

theorem E₂_add (hb : b < N) (p : ℕ × ℕ) : E₂ N b p + b * (p.2 + 1) = N * ((p.1 + 1) * (p.2 + 1)) := by
  unfold E₂
  have hle : b ≤ (p.1 + 1) * N := le_trans hb.le (Nat.le_mul_of_pos_left N (Nat.succ_pos _))
  rw [← Nat.add_mul, Nat.sub_add_cancel hle]; ring

variable [NeZero N]

theorem le_E₁ (p : ℕ × ℕ) : (p.1 + 1) * (p.2 + 1) ≤ E₁ N b p := by
  rw [E₁_eq]
  have h1 := one_le_N (N := N)
  calc (p.1 + 1) * (p.2 + 1) = 1 * ((p.1 + 1) * (p.2 + 1)) := (one_mul _).symm
    _ ≤ N * ((p.1 + 1) * (p.2 + 1)) := Nat.mul_le_mul_right _ h1
    _ ≤ N * ((p.1 + 1) * (p.2 + 1)) + b * (p.2 + 1) := Nat.le_add_right _ _

theorem le_E₃ (p : ℕ × ℕ) : (p.1 + 1) * (p.2 + 1) ≤ E₃ N p := by
  rw [E₃_eq]
  have h1 := one_le_N (N := N)
  calc (p.1 + 1) * (p.2 + 1) = 1 * ((p.1 + 1) * (p.2 + 1)) := (one_mul _).symm
    _ ≤ N * ((p.1 + 1) * (p.2 + 1)) := Nat.mul_le_mul_right _ h1

theorem le_E₂ (hb : b < N) (p : ℕ × ℕ) : (p.1 + 1) * (p.2 + 1) ≤ E₂ N b p := by
  unfold E₂
  apply Nat.mul_le_mul_right

  have : (p.1 + 1) * N = p.1 * N + N := by ring
  rw [this]
  have h1 := one_le_N (N := N)
  have : p.1 ≤ p.1 * N := Nat.le_mul_of_pos_right _ h1
  omega

theorem window_le (p : ℕ × ℕ) : p.1 + p.2 + 1 ≤ (p.1 + 1) * (p.2 + 1) := by nlinarith

theorem mem_S₁ (p : ℕ × ℕ) : p ∈ S₁ N b n ↔ E₁ N b p = n := by
  simp only [S₁, Finset.mem_filter, mem_window, and_iff_right_iff_imp]
  intro h; rw [← h]; exact le_E₁ p

theorem mem_S₂ (hb : b < N) (p : ℕ × ℕ) : p ∈ S₂ N b n ↔ E₂ N b p = n := by
  simp only [S₂, Finset.mem_filter, mem_window, and_iff_right_iff_imp]
  intro h; rw [← h]; exact le_E₂ hb p

theorem mem_S₃ (p : ℕ × ℕ) : p ∈ S₃ N n ↔ E₃ N p = n := by
  simp only [S₃, Finset.mem_filter, mem_window, and_iff_right_iff_imp]
  intro h; rw [← h]; exact le_E₃ p

theorem sum_T₁ (y : ℂ) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (e : ℂ) * (if n = N * M + b * e then y ^ e else 0) =
      ∑ p ∈ S₁ N b n, ((p.2 + 1 : ℕ) : ℂ) * y ^ (p.2 + 1) := by
  rw [sum_divisors_eq_sum_window n (fun M e => (e : ℂ) * (if n = N * M + b * e then y ^ e else 0)),
    S₁, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [E₁_eq]
  by_cases h : n = N * ((p.1 + 1) * (p.2 + 1)) + b * (p.2 + 1)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem sum_T₂ (hb : b < N) (y : ℂ) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (e : ℂ) * (if n + b * e = N * M then y ^ e else 0) =
      ∑ p ∈ S₂ N b n, ((p.2 + 1 : ℕ) : ℂ) * y ^ (p.2 + 1) := by
  rw [sum_divisors_eq_sum_window n (fun M e => (e : ℂ) * (if n + b * e = N * M then y ^ e else 0)),
    S₂, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have key : (n + b * (p.2 + 1) = N * ((p.1 + 1) * (p.2 + 1))) ↔ E₂ N b p = n := by
    rw [← E₂_add hb p]; omega
  by_cases h : n + b * (p.2 + 1) = N * ((p.1 + 1) * (p.2 + 1))
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mpr h')), mul_zero]

theorem sum_T₃ :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (e : ℂ) * (if n = N * M then (2 : ℂ) else 0) =
      2 * ∑ p ∈ S₃ N n, ((p.2 + 1 : ℕ) : ℂ) := by
  rw [sum_divisors_eq_sum_window n (fun M e => (e : ℂ) * (if n = N * M then (2 : ℂ) else 0)),
    S₃, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [E₃_eq]
  by_cases h : n = N * ((p.1 + 1) * (p.2 + 1))
  · rw [if_pos h, if_pos h.symm, mul_comm]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero, mul_zero]

def S₀ (b n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter fun m => b * m = n

theorem mem_S₀ (hb : 0 < b) (m : ℕ) : m ∈ S₀ b n ↔ b * m = n := by
  simp only [S₀, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h; rw [← h]; nlinarith

theorem sum_S₀ (hb : 0 < b) (y : ℂ) :
    ∑ m ∈ S₀ b n, (m : ℂ) * y ^ m = if b ∣ n then ((n / b : ℕ) : ℂ) * y ^ (n / b) else 0 := by
  by_cases hbn : b ∣ n
  · rw [if_pos hbn]
    have : S₀ b n = {n / b} := by
      ext m
      rw [mem_S₀ hb, Finset.mem_singleton]
      constructor
      · rintro rfl; rw [Nat.mul_div_cancel_left _ hb]
      · rintro rfl; exact Nat.mul_div_cancel' hbn
    rw [this, Finset.sum_singleton]
  · rw [if_neg hbn]
    have : S₀ b n = ∅ := by
      ext m
      rw [mem_S₀ hb]
      simp only [Finset.notMem_empty, iff_false]
      rintro rfl; exact hbn (Dvd.intro _ rfl)
    rw [this, Finset.sum_empty]

end Fibres

section Main

open ModularCurve

def shiftEquiv : ℕ × ℕ ≃ ℕ+ × ℕ+ := Equiv.prodCongr Equiv.pnatEquivNat.symm Equiv.pnatEquivNat.symm

@[scoped simp] theorem shiftEquiv_fst (p : ℕ × ℕ) : (((shiftEquiv p).1 : ℕ+) : ℕ) = p.1 + 1 := rfl
@[scoped simp] theorem shiftEquiv_snd (p : ℕ × ℕ) : (((shiftEquiv p).2 : ℕ+) : ℕ) = p.2 + 1 := rfl

theorem norm_eq_one_of_pow_eq_one {x : ℂ} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).mp h

theorem main (N : ℕ) [NeZero N] (c : ℂˣ) (hc : c ^ N = 1) (b : ℕ) (hb0 : 0 < b) (hbN : b < N) :
    ∃ F : ModularForm Γᴸ(N) 2,
      ∀ n : ℕ, (qExpansion 1 F).coeff n =
        (if n = 0 then (1 / 12 : ℂ) else 0) + PowerSeries.coeff n (slotSubst ℂ N c b tateUnivX) := by
  have hN : N ≠ 0 := NeZero.ne N

  set ζ : ℂ := cexp (2 * π * I / N) with hζ_def
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hcN : (c : ℂ) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  obtain ⟨a, ha, hax⟩ := hζ.eq_pow_of_pow_eq_one hcN
  set x : ℂ := (c : ℂ) with hx_def
  have hx1 : ‖x‖ = 1 := norm_eq_one_of_pow_eq_one hN hcN
  have hxinv1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv, hx1, inv_one]
  have hcinv : ((c⁻¹ : ℂˣ) : ℂ) = x⁻¹ := Units.val_inv_eq_inv_val c
  obtain ⟨F, hF⟩ := exists_modularForm_pointwise N a b ha hb0 hbN
  refine ⟨F, ?_⟩

  set D : ℕ → ℂ := fun n =>
    (if n = 0 then (1 / 12 : ℂ) else 0) + PowerSeries.coeff n (slotSubst ℂ N c b tateUnivX) with hD
  have hper : (1 : ℝ) ∈ (Γᴸ(N)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_levelGroup N)]
    exact AddSubgroup.mem_zmultiples 1
  suffices hHas : ∀ τ : ℍ, HasSum (fun m => D m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ) by
    intro n
    exact (ModularFormClass.qExpansion_coeff_unique one_pos hper hHas n).symm
  intro τ
  set q : ℂ := cexp (2 * π * I * (τ : ℂ)) with hq_def
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hqP : Function.Periodic.qParam 1 (τ : ℂ) = q := by
    simp [Function.Periodic.qParam, hq_def]
  simp_rw [hqP, smul_eq_mul]

  set g₁ : ℕ × ℕ → ℂ := fun p => ((p.2 + 1 : ℕ) : ℂ) * x ^ (p.2 + 1) * q ^ E₁ N b p with hg₁
  set g₂ : ℕ × ℕ → ℂ := fun p => ((p.2 + 1 : ℕ) : ℂ) * x⁻¹ ^ (p.2 + 1) * q ^ E₂ N b p with hg₂
  have hs₁ : Summable g₁ := summable_double x q hx1.le hq1 (E₁ N b)
    (fun p => le_trans (window_le p) (le_E₁ p))
  have hs₂ : Summable g₂ := summable_double x⁻¹ q hxinv1 hq1 (E₂ N b)
    (fun p => le_trans (window_le p) (le_E₂ hbN p))
  have hs₃' : Summable fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℂ) * q ^ E₃ N p :=
    (summable_double 1 q (by simp) hq1 (E₃ N) (fun p => le_trans (window_le p) (le_E₃ p))).congr
      (fun p => by rw [one_pow, mul_one])

  have hr₁ : HasSum (fun n => (∑ p ∈ S₁ N b n, ((p.2 + 1 : ℕ) : ℂ) * x ^ (p.2 + 1)) * q ^ n)
      (∑' p, g₁ p) :=
    hasSum_regroup (fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℂ) * x ^ (p.2 + 1)) (E₁ N b) q (S₁ N b)
      (fun n p => mem_S₁ p) hs₁
  have hr₂ : HasSum (fun n => (∑ p ∈ S₂ N b n, ((p.2 + 1 : ℕ) : ℂ) * x⁻¹ ^ (p.2 + 1)) * q ^ n)
      (∑' p, g₂ p) :=
    hasSum_regroup (fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℂ) * x⁻¹ ^ (p.2 + 1)) (E₂ N b) q (S₂ N b)
      (fun n p => mem_S₂ hbN p) hs₂
  have hr₃ : HasSum (fun n => (∑ p ∈ S₃ N n, ((p.2 + 1 : ℕ) : ℂ)) * q ^ n)
      (∑' p : ℕ × ℕ, ((p.2 + 1 : ℕ) : ℂ) * q ^ E₃ N p) :=
    hasSum_regroup (fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℂ)) (E₃ N) q (S₃ N)
      (fun n p => mem_S₃ p) hs₃'

  set u : ℂ := x * q ^ b with hu
  have hu1 : ‖u‖ < 1 := by
    rw [hu, norm_mul, hx1, one_mul, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 hb0.ne'
  have hgeom : HasSum (fun m : ℕ => (m : ℂ) * u ^ m) (u / (1 - u) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hu1
  have hgeom' : HasSum (fun m : ℕ => ((m : ℂ) * x ^ m) * q ^ (b * m)) (u / (1 - u) ^ 2) := by
    convert hgeom using 1; funext m; rw [hu, mul_pow, ← pow_mul, mul_assoc]
  have hr₀ : HasSum (fun n => (∑ m ∈ S₀ b n, (m : ℂ) * x ^ m) * q ^ n) (u / (1 - u) ^ 2) := by
    have h := hasSum_regroup (fun m : ℕ => (m : ℂ) * x ^ m) (fun m => b * m) q (S₀ b)
      (fun n m => mem_S₀ hb0 m) hgeom'.summable
    rwa [hgeom'.tsum_eq] at h

  have hcst : HasSum (fun n : ℕ => (if n = 0 then (1 / 12 : ℂ) else 0) * q ^ n) (1 / 12) := by
    have h := hasSum_single (f := fun n : ℕ => (if n = 0 then (1 / 12 : ℂ) else 0) * q ^ n) 0
      (fun n hn => by simp [hn])
    simpa using h

  have hval : F τ = u / (1 - u) ^ 2 + 1 / 12 +
      ((∑' p, g₁ p) + (∑' p, g₂ p) - 2 * ∑' p : ℕ × ℕ, ((p.2 + 1 : ℕ) : ℂ) * q ^ E₃ N p) := by
    rw [hF τ]
    simp only [← hq_def, ← hζ_def]
    have hxa : ζ ^ a = x := hax
    have hz1 : ∀ m : ℕ, ζ ^ (a * m) = x ^ m := fun m => by rw [pow_mul, hxa]
    have hz2 : ∀ m : ℕ, ζ⁻¹ ^ (a * m) = x⁻¹ ^ m := fun m => by rw [inv_pow, pow_mul, hxa, inv_pow]
    congr 1
    · rw [hu, ← hxa]
    ·
      have hsum3 : HasSum (fun p : ℕ × ℕ => g₁ p + g₂ p - 2 * (((p.2 + 1 : ℕ) : ℂ) * q ^ E₃ N p))
          ((∑' p, g₁ p) + (∑' p, g₂ p) - 2 * ∑' p : ℕ × ℕ, ((p.2 + 1 : ℕ) : ℂ) * q ^ E₃ N p) :=
        (hs₁.hasSum.add hs₂.hasSum).sub (hs₃'.hasSum.mul_left 2)
      rw [← hsum3.tsum_eq, ← Equiv.tsum_eq shiftEquiv]
      refine tsum_congr fun p => ?_
      simp only [shiftEquiv_fst, shiftEquiv_snd, hg₁, hg₂, E₁, E₂, E₃, hz1, hz2]
      ring
  rw [hval]
  have htot := ((hr₀.add hcst).add ((hr₁.add hr₂).sub (hr₃.mul_left 2)))
  convert htot using 1
  funext n

  rw [hD]
  simp only
  rw [ModularCurve.coeff_slotSubst_tateUnivX N c b hb0 hbN n, hcinv]
  have hsplit : ∀ M ∈ Finset.range (n + 1),
      ∑ e ∈ M.divisors, (e : ℂ) *
        ((if n = N * M + b * e then x ^ e else 0) +
          (if n + b * e = N * M then x⁻¹ ^ e else 0) - (if n = N * M then 2 else 0)) =
      ∑ e ∈ M.divisors, (e : ℂ) * (if n = N * M + b * e then x ^ e else 0) +
        ∑ e ∈ M.divisors, (e : ℂ) * (if n + b * e = N * M then x⁻¹ ^ e else 0) -
        ∑ e ∈ M.divisors, (e : ℂ) * (if n = N * M then (2 : ℂ) else 0) := by
    intro M _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_T₁, sum_T₂ hbN, sum_T₃, sum_S₀ hb0]
  ring

end Main

end NonToricDivision
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX.NonToricDivision"

open scoped MatrixGroups in
theorem solution
    (N : ℕ) [NeZero N] (c : ℂˣ) (hc : c ^ N = 1) (b : ℕ) (hb0 : 0 < b) (hbN : b < N) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N ^ 2) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff n =
        (if n = 0 then (1 / 12 : ℂ) else 0) +
          PowerSeries.coeff n (ModularCurve.slotSubst ℂ N c b ModularCurve.tateUnivX) :=
  NonToricDivision.main N c hc b hb0 hbN

end
end S_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX (solution)
