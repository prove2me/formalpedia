-- Prove2me | solution 1 for ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7052ad18-ca24-5945-bdd1-bfff20153cb6

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand
import Theorems.Thm_EisensteinSeries_qExpansion_coeff_of_apply_eq_tsum_eisSummand
import Theorems.Thm_EisensteinSeries_qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand
import Theorems.Thm_Complex_tsum_one_div_add_int_pow_three
import Theorems.Thm_ModularCurve_ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "UpperHalfPlane~I"
open Complex ModularForm CongruenceSubgroup Matrix ConjAct
open scoped MatrixGroups ModularForm Real Topology Pointwise

namespace ToricDivision2

abbrev levelGroup (N n : ℕ) : Subgroup SL(2, ℤ) := Gamma1 n ⊓ Gamma0 (N * n)

scoped instance (N n : ℕ) [NeZero N] [NeZero n] : (levelGroup N n).FiniteIndex := by
  haveI : NeZero (N * n) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne n)⟩
  unfold levelGroup; infer_instance

theorem T_mem_levelGroup (N n : ℕ) : ModularGroup.T ∈ levelGroup N n := by
  refine ⟨?_, ?_⟩
  · simp [Gamma1_mem, ModularGroup.T]
  · simp [Gamma0_mem, ModularGroup.T]

def diagInt (N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1]

theorem diagInt_map_eq {N : ℕ} (hN : N ≠ 0) :
    (diagInt N).map (algebraMap ℤ ℝ) =
      ((heckeDiagMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hN]; unfold diagInt
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_cocycle {N n : ℕ} [NeZero N] [NeZero n] {γ : SL(2, ℤ)} (hγ : γ ∈ levelGroup N n) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 n ∧
      diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagInt N := by
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  obtain ⟨ha, hd, -⟩ := h1
  have hc : ((N * n : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
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
  have hdet' : Matrix.det !![a, (N : ℤ) * b; (n : ℤ) * c₀, d] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + b * hc₀
  refine ⟨⟨_, hdet'⟩, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((a : ℤ) : ZMod n) = 1; exact ha
    · show ((d : ℤ) : ZMod n) = 1; exact hd
    · show (((n : ℤ) * c₀ : ℤ) : ZMod n) = 0; push_cast; rw [ZMod.natCast_self, zero_mul]
  · show diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, (N : ℤ) * b; (n : ℤ) * c₀, d] * diagInt N
    rw [hγmat]; unfold diagInt
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show ((N : ℤ) * a + 0 * c : ℤ) = a * (N : ℤ) + (N : ℤ) * b * 0; ring
    · show ((N : ℤ) * b + 0 * d : ℤ) = a * 0 + (N : ℤ) * b * 1; ring
    · show (0 * a + 1 * c : ℤ) = (n : ℤ) * c₀ * (N : ℤ) + d * 0; linear_combination hc₀
    · show (0 * b + 1 * d : ℤ) = (n : ℤ) * c₀ * 0 + d * 1; ring

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

theorem levelGroup_le_conj₁ (N n : ℕ) [NeZero N] [NeZero n] :
    ((levelGroup N n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (heckeDiagMatrix N)⁻¹ • ((Gamma1 n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
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

def S₀ (N n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter fun m => N * m = n

theorem mem_S₀ {N n : ℕ} (hN : 0 < N) (m : ℕ) : m ∈ S₀ N n ↔ N * m = n := by
  simp only [S₀, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h; rw [← h]; nlinarith

theorem sum_S₀ {N n : ℕ} (hN : 0 < N) (w : ℕ → ℂ) :
    ∑ m ∈ S₀ N n, w m = if N ∣ n then w (n / N) else 0 := by
  by_cases hbn : N ∣ n
  · rw [if_pos hbn]
    have : S₀ N n = {n / N} := by
      ext m
      rw [mem_S₀ hN, Finset.mem_singleton]
      constructor
      · rintro rfl; rw [Nat.mul_div_cancel_left _ hN]
      · rintro rfl; exact Nat.mul_div_cancel' hbn
    rw [this, Finset.sum_singleton]
  · rw [if_neg hbn]
    have : S₀ N n = ∅ := by
      ext m
      rw [mem_S₀ hN]
      simp only [Finset.notMem_empty, iff_false]
      rintro rfl; exact hbn (Dvd.intro _ rfl)
    rw [this, Finset.sum_empty]

theorem sum_divisors_filter_dvd {N m : ℕ} (hN : 0 < N) (g : ℕ → ℂ) :
    ∑ d ∈ (N * m).divisors, (if N ∣ d then g (N * m / d) else 0) =
      ∑ d ∈ m.divisors, g (m / d) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun d => d / N) (fun d => N * d) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, hn0⟩, ⟨k, rfl⟩⟩ := hd
    rw [Nat.mem_divisors, Nat.mul_div_cancel_left k hN]
    refine ⟨?_, fun hm => hn0 (by rw [hm, mul_zero])⟩
    exact Nat.dvd_of_mul_dvd_mul_left hN hdn
  · intro d hd
    rw [Nat.mem_divisors] at hd
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left N hd.1, Nat.mul_ne_zero hN.ne' hd.2⟩, Dvd.intro _ rfl⟩
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨-, ⟨k, rfl⟩⟩ := hd
    rw [Nat.mul_div_cancel_left k hN]
  · intro d _
    exact Nat.mul_div_cancel_left d hN
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨-, ⟨k, rfl⟩⟩ := hd
    simp only [Nat.mul_div_cancel_left k hN, Nat.mul_div_mul_left m k hN]

theorem sum_divisors_toric {N : ℕ} (hN : 0 < N) (y : ℂ) (m : ℕ) :
    ∑ d ∈ (N * m).divisors,
        (if N ∣ d then ((N * m / d : ℕ) : ℂ) * (y ^ (N * m / d) + y⁻¹ ^ (N * m / d)) else 0) =
      ∑ e ∈ m.divisors, (e : ℂ) * (y ^ e + y⁻¹ ^ e) := by
  have h := sum_divisors_filter_dvd (m := m) hN (fun e => (e : ℂ) * (y ^ e + y⁻¹ ^ e))
  rw [h, Nat.sum_div_divisors m (fun e => (e : ℂ) * (y ^ e + y⁻¹ ^ e))]

def liftForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic] {k : ℤ} (F : ModularForm Γ k)
    (hinv : ∀ γ ∈ Γ', (⇑F : ℍ → ℂ) ∣[k] γ = ⇑F) : ModularForm Γ' k where
  toFun := F
  slash_action_eq' := fun γ hγ => hinv γ hγ
  holo' := F.holo'
  bdd_at_cusps' := fun hc => F.bdd_at_cusps'
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mpr ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ').mp hc))

@[scoped simp] theorem coe_liftForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic] {k : ℤ} (F : ModularForm Γ k)
    (hinv : ∀ γ ∈ Γ', (⇑F : ℍ → ℂ) ∣[k] γ = ⇑F) : (⇑(liftForm F hinv) : ℍ → ℂ) = ⇑F := rfl

local notation "Γᴸ(" N "," n ")" => ((levelGroup N n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₁ᴳ(" n ")" => ((Gamma1 n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γᴺ(" n ")" => ((CongruenceSubgroup.Gamma n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Eis

variable (N n : ℕ) [NeZero N] [NeZero n]

def G : (Fin 2 → ZMod n) → ModularForm Γᴺ(n) 3 :=
  Classical.choose (EisensteinSeries.exists_modularForm_gamma_apply_eq_tsum_eisSummand n 3 le_rfl)

theorem G_spec : (∀ (v : Fin 2 → ZMod n) (τ : ℍ),
      G n v τ = ∑' x : {x : Fin 2 → ℤ // ((↑) : ℤ → ZMod n) ∘ x = v}, EisensteinSeries.eisSummand 3 x.1 τ) ∧
    (∀ (v : Fin 2 → ZMod n) (γ : SL(2, ℤ)),
      ((⇑(G n v) : ℍ → ℂ) ∣[(3 : ℤ)] (γ : GL (Fin 2) ℝ)) =
        ⇑(G n (Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod n))))) :=
  Classical.choose_spec (EisensteinSeries.exists_modularForm_gamma_apply_eq_tsum_eisSummand n 3 le_rfl)

def vt (t : ZMod n) : Fin 2 → ZMod n := ![0, t]

theorem vecMul_vt (t : ZMod n) (γ : SL(2, ℤ)) (h10 : ((γ 1 0 : ℤ) : ZMod n) = 0) :
    Matrix.vecMul (vt n t) ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod n)) =
      vt n (t * ((γ 1 1 : ℤ) : ZMod n)) := by
  funext j
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  fin_cases j
  · simp [vt, Matrix.map_apply, h10]
  · simp [vt, Matrix.map_apply]

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 n := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods₁ : (1 : ℝ) ∈ (Γ₁ᴳ(n)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 n)]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_L : (1 : ℝ) ∈ (Γᴸ(N, n)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_levelGroup N n)]
  exact AddSubgroup.mem_zmultiples 1

def G₁ (t : ZMod n) : ModularForm Γ₁ᴳ(n) 3 :=
  liftForm (G n (vt n t)) (by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hA
    rw [Gamma1_mem] at hγ
    obtain ⟨-, h11, h10⟩ := hγ
    rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) from rfl,
      (G_spec n).2, vecMul_vt n t γ h10, h11, mul_one])

theorem coe_G₁ (t : ZMod n) : (⇑(G₁ n t) : ℍ → ℂ) = ⇑(G n (vt n t)) := rfl

def F (t : ZMod n) : ModularForm Γᴸ(N, n) 3 :=
  ModularCurve.restrictForm (levelGroup_le_conj₁ N n) (ModularForm.translate (G₁ n t) (heckeDiagMatrix N))

theorem coe_F (t : ZMod n) : (⇑(F N n t) : ℍ → ℂ) = (⇑(G n (vt n t)) : ℍ → ℂ) ∣[(3 : ℤ)] heckeDiagMatrix N := rfl

def ζn : ℂ := cexp (2 * π * I / n)

theorem ζn_prim : IsPrimitiveRoot (ζn n) n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)

def sOf (c : ℂˣ) : ℕ :=
  if h : (c : ℂ) ^ n = 1 then Classical.choose ((ζn_prim n).eq_pow_of_pow_eq_one h) else 0

theorem sOf_spec (c : ℂˣ) (h : (c : ℂ) ^ n = 1) : sOf n c < n ∧ ζn n ^ sOf n c = c := by
  unfold sOf; rw [dif_pos h]; exact Classical.choose_spec ((ζn_prim n).eq_pow_of_pow_eq_one h)

def tOf (c : ℂˣ) : ZMod n := ((sOf n c : ℕ) : ZMod n)

theorem coe_pow_n {c : ℂˣ} (h : c ^ n = 1) : (c : ℂ) ^ n = 1 := by
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem tOf_zpow (c : ℂˣ) (h : c ^ n = 1) (d : ℤ) :
    tOf n (c ^ d) = tOf n c * ((d : ℤ) : ZMod n) := by
  have hc : (c : ℂ) ^ n = 1 := coe_pow_n n h
  have hcd : (((c ^ d : ℂˣ)) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h, _root_.one_zpow, Units.val_one]
  obtain ⟨-, hs⟩ := sOf_spec n c hc
  obtain ⟨-, hs'⟩ := sOf_spec n (c ^ d) hcd

  have h1 : (ζn n) ^ ((sOf n (c ^ d) : ℤ)) = (ζn n) ^ ((sOf n c : ℤ) * d) := by
    rw [zpow_natCast, hs', _root_.zpow_mul, zpow_natCast, hs, Units.val_zpow_eq_zpow_val]
  have h2 : (ζn n) ^ (((sOf n (c ^ d) : ℤ)) - (sOf n c : ℤ) * d) = 1 := by
    rw [zpow_sub₀ ((ζn_prim n).ne_zero (NeZero.ne n)), h1, div_self]
    exact zpow_ne_zero _ ((ζn_prim n).ne_zero (NeZero.ne n))
  have h3 := ((ζn_prim n).zpow_eq_one_iff_dvd _).mp h2
  unfold tOf
  rw [show ((sOf n c : ℕ) : ZMod n) * ((d : ℤ) : ZMod n) = (((sOf n c : ℤ) * d : ℤ) : ZMod n) by push_cast; ring,
    show ((sOf n (c ^ d) : ℕ) : ZMod n) = (((sOf n (c ^ d) : ℤ)) : ZMod n) by push_cast; rfl,
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  have : ((n : ℤ)) ∣ -(((sOf n (c ^ d) : ℤ)) - (sOf n c : ℤ) * d) := (dvd_neg).mpr h3
  convert this using 1; ring

def κ : ℂ := -2 * (n : ℂ) ^ 3 / ((2 * π * I) ^ 3 * (N : ℂ) ^ 2)

def Y (c : ℂˣ) : ModularForm Γᴸ(N, n) 3 := κ N n • F N n (tOf n c)

theorem coe_Y (c : ℂˣ) : (⇑(Y N n c) : ℍ → ℂ) = κ N n • ((⇑(G n (vt n (tOf n c))) : ℍ → ℂ) ∣[(3 : ℤ)] heckeDiagMatrix N) := by
  rw [Y, ModularForm.IsGLPos.coe_smul, coe_F]

theorem heckeDiag_mul_conjElemN (ρ : SL(2, ℤ)) :
    heckeDiagMatrix N * ModularCurve.FullLevel.conjElemN N ρ = (ρ : GL (Fin 2) ℝ) * heckeDiagMatrix N := by
  have hN : N ≠ 0 := NeZero.ne N
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.FullLevel.conjElemN, mul_comm] <;> field_simp

theorem σ_conjElemN (ρ : SL(2, ℤ)) (z : ℂ) : UpperHalfPlane.σ (ModularCurve.FullLevel.conjElemN N ρ) z = z := by
  have hdet : ((ModularCurve.FullLevel.conjElemN N ρ).det : ℝ) = 1 := by
    have h := congrArg (fun g : GL (Fin 2) ℝ => ((g.det : ℝˣ) : ℝ)) (heckeDiag_mul_conjElemN N ρ)
    simp only [map_mul, Units.val_mul] at h
    have hD : (((heckeDiagMatrix N).det : ℝˣ) : ℝ) = N := det_heckeDiagMatrix (NeZero.ne N)
    have hρ : ((((ρ : SL(2, ℤ)) : GL (Fin 2) ℝ).det : ℝˣ) : ℝ) = 1 := by
      simp [Matrix.GeneralLinearGroup.val_det_apply]
    rw [hD, hρ, one_mul] at h
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    exact mul_left_cancel₀ hNr (by rw [h, mul_one])
  rw [UpperHalfPlane.σ, if_pos (by rw [hdet]; exact one_pos)]
  rfl

theorem slash_law (ρ : SL(2, ℤ)) (hρ : ρ ∈ Gamma0 n) (c : ℂˣ) (hc : c ^ n = 1) :
    ((⇑(Y N n c) : ℍ → ℂ) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(Y N n (c ^ ((ρ 1 1 : ℤ)))) := by
  have h10 : ((ρ 1 0 : ℤ) : ZMod n) = 0 := Gamma0_mem.mp hρ
  rw [coe_Y, coe_Y, ModularForm.smul_slash]
  have hσ : UpperHalfPlane.σ (ModularCurve.FullLevel.conjElemN N ρ) (κ N n) = κ N n := σ_conjElemN N ρ _
  rw [hσ, ← SlashAction.slash_mul, heckeDiag_mul_conjElemN, SlashAction.slash_mul, (G_spec n).2,
    vecMul_vt n _ ρ h10, tOf_zpow n c hc]

end Eis

section QExp

variable (N n : ℕ) [NeZero N] [NeZero n]

theorem two_mul_choose_two_add (e : ℕ) : 2 * ((e.choose 2 : ℕ) : ℂ) + e = (e : ℂ) ^ 2 := by
  have h : 2 * e.choose 2 = e * (e - 1) := by
    rw [Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self e)]
  have h' : (2 * ((e.choose 2 : ℕ) : ℂ)) = ((e * (e - 1) : ℕ) : ℂ) := by exact_mod_cast h
  rw [h']
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · rw [Nat.cast_mul, Nat.cast_sub he]; ring

theorem two_mul_choose_two_succ_sub (e : ℕ) : 2 * (((e + 1).choose 2 : ℕ) : ℂ) - e = (e : ℂ) ^ 2 := by
  have h : 2 * (e + 1).choose 2 = (e + 1) * e := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.two_mul_div_two_of_even]
    simpa [mul_comm] using Nat.even_mul_succ_self e
  have h' : (2 * (((e + 1).choose 2 : ℕ) : ℂ)) = (((e + 1) * e : ℕ) : ℂ) := by exact_mod_cast h
  rw [h']; push_cast; ring

theorem coeff_two_mul_snd_add_fst (c : ℂˣ) (M : ℕ) :
    (2 * (ModularCurve.tateToricPoint ℂ N c).2 + (ModularCurve.tateToricPoint ℂ N c).1).coeff (M : ℤ) =
      if M = 0 then 2 * ((c : ℂ) ^ 2 * Ring.inverse (1 - (c : ℂ)) ^ 3) + (c : ℂ) * Ring.inverse (1 - (c : ℂ)) ^ 2
      else ∑ d ∈ M.divisors, (if N ∣ d then ((M / d : ℕ) : ℂ) ^ 2 * ((c : ℂ) ^ (M / d) - ((c⁻¹ : ℂˣ) : ℂ) ^ (M / d)) else 0) := by
  rw [two_mul, HahnSeries.coeff_add', HahnSeries.coeff_add', Pi.add_apply, Pi.add_apply,
    ModularCurve.tateToricPoint_fst, ModularCurve.tateToricPoint_snd,
    HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hM : M = 0
  · simp only [hM, if_true]; ring
  · simp only [hM, if_false]
    rw [show ∀ (A B S T : ℂ), (A + S) + (A + S) + (B - 2 * T) = (A + A + B) + (S + S - 2 * T) from fun _ _ _ _ => by ring,
      show ∀ (S T : ℂ), S + S - 2 * T = 2 * (S - T) from fun _ _ => by ring]
    have hST : ((if N ∣ M then ∑ e ∈ (M / N).divisors, (e : ℂ) else 0) - (if N ∣ M then ∑ e ∈ (M / N).divisors, (e : ℂ) else 0)) = 0 := sub_self _
    rw [hST, mul_zero, add_zero, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with hNd
    · have h1 := two_mul_choose_two_add (M / d)
      have h2 := two_mul_choose_two_succ_sub (M / d)
      linear_combination ((c : ℂ) ^ (M / d)) * h1 - (((c⁻¹ : ℂˣ) : ℂ) ^ (M / d)) * h2
    · simp

theorem tate_sum_eq (y : ℂ) (j : ℕ) :
    ∑ d ∈ (N * j).divisors, (if N ∣ d then ((N * j / d : ℕ) : ℂ) ^ 2 * (y ^ (N * j / d) - y⁻¹ ^ (N * j / d)) else 0) =
      ∑ e ∈ j.divisors, (e : ℂ) ^ 2 * (y ^ e - y⁻¹ ^ e) := by
  have h := sum_divisors_filter_dvd (m := j) (Nat.pos_of_ne_zero (NeZero.ne N)) (fun e => (e : ℂ) ^ 2 * (y ^ e - y⁻¹ ^ e))
  rw [h, Nat.sum_div_divisors j (fun e => (e : ℂ) ^ 2 * (y ^ e - y⁻¹ ^ e))]

theorem tate_sum_eq_zero (y : ℂ) (M : ℕ) (hM : ¬ N ∣ M) :
    ∑ d ∈ M.divisors, (if N ∣ d then ((M / d : ℕ) : ℂ) ^ 2 * (y ^ (M / d) - y⁻¹ ^ (M / d)) else 0) = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  exact fun hNd => hM (dvd_trans hNd (Nat.dvd_of_mem_divisors hd))

theorem eis_coeff_mul (t : ZMod n) (j : ℕ) (hj : 1 ≤ j) :
    (UpperHalfPlane.qExpansion (n : ℝ) (⇑(G n (vt n t)))).coeff (n * j) =
      ((-2 * π * I) ^ 3 / ((3 - 1).factorial * (n : ℂ) ^ 3)) *
        ∑ e ∈ j.divisors, (e : ℂ) ^ 2 * ((ζn n ^ t.val) ^ e - (ζn n ^ t.val)⁻¹ ^ e) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnj : 1 ≤ n * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne n) (Nat.one_le_iff_ne_zero.mp hj))
  rw [EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_eisSummand n 3 le_rfl (vt n t) (G n (vt n t))
    ((G_spec n).1 (vt n t)) (n * j) hnj]
  congr 1

  have he1 : ∀ d : ℕ, Complex.exp (2 * π * I * ((d * t.val : ℕ) : ℂ) / n) = (ζn n ^ t.val) ^ d := by
    intro d; rw [ζn, ← pow_mul, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have he2 : ∀ d : ℕ, Complex.exp (-(2 * π * I * ((d * t.val : ℕ) : ℂ) / n)) = (ζn n ^ t.val)⁻¹ ^ d := by
    intro d; rw [Complex.exp_neg, he1, inv_pow]
  have hv0 : vt n t 0 = 0 := rfl
  have hv1 : vt n t 1 = t := rfl
  simp only [hv0, hv1, neg_zero, he1, he2]

  rw [Nat.sum_divisorsAntidiagonal (fun (i d : ℕ) => (d : ℂ) ^ (3 - 1) *
      ((if ((i : ℕ) : ZMod n) = 0 then (ζn n ^ t.val) ^ d else 0) + (-1) ^ 3 * (if ((i : ℕ) : ZMod n) = 0 then (ζn n ^ t.val)⁻¹ ^ d else 0)))]
  have hrw : ∀ i ∈ (n * j).divisors,
      ((n * j / i : ℕ) : ℂ) ^ (3 - 1) *
        ((if ((i : ℕ) : ZMod n) = 0 then (ζn n ^ t.val) ^ (n * j / i) else 0) +
          (-1) ^ 3 * (if ((i : ℕ) : ZMod n) = 0 then (ζn n ^ t.val)⁻¹ ^ (n * j / i) else 0)) =
      (if n ∣ i then ((n * j / i : ℕ) : ℂ) ^ 2 * ((ζn n ^ t.val) ^ (n * j / i) - (ζn n ^ t.val)⁻¹ ^ (n * j / i)) else 0) := by
    intro i _
    by_cases hi : n ∣ i
    · have hi' : ((i : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff i n).mpr hi
      rw [if_pos hi, if_pos hi', if_pos hi']; ring
    · have hi' : ¬ ((i : ℕ) : ZMod n) = 0 := fun h => hi ((ZMod.natCast_eq_zero_iff i n).mp h)
      rw [if_neg hi, if_neg hi', if_neg hi']; ring
  rw [Finset.sum_congr rfl hrw, tate_sum_eq n (ζn n ^ t.val) j]

theorem eis_coeff_zero (t : ZMod n) (ht : t ≠ 0) :
    (UpperHalfPlane.qExpansion (n : ℝ) (⇑(G n (vt n t)))).coeff 0 =
      ((n : ℂ) ^ 3)⁻¹ * (-((2 * π * I) ^ 3 / 2) *
        ((ζn n ^ t.val) * (1 + ζn n ^ t.val) / (1 - ζn n ^ t.val) ^ 3)) := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [EisensteinSeries.qExpansion_coeff_zero_of_apply_eq_tsum_eisSummand n 3 le_rfl (vt n t) (G n (vt n t))
    ((G_spec n).1 (vt n t)), if_pos (show vt n t 0 = 0 from rfl)]
  have ht1 : 0 < t.val := by rwa [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
  have ht2 : t.val < n := ZMod.val_lt t
  have hx : ∀ m : ℤ, ((t.val : ℝ) / (n : ℕ) : ℝ) ≠ m := by
    intro m h
    have h0 : (0 : ℝ) < (t.val : ℝ) / (n : ℕ) := by positivity
    have h1 : (t.val : ℝ) / (n : ℕ) < 1 := by
      rw [div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]; exact_mod_cast ht2
    rw [h] at h0 h1
    have : (0 : ℤ) < m := by exact_mod_cast h0
    have : m < 1 := by exact_mod_cast h1
    omega
  have hH := Complex.tsum_one_div_add_int_pow_three ((t.val : ℝ) / (n : ℕ)) hx
  have hsum : (∑' m : ℤ, 1 / ((((vt n t 1).val : ℕ) : ℂ) + ((n : ℕ) : ℂ) * (m : ℂ)) ^ 3) =
      (((n : ℕ) : ℂ) ^ 3)⁻¹ * ∑' m : ℤ, 1 / ((((t.val : ℝ) / (n : ℕ) : ℝ) : ℂ) + m) ^ 3 := by
    rw [← tsum_mul_left]
    congr 1; funext m
    have hnC : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [show vt n t 1 = t from rfl]
    push_cast
    field_simp
  have hexp : Complex.exp (2 * π * I * (((t.val : ℝ) / (n : ℕ) : ℝ) : ℂ)) = ζn n ^ t.val := by
    rw [ζn, ← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [hsum, hH, hexp]

theorem coeff_one_eq_coeff_n (t : ZMod n) (j : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑(G₁ n t))).coeff j =
      (UpperHalfPlane.qExpansion (n : ℝ) (⇑(G n (vt n t)))).coeff (n * j) := by
  have h := ModularCurve.ofPowerSeries_qExpansion_natCast_eq_qExpand_of_one_mem_strictPeriods (G₁ n t)
    (one_mem_strictPeriods₁ n) n
  have h2 := congrArg (fun x : LaurentSeries ℂ => x.coeff ((n * j : ℕ) : ℤ)) h
  simp only [HahnSeries.ofPowerSeries_apply_coeff] at h2
  rw [coe_G₁] at h2
  rw [h2, Nat.cast_mul, ModularCurve.qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff]
  rfl

theorem qexp_eq (c : ℂˣ) (hc : c ^ n = 1) (hc1 : c ≠ 1) :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Y N n c))) =
      2 * (ModularCurve.tateToricPoint ℂ N c).2 + (ModularCurve.tateToricPoint ℂ N c).1 := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hn : n ≠ 0 := NeZero.ne n
  have hcC : (c : ℂ) ^ n = 1 := coe_pow_n n hc
  obtain ⟨hs, hζs⟩ := sOf_spec n c hcC
  set s : ℕ := sOf n c with hs_def
  set t : ZMod n := tOf n c with ht_def
  have htval : t.val = s := by rw [ht_def, tOf]; exact ZMod.val_natCast_of_lt hs
  have hs0 : s ≠ 0 := by
    intro h0; apply hc1; apply Units.ext; rw [Units.val_one, ← hζs, h0, pow_zero]
  have ht0 : t ≠ 0 := by intro h; apply hs0; rw [← htval, h, ZMod.val_zero]
  have hx : ζn n ^ t.val = (c : ℂ) := by rw [htval, hζs]
  have hcinv : ((c⁻¹ : ℂˣ) : ℂ) = (c : ℂ)⁻¹ := Units.val_inv_eq_inv_val c
  have hc1' : (1 - (c : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hc1 (Units.val_eq_one.mp h.symm)

  set a : ℕ → ℂ := fun j => (UpperHalfPlane.qExpansion 1 (⇑(G₁ n t))).coeff j with ha
  set D : ℕ → ℂ := fun M => κ N n * (N : ℂ) ^ 2 * ∑ j ∈ S₀ N M, a j with hD

  have hA : ∀ M : ℕ, (UpperHalfPlane.qExpansion 1 (⇑(Y N n c))).coeff M = D M := by
    have hYval : ∀ τ : ℍ, (Y N n c) τ = κ N n * (N : ℂ) ^ 2 * (G₁ n t) (heckeDiagMatrix N • τ) := by
      intro τ
      rw [show (Y N n c) τ = (⇑(Y N n c) : ℍ → ℂ) τ from rfl, coe_Y, Pi.smul_apply, smul_eq_mul,
        slash_heckeDiagMatrix_apply _ hN, ← coe_G₁]
      have : ((N : ℂ) ^ ((3 : ℤ) - 1)) = (N : ℂ) ^ 2 := by
        rw [show ((3 : ℤ) - 1) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
      rw [this, ht_def]; ring
    suffices hHas : ∀ τ : ℍ, HasSum (fun M => D M • Function.Periodic.qParam 1 (τ : ℂ) ^ M) ((Y N n c) τ) by
      intro M
      exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_L N n) hHas M).symm
    intro τ
    set q : ℂ := cexp (2 * π * I * (τ : ℂ)) with hq_def
    have hqP : Function.Periodic.qParam 1 (τ : ℂ) = q := by
      simp [Function.Periodic.qParam, hq_def]
    simp_rw [hqP, smul_eq_mul]
    rw [hYval τ]
    have hFact : Fact (IsCusp OnePoint.infty Γ₁ᴳ(n)) :=
      ⟨(Γ₁ᴳ(n)).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods₁ n)⟩
    have hWsum := UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex (G₁ n t) (one_mem_strictPeriods₁ n))
      (ModularFormClass.holo (G₁ n t)) (ModularFormClass.bdd_at_infty (G₁ n t)) (heckeDiagMatrix N • τ)
    have hqN : Function.Periodic.qParam 1 (((heckeDiagMatrix N • τ : ℍ) : ℂ)) = q ^ N := by
      rw [coe_heckeDiagMatrix_smul hN]
      simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
      rw [hq_def, ← Complex.exp_nat_mul]; ring_nf
    simp_rw [hqN, smul_eq_mul, ← pow_mul] at hWsum
    have hr : HasSum (fun M => (∑ j ∈ S₀ N M, a j) * q ^ M) ((G₁ n t) (heckeDiagMatrix N • τ)) := by
      have h := hasSum_regroup (fun j => a j) (fun j => N * j) q (S₀ N) (fun M j => mem_S₀ hN0 j) hWsum.summable
      rwa [hWsum.tsum_eq] at h
    have htot := hr.mul_left (κ N n * (N : ℂ) ^ 2)
    convert htot using 1 <;> try rfl
    funext M
    rw [hD]; ring

  have hB : ∀ M : ℕ, D M = (2 * (ModularCurve.tateToricPoint ℂ N c).2 + (ModularCurve.tateToricPoint ℂ N c).1).coeff (M : ℤ) := by
    intro M
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    show κ N n * (N : ℂ) ^ 2 * ∑ j ∈ S₀ N M, a j = _
    rw [coeff_two_mul_snd_add_fst N c M, sum_S₀ hN0]
    by_cases hNM : N ∣ M
    · obtain ⟨j, rfl⟩ := hNM
      rw [if_pos (dvd_mul_right N j), Nat.mul_div_cancel_left j hN0]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      ·
        rw [mul_zero, if_pos rfl, ha]
        dsimp only
        rw [coeff_one_eq_coeff_n, mul_zero, eis_coeff_zero n t ht0, hx, Ring.inverse_eq_inv', κ]
        field_simp
        ring
      · have hNj : N * j ≠ 0 := Nat.mul_ne_zero hN hj.ne'
        rw [if_neg hNj, ha]
        dsimp only
        rw [hcinv, coeff_one_eq_coeff_n, eis_coeff_mul n t j hj, hx, tate_sum_eq N (c : ℂ) j, κ, ← mul_assoc]
        conv_rhs => rw [← one_mul (∑ e ∈ j.divisors, (e : ℂ) ^ 2 * ((c : ℂ) ^ e - (c : ℂ)⁻¹ ^ e))]
        congr 1
        rw [show ((3 : ℕ) - 1).factorial = 2 by norm_num [Nat.factorial]]
        push_cast
        field_simp
    · rw [if_neg hNM, mul_zero]
      have hM0 : M ≠ 0 := fun h => hNM (h ▸ dvd_zero N)
      rw [if_neg hM0, hcinv, tate_sum_eq_zero N _ M hNM]

  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    · rw [ModularCurve.tateToricPoint_fst, ModularCurve.tateToricPoint_snd,
        show (2 : LaurentSeries ℂ) = HahnSeries.ofPowerSeries ℤ ℂ 2 from (map_ofNat _ 2).symm, ← map_mul, ← map_add,
        HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
      intro hmem; obtain ⟨j, hj⟩ := hmem
      change (j : ℤ) = _ at hj
      omega
    · intro hmem; obtain ⟨j, hj⟩ := hmem
      change (j : ℤ) = _ at hj
      omega
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, hA, hB]

end QExp

end ToricDivision2
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq.ToricDivision2"

open scoped MatrixGroups in

theorem solution (N n : ℕ) [NeZero N] [NeZero n] :
    ∃ Y : ℂˣ → ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 3,
      (∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Y c))) =
          2 * (ModularCurve.tateToricPoint ℂ N c).2 + (ModularCurve.tateToricPoint ℂ N c).1) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 n → ∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        (⇑(Y c) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(Y (c ^ ((ρ 1 1 : ℤ))))) :=
  ⟨ToricDivision2.Y N n, fun c hc hc1 => ToricDivision2.qexp_eq N n c hc hc1,
    fun ρ hρ c hc _ => ToricDivision2.slash_law N n ρ hρ c hc⟩

end
end S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_weight_three_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq (solution)
