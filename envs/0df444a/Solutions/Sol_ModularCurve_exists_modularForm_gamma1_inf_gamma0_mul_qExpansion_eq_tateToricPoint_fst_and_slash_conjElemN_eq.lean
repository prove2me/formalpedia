-- Prove2me | solution 1 for ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/07b1e9b6-49c7-5cde-a11b-4c41d2ca152b

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "UpperHalfPlane~I"
open Complex ModularForm CongruenceSubgroup Matrix ConjAct
open scoped MatrixGroups ModularForm Real Topology Pointwise

namespace ToricDivision2

abbrev levelGroup (N M : ℕ) : Subgroup SL(2, ℤ) := Gamma1 M ⊓ Gamma0 (N * M)

theorem T_mem_levelGroup (N M : ℕ) : ModularGroup.T ∈ levelGroup N M := by
  refine ⟨?_, ?_⟩
  · simp [Gamma1_mem, ModularGroup.T]
  · simp [Gamma0_mem, ModularGroup.T]

def diagInt (N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1]

theorem diagInt_map_eq {N : ℕ} (hN : N ≠ 0) :
    (diagInt N).map (algebraMap ℤ ℝ) =
      ((heckeDiagMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hN]; unfold diagInt
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_cocycle {N M : ℕ} [NeZero N] {γ : SL(2, ℤ)} (hγ : γ ∈ levelGroup N M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 M ∧
      diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagInt N := by
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  obtain ⟨ha, hd, -⟩ := h1
  have hc : ((N * M : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
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
  have hdet' : Matrix.det !![a, (N : ℤ) * b; (M : ℤ) * c₀, d] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + b * hc₀
  refine ⟨⟨_, hdet'⟩, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((a : ℤ) : ZMod M) = 1; exact ha
    · show ((d : ℤ) : ZMod M) = 1; exact hd
    · show (((M : ℤ) * c₀ : ℤ) : ZMod M) = 0; push_cast; rw [ZMod.natCast_self, zero_mul]
  · show diagInt N * (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, (N : ℤ) * b; (M : ℤ) * c₀, d] * diagInt N
    rw [hγmat]; unfold diagInt
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show ((N : ℤ) * a + 0 * c : ℤ) = a * (N : ℤ) + (N : ℤ) * b * 0; ring
    · show ((N : ℤ) * b + 0 * d : ℤ) = a * 0 + (N : ℤ) * b * 1; ring
    · show (0 * a + 1 * c : ℤ) = (M : ℤ) * c₀ * (N : ℤ) + d * 0; linear_combination hc₀
    · show (0 * b + 1 * d : ℤ) = (M : ℤ) * c₀ * 0 + d * 1; ring

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

theorem levelGroup_le_conj₁ (N M : ℕ) [NeZero N] :
    ((levelGroup N M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (heckeDiagMatrix N)⁻¹ • ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
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

theorem heckeDiagMatrix_mul_conjElemN (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    heckeDiagMatrix N * ModularCurve.FullLevel.conjElemN N γ = (γ : GL (Fin 2) ℝ) * heckeDiagMatrix N := by
  have hN : N ≠ 0 := NeZero.ne N
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h1 : ((ModularCurve.FullLevel.conjElemN N γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / N; (N : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix hN, h1]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_div_assoc', mul_div_cancel_left₀ _ hNr, mul_comm]

theorem conjElemN_eq (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    ModularCurve.FullLevel.conjElemN N γ = (heckeDiagMatrix N)⁻¹ * (γ : GL (Fin 2) ℝ) * heckeDiagMatrix N := by
  rw [mul_assoc, ← heckeDiagMatrix_mul_conjElemN, inv_mul_cancel_left]

theorem σ_conjElemN (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (z : ℂ) :
    UpperHalfPlane.σ (ModularCurve.FullLevel.conjElemN N γ) z = z := by
  have hdet : (0 : ℝ) < ((ModularCurve.FullLevel.conjElemN N γ).det : ℝ) := by
    rw [conjElemN_eq, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    have h1 : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ).det : ℝ) = 1 := by simp
    rw [h1, mul_one, inv_mul_cancel₀ (det_heckeDiagMatrix_pos N).ne']
    exact one_pos
  rw [UpperHalfPlane.σ, if_pos hdet]
  rfl

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

local notation "Γᴸ(" N "," M ")" => ((levelGroup N M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₁ᴳ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods₁ (M : ℕ) : (1 : ℝ) ∈ (Γ₁ᴳ(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods (N M : ℕ) : (1 : ℝ) ∈ (Γᴸ(N, M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_levelGroup N M)]
  exact AddSubgroup.mem_zmultiples 1

open ModularCurve

def form (N M : ℕ) [NeZero N] (W : ZMod M → ModularForm Γ₁ᴳ(M) 2) (t : ZMod M) : ModularForm Γᴸ(N, M) 2 :=
  ((1 / 12 : ℂ) * (N : ℂ)⁻¹) •
    ModularCurve.restrictForm (levelGroup_le_conj₁ N M) (ModularForm.translate (W t) (heckeDiagMatrix N))

theorem coe_form (N M : ℕ) [NeZero N] (W : ZMod M → ModularForm Γ₁ᴳ(M) 2) (t : ZMod M) :
    (⇑(form N M W t) : ℍ → ℂ) = ((1 / 12 : ℂ) * (N : ℂ)⁻¹) • ((⇑(W t) : ℍ → ℂ) ∣[(2 : ℤ)] heckeDiagMatrix N) := by
  rw [form, ModularForm.IsGLPos.coe_smul]
  rfl

theorem form_qExpansion_coeff (N M : ℕ) [NeZero N] [NeZero M]
    (W : ZMod M → ModularForm Γ₁ᴳ(M) 2)
    (hq : ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (UpperHalfPlane.qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * Complex.exp (2 * π * Complex.I / M) ^ t.val /
              (1 - Complex.exp (2 * π * Complex.I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (Complex.exp (2 * π * Complex.I / M) ^ (t.val * d) +
                  (Complex.exp (2 * π * Complex.I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)))
    (t : ZMod M) (ht0 : t ≠ 0) (a : ℕ) (htval : t.val = a) (c : ℂˣ)
    (hax : cexp (2 * π * I / M) ^ a = (c : ℂ)) (hc1 : c ≠ 1) :
    ∀ n : ℕ, (qExpansion 1 (form N M W t)).coeff n =
      (if n = 0 then (1 / 12 : ℂ) else 0) + (tateToricPoint ℂ N c).1.coeff (n : ℤ) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  set ζ : ℂ := cexp (2 * π * I / M) with hζ_def
  have hcinv : ((c⁻¹ : ℂˣ) : ℂ) = (c : ℂ)⁻¹ := Units.val_inv_eq_inv_val c
  have hqW := hq t ht0
  let F₁ := ModularForm.translate (W t) (heckeDiagMatrix N)
  let F₂ : ModularForm Γᴸ(N, M) 2 := ModularCurve.restrictForm (levelGroup_le_conj₁ N M) F₁
  have hform : form N M W t = ((1 / 12 : ℂ) * (N : ℂ)⁻¹) • F₂ := rfl
  rw [hform]
  have hFapply : ∀ τ : ℍ, (((1 / 12 : ℂ) * (N : ℂ)⁻¹) • F₂) τ = (1 / 12 : ℂ) * W t (heckeDiagMatrix N • τ) := by
    intro τ
    rw [ModularForm.IsGLPos.smul_apply, smul_eq_mul]
    have h2 : F₂ τ = ((⇑(W t) : ℍ → ℂ) ∣[(2 : ℤ)] heckeDiagMatrix N) τ := rfl
    rw [h2, slash_heckeDiagMatrix_apply 2 hN]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    have : ((N : ℂ) ^ ((2 : ℤ) - 1)) = N := by norm_num
    rw [this]; field_simp

  set w : ℕ → ℂ := fun m => (qExpansion 1 (W t)).coeff m with hw
  set D : ℕ → ℂ := fun n =>
    (if n = 0 then (1 / 12 : ℂ) else 0) + (tateToricPoint ℂ N c).1.coeff (n : ℤ) with hD
  suffices hHas : ∀ τ : ℍ,
      HasSum (fun m => D m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) ((((1 / 12 : ℂ) * (N : ℂ)⁻¹) • F₂) τ) by
    intro n
    exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods N M) hHas n).symm
  intro τ
  set q : ℂ := cexp (2 * π * I * (τ : ℂ)) with hq_def
  have hqP : Function.Periodic.qParam 1 (τ : ℂ) = q := by
    simp [Function.Periodic.qParam, hq_def]
  simp_rw [hqP, smul_eq_mul]
  rw [hFapply τ]

  have hFact : Fact (IsCusp OnePoint.infty Γ₁ᴳ(M)) :=
    ⟨(Γ₁ᴳ(M)).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods₁ M)⟩
  have hWsum := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (W t) (one_mem_strictPeriods₁ M))
    (ModularFormClass.holo (W t)) (ModularFormClass.bdd_at_infty (W t)) (heckeDiagMatrix N • τ)
  have hqN : Function.Periodic.qParam 1 (((heckeDiagMatrix N • τ : ℍ) : ℂ)) = q ^ N := by
    rw [coe_heckeDiagMatrix_smul hN]
    simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
    rw [hq_def, ← Complex.exp_nat_mul]; ring_nf
  simp_rw [hqN, smul_eq_mul, ← pow_mul] at hWsum

  have hr : HasSum (fun n => (∑ m ∈ S₀ N n, (qExpansion 1 (W t)).coeff m) * q ^ n)
      (W t (heckeDiagMatrix N • τ)) := by
    have h := hasSum_regroup (fun m => (qExpansion 1 (W t)).coeff m) (fun m => N * m) q (S₀ N)
      (fun n m => mem_S₀ hN0 m) hWsum.summable
    rwa [hWsum.tsum_eq] at h
  have htot := hr.mul_left (1 / 12 : ℂ)
  convert htot using 1 <;> try rfl
  funext n
  rw [← mul_assoc]
  congr 1

  rw [sum_S₀ hN0, hD]
  dsimp only
  rw [tateToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
  have hxa : ζ ^ a = (c : ℂ) := hax
  have hx1 : (1 - (c : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hc1 (Units.val_eq_one.mp h.symm)
  have hz1 : ∀ d : ℕ, ζ ^ (a * d) = (c : ℂ) ^ d := fun d => by rw [pow_mul, hxa]
  have hz2 : ∀ d : ℕ, ζ⁻¹ ^ (a * d) = (c : ℂ)⁻¹ ^ d := fun d => by
    rw [inv_pow, pow_mul, hxa, inv_pow]
  by_cases hn : N ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left m hN0]
    rw [hqW m, htval]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    ·
      simp only [mul_zero, ↓reduceIte]
      rw [Ring.inverse_eq_inv', hxa]
      field_simp
    · have hm0 : m ≠ 0 := hm.ne'
      have hNm0 : N * m ≠ 0 := Nat.mul_ne_zero hN hm0
      simp only [hNm0, hm0, ↓reduceIte, hcinv, hz1, hz2]
      rw [sum_divisors_toric hN0 (c : ℂ) m]
      ring
  · have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero N)
    simp only [hn0, hn, ↓reduceIte]
    rw [Finset.sum_eq_zero]
    · ring
    · intro d hd
      rw [if_neg]
      intro hNd
      exact hn (dvd_trans hNd (Nat.dvd_of_mem_divisors hd))

section Index

variable (M : ℕ) [NeZero M]

def zeta : ℂ := cexp (2 * π * I / M)

theorem zeta_prim : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M (NeZero.ne M)

def idx (c : ℂˣ) : ZMod M :=
  if h : ∃ i < M, zeta M ^ i = (c : ℂ) then ((Classical.choose h : ℕ) : ZMod M) else 0

theorem idx_spec {c : ℂˣ} (hc : c ^ M = 1) :
    ∃ a : ℕ, a < M ∧ (idx M c).val = a ∧ zeta M ^ a = (c : ℂ) := by
  have hcM : (c : ℂ) ^ M = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have h : ∃ i < M, zeta M ^ i = (c : ℂ) := (zeta_prim M).eq_pow_of_pow_eq_one hcM
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, ?_, (Classical.choose_spec h).2⟩
  rw [idx, dif_pos h, ZMod.val_natCast_of_lt (Classical.choose_spec h).1]

theorem zeta_pow_val_idx {c : ℂˣ} (hc : c ^ M = 1) : zeta M ^ (idx M c).val = (c : ℂ) := by
  obtain ⟨a, -, hva, hza⟩ := idx_spec M hc
  rw [hva, hza]

theorem idx_ne_zero {c : ℂˣ} (hc : c ^ M = 1) (hc1 : c ≠ 1) : idx M c ≠ 0 := by
  intro h
  have := zeta_pow_val_idx M hc
  rw [h, ZMod.val_zero, pow_zero] at this
  exact hc1 (Units.ext (by rw [Units.val_one, ← this]))

theorem zeta_pow_val_natCast (x : ℕ) : zeta M ^ ((x : ZMod M)).val = zeta M ^ x := by
  rw [ZMod.val_natCast]
  have h := pow_mod_orderOf (zeta M) x
  rwa [← (zeta_prim M).eq_orderOf] at h

theorem idx_eq_of_zeta_pow {c : ℂˣ} (hc : c ^ M = 1) {k : ZMod M} (hk : zeta M ^ k.val = (c : ℂ)) :
    idx M c = k := by
  apply ZMod.val_injective
  apply (zeta_prim M).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [zeta_pow_val_idx M hc, hk]

theorem idx_zpow {c : ℂˣ} (hc : c ^ M = 1) (d : ℤ) :
    idx M (c ^ d) = idx M c * ((d : ℤ) : ZMod M) := by
  have hM0 : (0 : ℤ) < (M : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hcd : (c ^ d) ^ M = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc, _root_.one_zpow]
  apply idx_eq_of_zeta_pow M hcd

  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = d % M := ⟨(d % M).toNat, Int.toNat_of_nonneg (Int.emod_nonneg d hM0.ne')⟩
  have hde : ((d : ℤ) : ZMod M) = ((e : ℕ) : ZMod M) := by
    rw [← Int.cast_natCast, he, ZMod.intCast_mod]
  have hcde : c ^ d = c ^ e := by
    rw [← zpow_natCast, he]
    exact zpow_eq_zpow_emod d (by exact_mod_cast hc)
  obtain ⟨a, -, hva, hza⟩ := idx_spec M hc
  rw [hde, hcde, ← ZMod.natCast_zmod_val (idx M c), hva, ← Nat.cast_mul, zeta_pow_val_natCast,
    pow_mul, hza, Units.val_pow_eq_pow_val]

end Index

theorem main (N M : ℕ) [NeZero N] [NeZero M] :
    ∃ X : ℂˣ → ModularForm Γᴸ(N, M) 2,
      (∀ c : ℂˣ, c ^ M = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(X c))) =
          (tateToricPoint ℂ N c).1 + HahnSeries.C ((12 : ℂ)⁻¹)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ Gamma0 M → ∀ c : ℂˣ, c ^ M = 1 → c ≠ 1 →
        (⇑(X c) ∣[(2 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(X (c ^ ((ρ 1 1 : ℤ))))) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨W, -, hWs, hq⟩ := PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M
  refine ⟨fun c => form N M W (idx M c), ?_, ?_⟩
  · intro c hc hc1
    obtain ⟨a, ha, hva, hza⟩ := idx_spec M hc
    have hcoeff := form_qExpansion_coeff N M W hq (idx M c) (idx_ne_zero M hc hc1) a hva c hza hc1

    rw [tateToricPoint_fst, ← HahnSeries.ofPowerSeries_C, ← map_add]
    congr 1
    ext n
    rw [hcoeff n, map_add, PowerSeries.coeff_C, tateToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, add_comm]
    congr 1
    split_ifs <;> simp
  · intro ρ hρ c hc hc1
    rw [coe_form, coe_form, idx_zpow M hc, ← hWs _ ρ hρ, ModularForm.smul_slash, σ_conjElemN, SL_slash,
      ← SlashAction.slash_mul, ← SlashAction.slash_mul, conjElemN_eq, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]

end ToricDivision2

open scoped MatrixGroups ModularForm in
theorem solution
    (N n : ℕ) [NeZero N] [NeZero n] :
    ∃ X : ℂˣ → ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(X c))) =
          (ModularCurve.tateToricPoint ℂ N c).1 + HahnSeries.C ((12 : ℂ)⁻¹)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 n → ∀ c : ℂˣ, c ^ n = 1 → c ≠ 1 →
        (⇑(X c) ∣[(2 : ℤ)] ModularCurve.FullLevel.conjElemN N ρ) = ⇑(X (c ^ ((ρ 1 1 : ℤ))))) :=
  ToricDivision2.main N n

end
end S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_eq_tateToricPoint_fst_and_slash_conjElemN_eq (solution)
