-- Prove2me | solution 1 for ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cbca79e3-83f2-57ca-8e5e-657ea616981d

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint

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
  convert h1 using 1 <;> try rfl
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

local notation "Γᴸ(" N "," n ")" => ((levelGroup N n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₁ᴳ(" N ")" => ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods₁ (N : ℕ) : (1 : ℝ) ∈ (Γ₁ᴳ(N)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods (N n : ℕ) : (1 : ℝ) ∈ (Γᴸ(N, n)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_levelGroup N n)]
  exact AddSubgroup.mem_zmultiples 1

open ModularCurve

theorem main (N n : ℕ) [NeZero N] [NeZero n] (hNn : N ∣ n) (c : ℂˣ) (hc : c ^ n = 1) (hc1 : c ≠ 1) :
    ∃ F : ModularForm Γᴸ(N, n) 2,
      ∀ m : ℕ, (qExpansion 1 F).coeff m =
        (if m = 0 then (1 / 12 : ℂ) else 0) + (tateToricPoint ℂ N c).1.coeff (m : ℤ) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hnn0 : n ≠ 0 := NeZero.ne n
  set ζ : ℂ := cexp (2 * π * I / n) with hζ_def
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hnn0
  have hcN : (c : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  obtain ⟨a, ha, hax⟩ := hζ.eq_pow_of_pow_eq_one hcN
  have hcinv : ((c⁻¹ : ℂˣ) : ℂ) = (c : ℂ)⁻¹ := Units.val_inv_eq_inv_val c
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hc1
    exact Units.ext (by rw [Units.val_one, ← hax, pow_zero])
  set t : ZMod n := (a : ZMod n) with ht_def
  have htval : t.val = a := ZMod.val_natCast_of_lt ha
  have ht0 : t ≠ 0 := by
    intro h
    apply ha0
    rw [← htval, h, ZMod.val_zero]

  obtain ⟨W, -, -, hq⟩ := PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff n
  have hqW := hq t ht0

  let F₁ := ModularForm.translate (W t) (heckeDiagMatrix N)
  let F₂ : ModularForm Γᴸ(N, n) 2 := ModularCurve.restrictForm (levelGroup_le_conj₁ N n) F₁
  refine ⟨((1 / 12 : ℂ) * (N : ℂ)⁻¹) • F₂, ?_⟩
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
    intro m
    exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods N n) hHas m).symm
  intro τ
  set q : ℂ := cexp (2 * π * I * (τ : ℂ)) with hq_def
  have hqP : Function.Periodic.qParam 1 (τ : ℂ) = q := by
    simp [Function.Periodic.qParam, hq_def]
  simp_rw [hqP, smul_eq_mul]
  rw [hFapply τ]

  have hFact : Fact (IsCusp OnePoint.infty Γ₁ᴳ(n)) :=
    ⟨(Γ₁ᴳ(n)).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods₁ n)⟩
  have hWsum := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (W t) (one_mem_strictPeriods₁ n))
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
    rw [hqW m, ← hζ_def, htval]
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

end ToricDivision2
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint.ToricDivision2"

open scoped MatrixGroups in
theorem solution
    (N n : ℕ) [NeZero N] [NeZero n] (hNn : N ∣ n) (c : ℂˣ) (hc : c ^ n = 1) (hc1 : c ≠ 1) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma1 n ⊓ CongruenceSubgroup.Gamma0 (N * n) :
        Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2,
      ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 F).coeff m =
        (if m = 0 then (1 / 12 : ℂ) else 0) + (ModularCurve.tateToricPoint ℂ N c).1.coeff (m : ℤ) :=
  ToricDivision2.main N n hNn c hc hc1

end
end S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint (solution)
