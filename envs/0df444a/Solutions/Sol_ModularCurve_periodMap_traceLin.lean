-- Prove2me | solution 1 for ModularCurve.periodMap_traceLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/794e83ed-32d9-5cd2-af98-abfed7d2fd48

import Definitions.Def_ModularCurve_PeriodTransfer
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_Period_traceSum_period_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMap_traceLin

set_option autoImplicit false

open CongruenceSubgroup UpperHalfPlane ModularCurve ModularCurve.Period
open scoped MatrixGroups ModularForm

namespace INH
namespace SolR1

theorem slash_two_eq_of_coe_eq_smul (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (β : SL(2, ℤ)) (c : ℝ) (hc : 0 < c)
    (h : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = c • ((β : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) :
    f ∣[(2 : ℤ)] g = f ∣[(2 : ℤ)] β := by
  have hent : ∀ i j, (g : Matrix (Fin 2) (Fin 2) ℝ) i j = c * ((β : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := by
    intro i j; rw [h]; rfl
  have hdetβ : ((β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)
      - ((β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) * ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) = 1 := by
    have := β.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = c ^ 2 := by
    rw [Matrix.det_fin_two, hent, hent, hent, hent]
    linear_combination c ^ 2 * hdetβ
  have hdetu : (g.det.val : ℝ) = c ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]
  have hgpos : 0 < g.det.val := by rw [hdetu]; positivity
  ext τ
  rw [ModularForm.SL_slash, ModularForm.slash_apply, ModularForm.slash_apply]

  have hσg : ∀ w : ℂ, σ g w = w := fun w => by
    have : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; positivity
    simp [σ, this]
  have hσβ : ∀ w : ℂ, σ (β : GL (Fin 2) ℝ) w = w := fun w => by
    simp [σ]

  have hden : denom g τ = (c : ℂ) * denom (β : GL (Fin 2) ℝ) τ := by
    simp only [denom, hent]
    push_cast
    simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    ring
  have hnum : num g τ = (c : ℂ) * num (β : GL (Fin 2) ℝ) τ := by
    simp only [num, hent]
    push_cast
    simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    ring
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hsmul : g • τ = (β : GL (Fin 2) ℝ) • τ := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hgpos, coe_smul_of_det_pos (by simp), hnum, hden,
      mul_div_mul_left _ _ hc']
  have hdβ : (((β : GL (Fin 2) ℝ)).det.val : ℝ) = 1 := by simp
  rw [hσg, hσβ, hsmul, hdetu, hdβ, hden]
  have hd : denom (β : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, zpow_one, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  rw [abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
  push_cast
  field_simp
  simp

section Reps

variable {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q)

def betaMat (j : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![W.a, W.a * j + W.b; (W.R : ℤ), (W.R : ℤ) * j + (q : ℤ)]

theorem det_betaMat (j : ℤ) : (betaMat W j).det = 1 := by
  rw [betaMat, Matrix.det_fin_two_of]
  linear_combination W.bezout

def betaSL (j : ℤ) : SL(2, ℤ) := ⟨betaMat W j, det_betaMat W j⟩

@[scoped simp] theorem betaSL_apply_00 (j : ℤ) : (betaSL W j : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = W.a := rfl
@[scoped simp] theorem betaSL_apply_01 (j : ℤ) : (betaSL W j : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = W.a * j + W.b := rfl
@[scoped simp] theorem betaSL_apply_10 (j : ℤ) : (betaSL W j : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (W.R : ℤ) := rfl
@[scoped simp] theorem betaSL_apply_11 (j : ℤ) :
    (betaSL W j : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (W.R : ℤ) * j + (q : ℤ) := rfl

theorem betaSL_mem (j : ℤ) : betaSL W j ∈ Gamma0 W.R := by
  rw [Gamma0_mem]
  show (((betaSL W j : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod W.R) = 0
  rw [betaSL_apply_10]
  simp

theorem alGL_mul_heckeMatrix [NeZero M] (hq : q ≠ 0) (j : ℕ) :
    (((W.alGL * ModularForm.heckeMatrix q j : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
      = (q : ℝ) • ((betaSL W (j : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
  have hmat : W.mat = !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)] := rfl
  ext i j'
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_entry,
    ModularForm.AtkinLehnerDatum.alGL_entry, ModularForm.val_heckeMatrix hq]
  fin_cases i <;> fin_cases j' <;> simp [hmat, betaSL, betaMat] <;> ring

end Reps

section Coset

variable {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)

theorem slash_eq_self_of_mem (f : CuspForm (Gamma0 M) 2) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) :
    (⇑f) ∣[(2 : ℤ)] δ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hδ)

def rep : Option (Fin q) → SL(2, ℤ)
  | none => 1
  | some j => betaSL W ((j : ℕ) : ℤ)

theorem rep_mem (i : Option (Fin q)) : rep W i ∈ Gamma0 W.R := by
  cases i with
  | none => exact Subgroup.one_mem _
  | some j => exact betaSL_mem W _

def cosetOf (i : Option (Fin q)) : ↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R) :=
  QuotientGroup.mk ⟨(rep W i)⁻¹, Subgroup.inv_mem _ (rep_mem W i)⟩

include hq

theorem not_q_dvd_R : ¬ (q : ℤ) ∣ (W.R : ℤ) := by
  rintro ⟨k, hk⟩
  have h1 : (q : ℤ) ∣ 1 := ⟨W.a - k * W.b, by linear_combination -W.bezout - W.b * hk⟩
  have := Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le q)) h1
  have hq1 := hq.one_lt
  omega

theorem R_lt_M [NeZero M] : (W.R : ℤ) < (M : ℤ) := by
  have hM : (M : ℤ) = q * W.R := by exact_mod_cast W.hM
  have hR : (0 : ℤ) < W.R := by exact_mod_cast W.R_pos
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  nlinarith

omit hq in

theorem mem_Gamma0_iff_dvd (γ : SL(2, ℤ)) : γ ∈ Gamma0 M ↔ (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

omit hq in
theorem coe_inv_apply_10 (γ : SL(2, ℤ)) :
    ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp

omit hq in
theorem coe_inv_apply_00 (γ : SL(2, ℤ)) :
    ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp

theorem cosetOf_injective [NeZero M] : Function.Injective (cosetOf (M := M) W) := by
  have hqR := not_q_dvd_R W hq
  have hRM := R_lt_M W hq
  have hR : (0 : ℤ) < W.R := by exact_mod_cast W.R_pos
  have hM : (M : ℤ) = q * W.R := by exact_mod_cast W.hM
  have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq

  have key : ∀ i i' : Option (Fin q), cosetOf W i = cosetOf W i' →
      (M : ℤ) ∣ ((rep W i * (rep W i')⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    intro i i' h
    have h' := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    have : ((⟨(rep W i)⁻¹, Subgroup.inv_mem _ (rep_mem W i)⟩ : ↥(Gamma0 W.R))⁻¹ *
        ⟨(rep W i')⁻¹, Subgroup.inv_mem _ (rep_mem W i')⟩ : ↥(Gamma0 W.R)) =
          (rep W i * (rep W i')⁻¹ : SL(2, ℤ)) := by
      simp
    rw [this] at h'
    exact (mem_Gamma0_iff_dvd (M := M) _).mp h'
  have entry : ∀ i i' : Option (Fin q),
      ((rep W i * (rep W i')⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (rep W i : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (rep W i' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
          - (rep W i : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (rep W i' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    intro i i'
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_inv_apply_00,
      coe_inv_apply_10]
    ring
  intro i i' h
  have hdvd := key i i' h
  rw [entry] at hdvd
  rcases i with _ | i <;> rcases i' with _ | i'
  · rfl
  · exfalso
    simp only [rep, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      Matrix.one_apply_eq, betaSL_apply_10, betaSL_apply_11, zero_mul, one_mul, zero_sub] at hdvd
    have := Int.le_of_dvd hR ((Int.dvd_neg).mp hdvd)
    omega
  · exfalso
    simp only [rep, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      Matrix.one_apply_eq, betaSL_apply_10, betaSL_apply_11, mul_zero, mul_one, sub_zero] at hdvd
    have := Int.le_of_dvd hR hdvd
    omega
  · simp only [rep, betaSL_apply_10, betaSL_apply_11] at hdvd

    rw [hM] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have h2 : (W.R : ℤ) * (W.R * (((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ)) - q * k) = 0 := by
      linear_combination hk
    have h3 : (q : ℤ) ∣ W.R * (((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := by
      refine ⟨k, ?_⟩
      have := (mul_eq_zero.mp h2).resolve_left hR.ne'
      linear_combination this
    have h4 : (q : ℤ) ∣ ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) :=
      (hqprime.dvd_or_dvd h3).resolve_left hqR
    have hi := i.isLt
    have hi' := i'.isLt
    congr 1
    apply Fin.ext
    rcases h4 with ⟨k, hk⟩
    have : k = 0 := by nlinarith
    subst this
    omega

theorem cosetOf_surjective : Function.Surjective (cosetOf (M := M) W) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqR := not_q_dvd_R W hq
  have hM : (M : ℤ) = q * W.R := by exact_mod_cast W.hM
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x

  set A : ℤ := ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hA
  set C : ℤ := ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hC
  have hRC : (W.R : ℤ) ∣ C := by
    have := g.2
    rw [Gamma0_mem] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hcop : IsCoprime (q : ℤ) (W.R : ℤ) := ⟨W.a, -W.b, by linear_combination W.bezout⟩

  have crit : ∀ i, (M : ℤ) ∣ ((rep W i * (g : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 →
      cosetOf W i = QuotientGroup.mk g := by
    intro i hdvd
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    have : ((⟨(rep W i)⁻¹, Subgroup.inv_mem _ (rep_mem W i)⟩ : ↥(Gamma0 W.R))⁻¹ * g : ↥(Gamma0 W.R)) =
        (rep W i * (g : SL(2, ℤ)) : SL(2, ℤ)) := by simp
    rw [this]
    exact (mem_Gamma0_iff_dvd (M := M) _).mpr hdvd
  have entry : ∀ i, ((rep W i * (g : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (rep W i : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * A + (rep W i : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * C := by
    intro i
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hqC : (q : ℤ) ∣ C
  · refine ⟨none, crit none ?_⟩
    rw [entry]
    simp only [rep, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      Matrix.one_apply_eq, zero_mul, one_mul, zero_add, hM]
    exact hcop.mul_dvd hqC hRC
  ·
    have hC0 : (C : ZMod q) ≠ 0 := by
      intro h0; exact hqC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
    let jz : ZMod q := -(A : ZMod q) * (C : ZMod q)⁻¹
    let j : Fin q := ⟨jz.val, ZMod.val_lt jz⟩
    refine ⟨some j, crit (some j) ?_⟩
    rw [entry]
    simp only [rep, betaSL_apply_10, betaSL_apply_11]

    rw [hM]
    have hqpart : (q : ℤ) ∣ A + ((j : ℕ) : ℤ) * C := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      have hj : ((j : ℕ) : ZMod q) = jz := by
        show ((jz.val : ℕ) : ZMod q) = jz
        exact ZMod.natCast_zmod_val jz
      rw [hj]
      simp only [jz]
      rw [neg_mul, neg_mul, mul_assoc, inv_mul_cancel₀ hC0, mul_one, add_neg_cancel]
    have h1 : (q : ℤ) * W.R ∣ W.R * (A + ((j : ℕ) : ℤ) * C) := by
      rw [mul_comm (q : ℤ)]
      exact mul_dvd_mul_left _ hqpart
    have h2 : (q : ℤ) * W.R ∣ (q : ℤ) * C := by
      exact mul_dvd_mul_left _ hRC
    convert dvd_add h1 h2 using 1
    · rfl
    ring

theorem cosetOf_bijective [NeZero M] : Function.Bijective (cosetOf (M := M) W) :=
  ⟨cosetOf_injective W hq, cosetOf_surjective W hq⟩

end Coset

section Final

variable {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)

omit hq in
theorem slash_traceRep_cosetOf (f : CuspForm (Gamma0 M) 2) (i : Option (Fin q)) :
    (⇑f) ∣[(2 : ℤ)] ((traceRep (Δ := Gamma0 M) (cosetOf W i) : ↥(Gamma0 W.R)) : SL(2, ℤ))
      = (⇑f) ∣[(2 : ℤ)] (rep W i) := by
  unfold cosetOf traceRep
  obtain ⟨h, H⟩ := QuotientGroup.mk_out_eq_mul ((Gamma0 M).subgroupOf (Gamma0 W.R))
    (⟨(rep W i)⁻¹, Subgroup.inv_mem _ (rep_mem W i)⟩ : ↥(Gamma0 W.R))
  rw [H]
  have hh : ((h : ↥(Gamma0 W.R)) : SL(2, ℤ)) ∈ Gamma0 M := Subgroup.mem_subgroupOf.mp h.2
  have : (((⟨(rep W i)⁻¹, Subgroup.inv_mem _ (rep_mem W i)⟩ * (h : ↥(Gamma0 W.R)))⁻¹ : ↥(Gamma0 W.R)) :
      SL(2, ℤ)) = ((h : ↥(Gamma0 W.R)) : SL(2, ℤ))⁻¹ * rep W i := by
    simp [mul_inv_rev]
  rw [this, SlashAction.slash_mul, slash_eq_self_of_mem f (Subgroup.inv_mem _ hh)]

include hq in

theorem coset_sum [NeZero M] [Fintype (↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R))] (f : CuspForm (Gamma0 M) 2) :
    (∑ x : ↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R),
        (⇑f) ∣[(2 : ℤ)] ((traceRep x : ↥(Gamma0 W.R)) : SL(2, ℤ)))
      = ⇑(CuspForm.traceLin W hq f) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [← Fintype.sum_bijective (cosetOf W) (cosetOf_bijective W hq) (fun i => (⇑f) ∣[(2 : ℤ)] rep W i) _
    (fun i => (slash_traceRep_cosetOf W f i).symm)]
  rw [Fintype.sum_option]
  have htr : ⇑(CuspForm.traceLin W hq f) = ⇑f + ModularForm.heckeU 2 q (ModularForm.alSlash W 2 ⇑f) := by
    ext τ; rfl
  rw [htr, ModularForm.heckeU_def, ← Fin.sum_univ_eq_sum_range]
  congr 1
  · show (⇑f) ∣[(2 : ℤ)] (1 : SL(2, ℤ)) = ⇑f
    exact SlashAction.slash_one _ _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ModularForm.alSlash_def, ← SlashAction.slash_mul]
    exact (slash_two_eq_of_coe_eq_smul (⇑f) _ _ (q : ℝ) (by exact_mod_cast hq.pos)
      (alGL_mul_heckeMatrix W hq0 j)).symm

noncomputable def moeb (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / denom g z

theorem hasDerivAt_moeb (g : GL (Fin 2) ℝ) (τ : ℍ) :
    HasDerivAt (moeb g) (((g.det.val : ℝ) : ℂ) / (denom g τ) ^ 2) (τ : ℂ) := by
  have hd : denom g (τ : ℂ) ≠ 0 := denom_ne_zero g τ
  have hn : HasDerivAt (num g) ((g 0 0 : ℝ) : ℂ) (τ : ℂ) := by
    have : num g = fun z : ℂ => ((g 0 0 : ℝ) : ℂ) * z + ((g 0 1 : ℝ) : ℂ) := rfl
    rw [this]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((g 0 0 : ℝ) : ℂ)).add_const ((g 0 1 : ℝ) : ℂ)
  have hdn : HasDerivAt (denom g) ((g 1 0 : ℝ) : ℂ) (τ : ℂ) := by
    have : denom g = fun z : ℂ => ((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ) := rfl
    rw [this]
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul ((g 1 0 : ℝ) : ℂ)).add_const ((g 1 1 : ℝ) : ℂ)
  have := hn.div hdn hd
  convert this using 1 <;> try with_reducible_and_instances rfl
  all_goals try rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [num, denom]
  push_cast
  ring

theorem hasDerivAt_conjPrimitive {F f : ℍ → ℂ} (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt (conjPrimitive g F ∘ ofComplex) ((f ∣[(2 : ℤ)] g) τ) ↑τ := by
  have hm : moeb g (τ : ℂ) = ((g • τ : ℍ) : ℂ) := (coe_smul_of_det_pos hg τ).symm
  have houter : HasDerivAt (F ∘ ofComplex) (f (g • τ)) (moeb g (τ : ℂ)) := by
    rw [hm]; exact hF (g • τ)
  have hcomp := houter.comp (τ : ℂ) (hasDerivAt_moeb g τ)
  have heq : (conjPrimitive g F ∘ ofComplex) =ᶠ[nhds (τ : ℂ)] ((F ∘ ofComplex) ∘ moeb g) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hz' : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
    have hsm : ((g • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) = moeb g z := coe_smul_of_det_pos hg ⟨z, hz⟩
    have him : 0 < (moeb g z).im := by rw [← hsm]; exact (g • (⟨z, hz⟩ : ℍ)).im_pos
    have hw : ofComplex (moeb g z) = g • (⟨z, hz⟩ : ℍ) := by
      rw [ofComplex_apply_of_im_pos him]
      exact UpperHalfPlane.ext hsm.symm
    simp only [Function.comp_apply, conjPrimitive, hz', hw]
  refine (hcomp.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [ModularForm.slash_apply]
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : σ g (f (g • τ)) = f (g • τ) := by
    simp [σ, hg']
  rw [hσ, abs_of_pos hg]
  have hd : denom g (τ : ℂ) ≠ 0 := denom_ne_zero g τ
  rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  field_simp

omit hq in

theorem hasDerivAt_traceSum [Fintype (↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R))]
    {F : ℍ → ℂ} (f : CuspForm (Gamma0 M) 2)
    (hFd : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt (traceSum (Gamma0 W.R) (Gamma0 M) F ∘ ofComplex)
      ((∑ x : ↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R),
        (⇑f) ∣[(2 : ℤ)] ((traceRep x : ↥(Gamma0 W.R)) : SL(2, ℤ))) τ) ↑τ := by
  have hfun : (traceSum (Gamma0 W.R) (Gamma0 M) F ∘ ofComplex) = fun z =>
      ∑ x : ↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R),
        (conjPrimitive (((traceRep x : ↥(Gamma0 W.R)) : SL(2, ℤ)) : GL (Fin 2) ℝ) F ∘ ofComplex) z := by
    ext z
    simp only [Function.comp_apply, traceSum, conjPrimitive]
    rfl
  rw [hfun, Finset.sum_apply]
  refine HasDerivAt.fun_sum fun x _ => ?_
  have hdet : 0 < (((traceRep x : ↥(Gamma0 W.R)) : SL(2, ℤ)) : GL (Fin 2) ℝ).det.val := by
    have h1 : (((traceRep x : ↥(Gamma0 W.R)) : SL(2, ℤ)) : GL (Fin 2) ℝ).det.val = 1 := by simp
    rw [h1]; exact one_pos
  have := hasDerivAt_conjPrimitive (((traceRep x : ↥(Gamma0 W.R)) : SL(2, ℤ)) : GL (Fin 2) ℝ) hdet hFd τ
  rwa [← ModularForm.SL_slash] at this

end Final

end INH.SolR1
p2m_reactivate "P2MW.S_ModularCurve_periodMap_traceLin.INH P2MW.S_ModularCurve_periodMap_traceLin.INH.SolR1"
p2m_reactivate "P2MW.S_ModularCurve_periodMap_traceLin.INH"

open CongruenceSubgroup ModularCurve ModularCurve.Period INH.SolR1 in
open scoped MatrixGroups in
theorem solution {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)
    (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    ModularCurve.periodMap W.R (CuspForm.traceLin W hq f) =
      HeckeEis.coresHom ((Gamma0 M).subgroupOf (Gamma0 W.R))
        (HeckeEis.pullbackHom ((Gamma0 W.R).subtype.subgroupComap (Gamma0 M))
          (ModularCurve.periodMap M f)) := by
  haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
  letI : Fintype (↥(Gamma0 W.R) ⧸ (Gamma0 M).subgroupOf (Gamma0 W.R)) :=
    ((Gamma0 M).subgroupOf (Gamma0 W.R)).fintypeQuotientOfFiniteIndex
  obtain ⟨F, hFd, -, hFeq, -⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  have hTd : ∀ τ : UpperHalfPlane, HasDerivAt (traceSum (Gamma0 W.R) (Gamma0 M) F ∘ UpperHalfPlane.ofComplex)
      ((CuspForm.traceLin W hq f) τ) ↑τ := by
    intro τ
    have := hasDerivAt_traceSum W f hFd τ
    rwa [coset_sum W hq f] at this
  rw [ModularCurve.periodMap_eq_periodHom hFeq.traceSum hTd, ModularCurve.periodMap_eq_periodHom hFeq hFd]
  refine AddMonoidHom.ext fun g => ?_
  set γ : ↥(Gamma0 W.R) := Additive.toMul g with hγ
  change hFeq.traceSum.period γ =
    HeckeEis.coresHom ((Gamma0 M).subgroupOf (Gamma0 W.R))
      (HeckeEis.pullbackHom ((Gamma0 W.R).subtype.subgroupComap (Gamma0 M)) hFeq.periodHom)
        (Additive.ofMul γ)
  rw [ModularCurve.Period.traceSum_period_eq hFeq γ, HeckeEis.coresHom_apply]
  exact Fintype.sum_bijective (fun x => γ⁻¹ • x) (MulAction.bijective γ⁻¹) _ _ fun x => rfl

end S_ModularCurve_periodMap_traceLin
end P2MW
export P2MW.S_ModularCurve_periodMap_traceLin (solution)
