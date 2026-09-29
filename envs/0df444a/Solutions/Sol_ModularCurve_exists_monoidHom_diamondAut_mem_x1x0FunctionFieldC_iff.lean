-- Prove2me | solution 1 for ModularCurve.exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3ed57bcf-a73d-556f-a849-0cbe8c1f78d8

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries ModularCurve
open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondGalois

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {M : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem qC_mul {a b : ℤ} (f : ModularForm Γ₁(M) a) (g : ModularForm Γ₁(M) b) :
    qC ((⇑f : ℍ → ℂ) * ⇑g) = qC ⇑f * qC ⇑g := by
  rw [qC, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) f g, map_mul]
  rfl

theorem qC_coe_mul {a b : ℤ} (f : ModularForm Γ₁(M) a) (g : ModularForm Γ₁(M) b) :
    qC (⇑(f.mul g)) = qC ⇑f * qC ⇑g := by
  rw [ModularForm.coe_mul, qC_mul]

theorem qC_smul {a : ℤ} (c : ℂ) (f : ModularForm Γ₁(M) a) : qC (⇑(c • f)) = c • qC ⇑f := by
  rw [ModularForm.IsGLPos.coe_smul, qC,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f, qC,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by
  rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by
  rw [qC, qExpansion_one, map_one]

theorem qC_coe_one : qC (⇑(1 : ModularForm Γ₁(M) 0)) = 1 := by
  rw [ModularForm.one_coe_eq_one]; exact qC_one

variable [NeZero M]

theorem hasSum_qC {a : ℤ} (f : ModularForm Γ₁(M) a) (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 (⇑f)).coeff m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M))
    f.holo' (ModularFormClass.bdd_at_infty f) τ

theorem coe_eq_of_qC_eq {a b : ℤ} (f : ModularForm Γ₁(M) a) (g : ModularForm Γ₁(M) b)
    (h : qC ⇑f = qC ⇑g) : (⇑f : ℍ → ℂ) = ⇑g := by
  have h' : qExpansion 1 (⇑f) = qExpansion 1 (⇑g) := HahnSeries.ofPowerSeries_injective h
  funext τ
  have hf := hasSum_qC f τ
  have hg := hasSum_qC g τ
  rw [h'] at hf
  exact hf.unique hg

omit [NeZero M] in
theorem qC_eq_zero_iff {a : ℤ} (f : ModularForm Γ₁(M) a) : qC ⇑f = 0 ↔ f = 0 := by
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M) f, qC]
  constructor
  · intro h
    exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

end QExp

section Slash

variable {M : ℕ} {k : ℤ}

theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    show ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

theorem isBoundedAt_slash [NeZero M] (f : ModularForm Γ₁(M) k) (γ : SL(2, ℤ)) {c : OnePoint ℝ}
    (hc : IsCusp c Γ₁(M)) : IsBoundedAt c ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) k := by
  have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₁(M)).mp hc
  have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) Γ₁(M) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact hcSL.smul_of_mem ⟨γ, rfl⟩
  exact IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

def diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁(M) k) :
    ModularForm Γ₁(M) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Gamma1 M := conj_mem_Gamma1 hγ hA
    have hGL : (γ : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((γ * A * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    show ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    exact isBoundedAt_slash f γ hc

@[scoped simp] theorem coe_diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm Γ₁(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem coe_diamondSlash_SL [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm Γ₁(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [coe_diamondSlash, ModularForm.SL_slash]

theorem slash_slash_inv (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ) ∣[k] γ⁻¹ = F := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem diamondSlash_ne_zero [NeZero M] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    {f : ModularForm Γ₁(M) k} (hf : f ≠ 0) : diamondSlash γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h1 : (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = 0 := by rw [h]; rfl
  rw [coe_diamondSlash_SL] at h1
  have h2 : (⇑f : ℍ → ℂ) = 0 := by
    rw [← slash_slash_inv (k := k) (⇑f) γ, h1, SlashAction.zero_slash]
  exact DFunLike.ext' (h2.trans ModularForm.coe_zero.symm)

theorem qC_slash_ne_zero [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm Γ₁(M) k}
    (hg : qC ⇑g ≠ 0) : qC ((⇑g : ℍ → ℂ) ∣[k] γ) ≠ 0 := by
  rw [← coe_diamondSlash_SL γ hγ, Ne, qC_eq_zero_iff]
  exact diamondSlash_ne_zero hγ (fun h => hg ((qC_eq_zero_iff g).mpr h))

theorem apply_zero_zero_mul_apply_one_one {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have := congrArg (Int.cast : ℤ → ZMod M) h1
  push_cast at this
  rw [hc, mul_zero, sub_zero] at this
  exact this

theorem mul_inv_mem_Gamma1 {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 0 0 : ℤ) : ZMod M) = ((γ' 0 0 : ℤ) : ZMod M)) : γ * γ'⁻¹ ∈ Gamma1 M := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ'
  have hdet := apply_zero_zero_mul_apply_one_one hγ
  have hdet' := apply_zero_zero_mul_apply_one_one hγ'
  have hinv : (γ'⁻¹ : SL(2, ℤ)) = ⟨!![γ' 1 1, -(γ' 0 1); -(γ' 1 0), γ' 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ'.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ'
  rw [Gamma1_mem, hinv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_add, Int.cast_mul, Int.cast_neg, hc, hc',
    Fin.isValue]
  refine ⟨?_, ?_, ?_⟩
  · rw [h, neg_zero, mul_zero, add_zero, hdet']
  · rw [zero_mul, zero_add, ← h, mul_comm, hdet]
  · simp

theorem slash_eq_of_apply_eq [NeZero M] (f : ModularForm Γ₁(M) k) {γ γ' : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 0 0 : ℤ) : ZMod M) = ((γ' 0 0 : ℤ) : ZMod M)) :
    (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] γ' := by
  have hmem := mul_inv_mem_Gamma1 hγ hγ' h
  have hinv : (⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
  calc (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹ * γ') := by rw [inv_mul_cancel_right]
    _ = ((⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹)) ∣[k] γ' := SlashAction.slash_mul _ _ _ _
    _ = (⇑f : ℍ → ℂ) ∣[k] γ' := by rw [hinv]

theorem mul_apply_zero_zero {γ γ' : SL(2, ℤ)} (hγ' : γ' ∈ Gamma0 M) :
    (((γ * γ') 0 0 : ℤ) : ZMod M) = ((γ 0 0 : ℤ) : ZMod M) * ((γ' 0 0 : ℤ) : ZMod M) := by
  have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ'
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
    Int.cast_mul, hc', mul_zero, add_zero, Fin.isValue]

theorem exists_gamma0_apply_eq {d : ℕ} (hd : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hd
  have hdet : Matrix.det !![(d : ℤ), -v; (M : ℤ), u] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination huv
  refine ⟨⟨_, hdet⟩, ?_, ?_⟩
  · rw [Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  · show (((d : ℤ)) : ZMod M) = (d : ZMod M)
    rw [Int.cast_natCast]

end Slash

section Integral

variable {M : ℕ}

abbrev toC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem toC_injective : Function.Injective toC := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact (algebraMap ℚ ℂ).injective this

theorem toC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (hp : IsIntegralQExp F p) :
    toC (intSeriesC ℚ p) = qC F := by
  ext n
  rw [coeffMap_coeff, intSeriesC, qC, ← hp, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · exact map_zero _
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

theorem toC_ratio {F G : ℍ → ℂ} {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp F pf) (hg : IsIntegralQExp G pg) :
    toC (intSeriesC ℚ pf / intSeriesC ℚ pg) = qC F / qC G := by
  rw [map_div₀, toC_intSeriesC hf, toC_intSeriesC hg]

theorem qC_ne_zero_of_intSeriesC_ne_zero {G : ℍ → ℂ} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp G pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC G ≠ 0 := by
  rw [← toC_intSeriesC hg]
  exact fun h => hg0 (toC_injective (by rw [h, map_zero]))

theorem intSeriesC_ne_zero_of_qC_ne_zero {G : ℍ → ℂ} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp G pg) (hg0 : qC G ≠ 0) : intSeriesC ℚ pg ≠ 0 := by
  intro h
  apply hg0
  rw [← toC_intSeriesC hg, h, map_zero]

theorem toC_algebraMap (c : ℚ) :
    toC (algebraMap ℚ (LaurentSeries ℚ) c) = HahnSeries.C (algebraMap ℚ ℂ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem isIntegralQExp_mul {a b : ℤ} {f : ModularForm Γ₁(M) a} {g : ModularForm Γ₁(M) b}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [map_mul, hf, hg, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) f g]

theorem isIntegralQExp_add {a : ℤ} {f g : ModularForm Γ₁(M) a}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f + g)) (pf + pg) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [map_add, hf, hg, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) f g]

theorem isIntegralQExp_intSmul {a : ℤ} {f : ModularForm Γ₁(M) a} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (D : ℤ) :
    IsIntegralQExp (⇑(((D : ℤ) : ℂ) • f)) (PowerSeries.C D * pf) := by
  unfold IsIntegralQExp at hf ⊢
  rw [map_mul, PowerSeries.map_C, hf, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) _ f, PowerSeries.smul_eq_C_mul,
    eq_intCast]

theorem isIntegralQExp_coe_one : IsIntegralQExp (⇑(1 : ModularForm Γ₁(M) 0)) 1 := by
  rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one

variable (M) in

def IsIntRatio (x : LaurentSeries ℚ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm Γ₁(M) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
      x = intSeriesC ℚ pf / intSeriesC ℚ pg

theorem intSeriesC_add (p p' : PowerSeries ℤ) :
    intSeriesC ℚ (p + p') = intSeriesC ℚ p + intSeriesC ℚ p' := by
  simp [intSeriesC]

theorem intSeriesC_C (D : ℤ) : intSeriesC ℚ (PowerSeries.C D) = HahnSeries.C (D : ℚ) := by
  rw [intSeriesC, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C]

theorem intSeriesC_C_ne_zero {D : ℤ} (hD : D ≠ 0) : intSeriesC ℚ (PowerSeries.C D) ≠ 0 := by
  rw [intSeriesC_C]
  exact HahnSeries.C_ne_zero (Int.cast_ne_zero.mpr hD)

theorem isIntRatio_algebraMap (c : ℚ) : IsIntRatio M (algebraMap ℚ (LaurentSeries ℚ) c) := by
  refine ⟨0, ((c.num : ℤ) : ℂ) • (1 : ModularForm Γ₁(M) 0), ((c.den : ℤ) : ℂ) • (1 : ModularForm Γ₁(M) 0),
    PowerSeries.C c.num * 1, PowerSeries.C (c.den : ℤ) * 1,
    isIntegralQExp_intSmul isIntegralQExp_coe_one _, isIntegralQExp_intSmul isIntegralQExp_coe_one _, ?_, ?_⟩
  · rw [mul_one]; exact intSeriesC_C_ne_zero (Int.natCast_ne_zero.mpr c.den_ne_zero)
  · rw [mul_one, mul_one, intSeriesC_C, intSeriesC_C, ← map_div₀, algebraMap_laurentSeries_eq_single,
      HahnSeries.C_apply, Int.cast_natCast, Rat.num_div_den]

theorem IsIntRatio.add {x y : LaurentSeries ℚ} (hx : IsIntRatio M x) (hy : IsIntRatio M y) :
    IsIntRatio M (x + y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', rfl⟩ := hy
  refine ⟨k + k', f.mul g' + g.mul f', g.mul g', pf * pg' + pg * pf', pg * pg',
    isIntegralQExp_add (isIntegralQExp_mul hf hg') (isIntegralQExp_mul hg hf'), isIntegralQExp_mul hg hg', ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hg0 hg0'
  · rw [intSeriesC_add, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg0 hg0']

theorem IsIntRatio.mul {x y : LaurentSeries ℚ} (hx : IsIntRatio M x) (hy : IsIntRatio M y) :
    IsIntRatio M (x * y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', rfl⟩ := hy
  refine ⟨k + k', f.mul f', g.mul g', pf * pf', pg * pg', isIntegralQExp_mul hf hf', isIntegralQExp_mul hg hg', ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hg0 hg0'
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem IsIntRatio.inv {x : LaurentSeries ℚ} (hx : IsIntRatio M x) : IsIntRatio M x⁻¹ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, inv_zero, ← map_zero (algebraMap ℚ (LaurentSeries ℚ))]
    exact isIntRatio_algebraMap 0
  · exact ⟨k, g, f, pg, pf, hg, hf, hf0, by rw [inv_div]⟩

theorem isIntRatio_of_mem {x : LaurentSeries ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M))) : IsIntRatio M x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  | algebraMap c => exact isIntRatio_algebraMap c
  | add y z _ _ hy hz => exact hy.add hz
  | inv y _ hy => exact hy.inv
  | mul y z _ _ hy hz => exact hy.mul hz

end Integral

section Diamond

variable {M : ℕ} [NeZero M]

theorem slashQExpC_eq (k : ℤ) (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    slashQExpC k F γ = qC (F ∣[k] γ) := by
  rw [slashQExpC, ModularForm.SL_slash]; rfl

theorem toC_apply_generator {d : ℕ} {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (hσ : IsDiamondAut M d σ) {k : ℤ} (f g : ModularForm Γ₁(M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    toC ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        x1FunctionField M) : LaurentSeries ℚ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ) / qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
  have h := hσ.2 k f g pf pg hf hg hg0 γ hγ hγd
  rw [slashQExpC_eq, slashQExpC_eq] at h
  rw [eq_div_iff (qC_slash_ne_zero γ hγ (qC_ne_zero_of_intSeriesC_ne_zero hg hg0))]
  exact h

omit [NeZero M] in

theorem algHom_ext_of_generators
    {φ ψ : x1FunctionField M →ₐ[ℚ] x1FunctionField M}
    (h : ∀ (k : ℤ) (f g : ModularForm Γ₁(M) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      φ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
        = ψ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩) :
    φ = ψ := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M)) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      exact h k f g pf pg hf hg hg0
  | algebraMap c =>
      let j₁ : ℚ →+* x1FunctionField M := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (x1FunctionField M) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun (Subsingleton.elim ((φ : x1FunctionField M →+* x1FunctionField M).comp j₁)
        ((ψ : x1FunctionField M →+* x1FunctionField M).comp j₁)) c
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : x1FunctionField M) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : x1FunctionField M) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : x1FunctionField M) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

omit [NeZero M] in

theorem isDiamondAut_congr {d e : ℕ} (he : Nat.Coprime e M) (hde : (d : ZMod M) = (e : ZMod M))
    {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M} (hσ : IsDiamondAut M d σ) :
    IsDiamondAut M e σ := by
  refine ⟨he, ?_⟩
  intro k f g pf pg hf hg hg0 γ hγ hγe
  exact hσ.2 k f g pf pg hf hg hg0 γ hγ (hγe.trans hde.symm)

theorem eq_of_isDiamondAut {d : ℕ} {σ σ' : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (hσ : IsDiamondAut M d σ) (hσ' : IsDiamondAut M d σ') : σ = σ' := by
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0_apply_eq (M := M) hσ.1
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_of_generators
  intro k f g pf pg hf hg hg0
  apply Subtype.ext
  apply toC_injective
  change toC ((σ _ : x1FunctionField M) : LaurentSeries ℚ) = toC ((σ' _ : x1FunctionField M) : _)
  rw [toC_apply_generator hσ f g hf hg hg0 hγ hγd, toC_apply_generator hσ' f g hf hg hg0 hγ hγd]

def DiamondsExist (M : ℕ) : Prop :=
  ∀ d : ℕ, Nat.Coprime d M →
    ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ

variable (hex : DiamondsExist M)
include hex

omit [NeZero M] in
theorem isDiamondAut_diamondAut' {d : ℕ} (hd : Nat.Coprime d M) :
    IsDiamondAut M d (diamondAut M d) :=
  isDiamondAut_diamondAut (hex d hd)

theorem diamondAut_congr {d e : ℕ} (hd : Nat.Coprime d M) (he : Nat.Coprime e M)
    (hde : (d : ZMod M) = (e : ZMod M)) : diamondAut M d = diamondAut M e :=
  eq_of_isDiamondAut (isDiamondAut_congr he hde (isDiamondAut_diamondAut' hex hd))
    (isDiamondAut_diamondAut' hex he)

theorem diamondAut_one : diamondAut M 1 = 1 := by
  refine eq_of_isDiamondAut (isDiamondAut_diamondAut' hex (Nat.coprime_one_left M)) ⟨Nat.coprime_one_left M, ?_⟩
  intro k f g pf pg hf hg hg0 γ hγ hγ1
  have h1 : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
    rw [slash_eq_of_apply_eq f hγ (one_mem _) (by rw [hγ1]; simp), SlashAction.slash_one]
  have h2 : (⇑g : ℍ → ℂ) ∣[k] γ = ⇑g := by
    rw [slash_eq_of_apply_eq g hγ (one_mem _) (by rw [hγ1]; simp), SlashAction.slash_one]
  rw [slashQExpC_eq, slashQExpC_eq, h1, h2, AlgEquiv.one_apply]
  change toC (intSeriesC ℚ pf / intSeriesC ℚ pg) * qC ⇑g = qC ⇑f
  rw [toC_ratio hf hg, div_mul_cancel₀ _ (qC_ne_zero_of_intSeriesC_ne_zero hg hg0)]

theorem exists_apply_generator_eq {e : ℕ} (he : Nat.Coprime e M) {γe : SL(2, ℤ)}
    (hγe : γe ∈ Gamma0 M) (hγee : ((γe 0 0 : ℤ) : ZMod M) = (e : ZMod M))
    {k : ℤ} (f g : ModularForm Γ₁(M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ (D D' : ℤ) (f₁ g₁ : ModularForm Γ₁(M) k) (p₁ p₁' : PowerSeries ℤ)
      (hF : IsIntegralQExp (⇑(((D' : ℤ) : ℂ) • f₁)) (PowerSeries.C D' * p₁))
      (hG : IsIntegralQExp (⇑(((D : ℤ) : ℂ) • g₁)) (PowerSeries.C D * p₁'))
      (hG0 : intSeriesC ℚ (PowerSeries.C D * p₁') ≠ 0),
      D ≠ 0 ∧ D' ≠ 0 ∧
      (⇑f₁ : ℍ → ℂ) = (D : ℂ) • ((⇑f : ℍ → ℂ) ∣[k] γe) ∧
      (⇑g₁ : ℍ → ℂ) = (D' : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] γe) ∧
      diamondAut M e ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
        = ⟨intSeriesC ℚ (PowerSeries.C D' * p₁) / intSeriesC ℚ (PowerSeries.C D * p₁'),
            div_mem_qExpFunctionFieldC _ _ hF hG hG0⟩ := by
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M f hf γe hγe
  obtain ⟨D', g₁, p₁', hD', hp₁', hg₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M g hg γe hγe
  have hqf₁ : qC ⇑f₁ = (D : ℂ) • qC ((⇑f : ℍ → ℂ) ∣[k] γe) := by
    have : (⇑f₁ : ℍ → ℂ) = ⇑((D : ℂ) • diamondSlash γe hγe f) := by
      rw [hf₁, ModularForm.IsGLPos.coe_smul, coe_diamondSlash_SL]
    rw [this, qC_smul, coe_diamondSlash_SL]
  have hqg₁ : qC ⇑g₁ = (D' : ℂ) • qC ((⇑g : ℍ → ℂ) ∣[k] γe) := by
    have : (⇑g₁ : ℍ → ℂ) = ⇑((D' : ℂ) • diamondSlash γe hγe g) := by
      rw [hg₁, ModularForm.IsGLPos.coe_smul, coe_diamondSlash_SL]
    rw [this, qC_smul, coe_diamondSlash_SL]
  have hF : IsIntegralQExp (⇑(((D' : ℤ) : ℂ) • f₁)) (PowerSeries.C D' * p₁) := isIntegralQExp_intSmul hp₁ D'
  have hG : IsIntegralQExp (⇑(((D : ℤ) : ℂ) • g₁)) (PowerSeries.C D * p₁') := isIntegralQExp_intSmul hp₁' D
  have hqG : qC (⇑(((D : ℤ) : ℂ) • g₁)) = ((D : ℂ) * D') • qC ((⇑g : ℍ → ℂ) ∣[k] γe) := by
    rw [qC_smul, hqg₁, smul_smul]
  have hqF : qC (⇑(((D' : ℤ) : ℂ) • f₁)) = ((D' : ℂ) * D) • qC ((⇑f : ℍ → ℂ) ∣[k] γe) := by
    rw [qC_smul, hqf₁, smul_smul]
  have hDD : ((D : ℂ) * D') ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hD) (Int.cast_ne_zero.mpr hD')
  have hG0 : intSeriesC ℚ (PowerSeries.C D * p₁') ≠ 0 := by
    apply intSeriesC_ne_zero_of_qC_ne_zero hG
    rw [hqG, ← HahnSeries.C_mul_eq_smul]
    exact mul_ne_zero (HahnSeries.C_ne_zero hDD) (qC_slash_ne_zero γe hγe hqg)
  refine ⟨D, D', f₁, g₁, p₁, p₁', hF, hG, hG0, hD, hD', hf₁, hg₁, ?_⟩
  apply Subtype.ext
  apply toC_injective
  rw [toC_apply_generator (isDiamondAut_diamondAut' hex he) f g hf hg hg0 hγe hγee]
  change _ = toC (intSeriesC ℚ (PowerSeries.C D' * p₁) / intSeriesC ℚ (PowerSeries.C D * p₁'))
  rw [toC_ratio hF hG, hqF, hqG, mul_comm (D' : ℂ) (D : ℂ), ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul, mul_div_mul_left _ _ (HahnSeries.C_ne_zero hDD)]

theorem diamondAut_mul {d e : ℕ} (hd : Nat.Coprime d M) (he : Nat.Coprime e M) :
    diamondAut M d * diamondAut M e = diamondAut M (d * e) := by
  obtain ⟨γd, hγd, hγdd⟩ := exists_gamma0_apply_eq (M := M) hd
  obtain ⟨γe, hγe, hγee⟩ := exists_gamma0_apply_eq (M := M) he
  have hde : Nat.Coprime (d * e) M := Nat.Coprime.mul_left hd he

  have hprod : γe * γd ∈ Gamma0 M := mul_mem hγe hγd
  have hprod00 : (((γe * γd) 0 0 : ℤ) : ZMod M) = ((d * e : ℕ) : ZMod M) := by
    rw [mul_apply_zero_zero hγd, hγee, hγdd, Nat.cast_mul, mul_comm]
  apply AlgEquiv.coe_algHom_injective
  apply algHom_ext_of_generators
  intro k f g pf pg hf hg hg0
  obtain ⟨D, D', f₁, g₁, p₁, p₁', hF, hG, hG0, hD, hD', hf₁, hg₁, happ⟩ :=
    exists_apply_generator_eq hex he hγe hγee f g hf hg hg0
  apply Subtype.ext
  apply toC_injective
  change toC ((diamondAut M d (diamondAut M e _) : x1FunctionField M) : LaurentSeries ℚ)
    = toC ((diamondAut M (d * e) _ : x1FunctionField M) : LaurentSeries ℚ)
  rw [happ, toC_apply_generator (isDiamondAut_diamondAut' hex hd) _ _ hF hG hG0 hγd hγdd,
    toC_apply_generator (isDiamondAut_diamondAut' hex hde) f g hf hg hg0 hprod hprod00,
    ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, hf₁, hg₁,
    ModularForm.SL_smul_slash, ModularForm.SL_smul_slash, ModularForm.SL_smul_slash,
    ModularForm.SL_smul_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul, smul_smul, smul_smul]
  have hDD : ((D' : ℤ) : ℂ) * (D : ℂ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hD') (Int.cast_ne_zero.mpr hD)
  have hne : qC ((⇑g : ℍ → ℂ) ∣[k] (γe * γd)) ≠ 0 :=
    qC_slash_ne_zero _ hprod (qC_ne_zero_of_intSeriesC_ne_zero hg hg0)
  have e1 : qC ((((D' : ℤ) : ℂ) * (D : ℂ)) • ((⇑f : ℍ → ℂ) ∣[k] (γe * γd)))
      = (((D' : ℤ) : ℂ) * (D : ℂ)) • qC ((⇑f : ℍ → ℂ) ∣[k] (γe * γd)) := by
    rw [← coe_diamondSlash_SL _ hprod f, ← ModularForm.IsGLPos.coe_smul, qC_smul]
  have e2 : qC ((((D : ℤ) : ℂ) * (D' : ℂ)) • ((⇑g : ℍ → ℂ) ∣[k] (γe * γd)))
      = (((D' : ℤ) : ℂ) * (D : ℂ)) • qC ((⇑g : ℍ → ℂ) ∣[k] (γe * γd)) := by
    rw [← coe_diamondSlash_SL _ hprod g, ← ModularForm.IsGLPos.coe_smul, qC_smul, mul_comm]
  rw [e1, e2, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    mul_div_mul_left _ _ (HahnSeries.C_ne_zero hDD)]

end Diamond

section Products

variable {M : ℕ} {k : ℤ} {ι : Type*}

def listProd (F : ι → ModularForm Γ₁(M) k) : (l : List ι) → ModularForm Γ₁(M) ((l.length : ℤ) * k)
  | [] => (1 : ModularForm Γ₁(M) 0).mcast (by simp)
  | i :: l => ((F i).mul (listProd F l)).mcast (by rw [List.length_cons]; push_cast; ring)

@[scoped simp] theorem coe_listProd (F : ι → ModularForm Γ₁(M) k) (l : List ι) :
    (⇑(listProd F l) : ℍ → ℂ) = (l.map fun i => (⇑(F i) : ℍ → ℂ)).prod := by
  induction l with
  | nil => rw [listProd, ModularForm.coe_mcast, ModularForm.one_coe_eq_one, List.map_nil, List.prod_nil]
  | cons i l ih => rw [listProd, ModularForm.coe_mcast, ModularForm.coe_mul, ih, List.map_cons,
      List.prod_cons]

theorem qC_listProd (F : ι → ModularForm Γ₁(M) k) (l : List ι) :
    qC (⇑(listProd F l)) = (l.map fun i => qC ⇑(F i)).prod := by
  induction l with
  | nil => rw [listProd, ModularForm.coe_mcast, qC_coe_one, List.map_nil, List.prod_nil]
  | cons i l ih => rw [listProd, ModularForm.coe_mcast, qC_coe_mul, ih, List.map_cons, List.prod_cons]

theorem isIntegralQExp_listProd (F : ι → ModularForm Γ₁(M) k) {p : ι → PowerSeries ℤ}
    (hF : ∀ i, IsIntegralQExp (F i) (p i)) (l : List ι) :
    IsIntegralQExp (⇑(listProd F l)) (l.map p).prod := by
  induction l with
  | nil => rw [listProd, ModularForm.coe_mcast, List.map_nil, List.prod_nil]; exact isIntegralQExp_coe_one
  | cons i l ih =>
      rw [listProd, ModularForm.coe_mcast, List.map_cons, List.prod_cons]
      exact isIntegralQExp_mul (hF i) ih

theorem slash_listProd (F : ι → ModularForm Γ₁(M) k) (l : List ι) (γ : SL(2, ℤ)) :
    (⇑(listProd F l) : ℍ → ℂ) ∣[(l.length : ℤ) * k] γ = (l.map fun i => (⇑(F i) : ℍ → ℂ) ∣[k] γ).prod := by
  induction l with
  | nil =>
      rw [coe_listProd, List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, List.length_nil,
        Nat.cast_zero, zero_mul]
      exact ModularForm.is_invariant_one γ
  | cons i l ih =>
      have hw : (((i :: l).length : ℕ) : ℤ) * k = k + (l.length : ℤ) * k := by
        rw [List.length_cons]; push_cast; ring
      rw [coe_listProd, List.map_cons, List.prod_cons, hw, ModularForm.mul_slash_SL2, ← coe_listProd, ih,
        List.map_cons, List.prod_cons]

theorem smul_eq_const_mul (c : ℂ) (F : ℍ → ℂ) : c • F = (fun _ => c) * F := by
  funext τ; simp [Pi.smul_apply, smul_eq_mul]

end Products

section Groups

variable (M₀ t : ℕ)

abbrev Gam : Subgroup SL(2, ℤ) := Gamma1 M₀ ⊓ Gamma0 t

abbrev Ker : Subgroup (ZMod (M₀ * t))ˣ := (ZMod.unitsMap (dvd_mul_right M₀ t)).ker

def kval (u : Ker M₀ t) : ℕ := ((u : (ZMod (M₀ * t))ˣ) : ZMod (M₀ * t)).val

variable {M₀ t}

theorem natCast_kval [NeZero (M₀ * t)] (u : Ker M₀ t) :
    ((kval M₀ t u : ℕ) : ZMod (M₀ * t)) = ((u : (ZMod (M₀ * t))ˣ) : ZMod (M₀ * t)) :=
  ZMod.natCast_zmod_val _

theorem mem_ker_iff [NeZero (M₀ * t)] (u : (ZMod (M₀ * t))ˣ) :
    u ∈ Ker M₀ t ↔ (((u : ZMod (M₀ * t)).val : ℕ) : ZMod M₀) = 1 := by
  rw [MonoidHom.mem_ker, ZMod.unitsMap_def, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe,
    ZMod.castHom_apply, Units.val_one, ZMod.cast_eq_val]

theorem kval_coprime (u : Ker M₀ t) : (kval M₀ t u).Coprime (M₀ * t) :=
  ZMod.val_coe_unit_coprime _

theorem natCast_kval_M₀ [NeZero (M₀ * t)] (u : Ker M₀ t) : ((kval M₀ t u : ℕ) : ZMod M₀) = 1 :=
  (mem_ker_iff _).mp u.2

theorem Gamma0_le_of_dvd {N N' : ℕ} (h : N ∣ N') : Gamma0 N' ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod N)) hA
  rwa [map_intCast, map_zero] at this

variable (M₀ t) in
theorem Gamma1_mul_le : Gamma1 (M₀ * t) ≤ Gam M₀ t :=
  le_inf (Gamma1_le_of_dvd (dvd_mul_right M₀ t))
    ((Gamma1_in_Gamma0 _).trans (Gamma0_le_of_dvd (dvd_mul_left t M₀)))

variable (M₀ t) in
theorem map_Gamma1_mul_le :
    (Γ₁(M₀ * t)) ≤ ((Gam M₀ t : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma1_mul_le M₀ t)

variable (M₀ t) in

theorem x1x0_le_x1 : x1x0FunctionFieldC ℚ M₀ t ≤ x1FunctionField (M₀ * t) :=
  qExpFunctionFieldC_mono ℚ (Gamma1_mul_le M₀ t)

theorem gam_le_Gamma0 (hM₀t : Nat.Coprime M₀ t) : Gam M₀ t ≤ Gamma0 (M₀ * t) := by
  intro γ hγ
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
  have h1' : ((γ 1 0 : ℤ) : ZMod M₀) = 0 := ((Gamma1_mem M₀ γ).mp h1).2.2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1'
  push_cast
  exact (Nat.isCoprime_iff_coprime.mpr hM₀t).mul_dvd h1' h0

def unitOf {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M₀ * t)) : (ZMod (M₀ * t))ˣ :=
  Units.mkOfMulEqOne _ _ (apply_zero_zero_mul_apply_one_one hγ)

theorem coe_unitOf {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M₀ * t)) :
    ((unitOf hγ : (ZMod (M₀ * t))ˣ) : ZMod (M₀ * t)) = ((γ 0 0 : ℤ) : ZMod (M₀ * t)) := rfl

theorem unitOf_mem [NeZero (M₀ * t)] {γ : SL(2, ℤ)} (hγ : γ ∈ Gam M₀ t) (hγ0 : γ ∈ Gamma0 (M₀ * t)) :
    unitOf hγ0 ∈ Ker M₀ t := by
  rw [mem_ker_iff, coe_unitOf, ← ZMod.cast_eq_val, ZMod.cast_intCast (dvd_mul_right M₀ t)]
  exact ((Gamma1_mem M₀ γ).mp (Subgroup.mem_inf.mp hγ).1).1

theorem exists_rep [NeZero (M₀ * t)] (u : Ker M₀ t) :
    ∃ γ : SL(2, ℤ), γ ∈ Gam M₀ t ∧ γ ∈ Gamma0 (M₀ * t) ∧
      ((γ 0 0 : ℤ) : ZMod (M₀ * t)) = (kval M₀ t u : ZMod (M₀ * t)) := by
  obtain ⟨γ, hγ0, hγd⟩ := exists_gamma0_apply_eq (M := M₀ * t) (kval_coprime u)
  refine ⟨γ, ?_, hγ0, hγd⟩
  have hM₀ : γ ∈ Gamma0 M₀ := Gamma0_le_of_dvd (dvd_mul_right M₀ t) hγ0
  have h00 : ((γ 0 0 : ℤ) : ZMod M₀) = 1 := by
    have := congrArg (ZMod.castHom (dvd_mul_right M₀ t) (ZMod M₀)) hγd
    rw [map_intCast, map_natCast, natCast_kval_M₀] at this
    exact this
  refine Subgroup.mem_inf.mpr ⟨?_, Gamma0_le_of_dvd (dvd_mul_left t M₀) hγ0⟩
  rw [Gamma1_mem]
  refine ⟨h00, ?_, Gamma0_mem.mp hM₀⟩
  have hdet := apply_zero_zero_mul_apply_one_one hM₀
  rwa [h00, one_mul] at hdet

def rep [NeZero (M₀ * t)] (u : Ker M₀ t) : SL(2, ℤ) := (exists_rep u).choose

theorem rep_mem [NeZero (M₀ * t)] (u : Ker M₀ t) : rep u ∈ Gam M₀ t := (exists_rep u).choose_spec.1

theorem rep_mem_Gamma0 [NeZero (M₀ * t)] (u : Ker M₀ t) : rep u ∈ Gamma0 (M₀ * t) :=
  (exists_rep u).choose_spec.2.1

theorem rep_apply [NeZero (M₀ * t)] (u : Ker M₀ t) :
    (((rep u) 0 0 : ℤ) : ZMod (M₀ * t)) = ((u : (ZMod (M₀ * t))ˣ) : ZMod (M₀ * t)) := by
  rw [← natCast_kval]
  exact (exists_rep u).choose_spec.2.2

theorem slash_rep_one [NeZero (M₀ * t)] {k : ℤ} (g : ModularForm Γ₁(M₀ * t) k) :
    (⇑g : ℍ → ℂ) ∣[k] rep (1 : Ker M₀ t) = ⇑g := by
  rw [slash_eq_of_apply_eq g (rep_mem_Gamma0 1) (one_mem _) ?_, SlashAction.slash_one]
  rw [rep_apply]
  simp

theorem rep_mul_apply [NeZero (M₀ * t)] (u : Ker M₀ t) {γ : SL(2, ℤ)} (hγ : γ ∈ Gam M₀ t)
    (hγ0 : γ ∈ Gamma0 (M₀ * t)) :
    ((((rep u) * γ) 0 0 : ℤ) : ZMod (M₀ * t))
      = (((rep (u * ⟨unitOf hγ0, unitOf_mem hγ hγ0⟩)) 0 0 : ℤ) : ZMod (M₀ * t)) := by
  rw [mul_apply_zero_zero hγ0, rep_apply, rep_apply]
  rfl

variable [NeZero (M₀ * t)] (hex : DiamondsExist (M₀ * t))
include hex

variable (M₀ t) in

def delta : Ker M₀ t →* (x1FunctionField (M₀ * t) ≃ₐ[ℚ] x1FunctionField (M₀ * t)) :=
  MonoidHom.mk' (fun u => diamondAut (M₀ * t) (kval M₀ t u)) (fun u v => by
    show diamondAut (M₀ * t) (kval M₀ t (u * v))
      = diamondAut (M₀ * t) (kval M₀ t u) * diamondAut (M₀ * t) (kval M₀ t v)
    rw [diamondAut_mul hex (kval_coprime u) (kval_coprime v)]
    apply diamondAut_congr hex (kval_coprime _) (Nat.Coprime.mul_left (kval_coprime u) (kval_coprime v))
    rw [natCast_kval, Nat.cast_mul, natCast_kval, natCast_kval]
    rfl)

theorem delta_apply (u : Ker M₀ t) : delta M₀ t hex u = diamondAut (M₀ * t) (kval M₀ t u) := rfl

end Groups

section Fix

variable {M₀ t : ℕ} [NeZero (M₀ * t)] (hex : DiamondsExist (M₀ * t))
include hex

theorem diamondAut_apply_eq_self (u : Ker M₀ t) (x : x1FunctionField (M₀ * t))
    (hx : (x : LaurentSeries ℚ) ∈ x1x0FunctionFieldC ℚ M₀ t) :
    diamondAut (M₀ * t) (kval M₀ t u) x = x := by
  obtain ⟨x, hxF⟩ := x
  have hle : x1x0FunctionFieldC ℚ M₀ t ≤ x1FunctionField (M₀ * t) := x1x0_le_x1 M₀ t
  have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gam M₀ t)) := hx
  suffices h : diamondAut (M₀ * t) (kval M₀ t u) ⟨x, hle hx'⟩ = ⟨x, hle hx'⟩ by exact h
  clear hx hxF
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      have hf' : IsIntegralQExp (⇑(restrictForm (map_Gamma1_mul_le M₀ t) f)) pf := hf
      have hg' : IsIntegralQExp (⇑(restrictForm (map_Gamma1_mul_le M₀ t) g)) pg := hg
      have key := toC_apply_generator (isDiamondAut_diamondAut' hex (kval_coprime u))
        (restrictForm (map_Gamma1_mul_le M₀ t) f) (restrictForm (map_Gamma1_mul_le M₀ t) g)
        hf' hg' hg0 (rep_mem_Gamma0 u) ((rep_apply u).trans (natCast_kval u).symm)
      apply Subtype.ext
      apply toC_injective
      change toC ((diamondAut (M₀ * t) (kval M₀ t u) _ : x1FunctionField (M₀ * t)) : LaurentSeries ℚ) = _
      rw [key, coe_restrictForm, coe_restrictForm, toC_ratio hf hg]
      have hinvf : (⇑f : ℍ → ℂ) ∣[k] rep u = ⇑f := by
        rw [ModularForm.SL_slash]
        exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (rep_mem u))
      have hinvg : (⇑g : ℍ → ℂ) ∣[k] rep u = ⇑g := by
        rw [ModularForm.SL_slash]
        exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (rep_mem u))
      rw [hinvf, hinvg]
  | algebraMap c =>
      let j₁ : ℚ →+* x1FunctionField (M₀ * t) := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
        (x1FunctionField (M₀ * t)) (fun c => IntermediateField.algebraMap_mem _ c)
      exact RingHom.congr_fun (Subsingleton.elim
        ((diamondAut (M₀ * t) (kval M₀ t u) : x1FunctionField (M₀ * t) →+* x1FunctionField (M₀ * t)).comp j₁)
        j₁) c
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, hle (add_mem hy hz)⟩ : x1FunctionField (M₀ * t)) = ⟨y, hle hy⟩ + ⟨z, hle hz⟩ := rfl
      rw [this, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, hle (inv_mem hy)⟩ : x1FunctionField (M₀ * t)) = ⟨y, hle hy⟩⁻¹ := rfl
      rw [this, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, hle (mul_mem hy hz)⟩ : x1FunctionField (M₀ * t)) = ⟨y, hle hy⟩ * ⟨z, hle hz⟩ := rfl
      rw [this, map_mul, ihy, ihz]

end Fix

section Hard

variable {M₀ t : ℕ} [NeZero M₀] [NeZero t]

scoped instance instNeZeroMul' : NeZero (M₀ * t) := ⟨mul_ne_zero (NeZero.ne M₀) (NeZero.ne t)⟩

variable (M₀ t) in

def Lst : List (Ker M₀ t) := (Finset.univ : Finset (Ker M₀ t)).toList

variable (M₀ t) in

def Lst' : List (Ker M₀ t) := @List.erase _ instBEqOfDecidableEq (Lst M₀ t) 1

theorem one_mem_Lst : (1 : Ker M₀ t) ∈ Lst M₀ t := Finset.mem_toList.mpr (Finset.mem_univ _)

theorem weight_eq (k : ℤ) : k + ((Lst' M₀ t).length : ℤ) * k = ((Lst M₀ t).length : ℤ) * k := by
  rw [Lst', @List.length_erase_of_mem (Ker M₀ t) instBEqOfDecidableEq inferInstance (1 : Ker M₀ t)
      (Lst M₀ t) one_mem_Lst, Nat.cast_sub (List.length_pos_of_mem one_mem_Lst)]
  push_cast
  ring

variable (hM₀t : Nat.Coprime M₀ t)
include hM₀t

omit hM₀t in

theorem isCusp_transfer {c : OnePoint ℝ}
    (hc : IsCusp c ((Gam M₀ t : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) : IsCusp c Γ₁(M₀ * t) :=
  (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)

theorem prod_slash_eq {k : ℤ} (g : ModularForm Γ₁(M₀ * t) k) (D : Ker M₀ t → ℤ)
    (gg : Ker M₀ t → ModularForm Γ₁(M₀ * t) k)
    (hgg : ∀ u, (⇑(gg u) : ℍ → ℂ) = ((D u : ℤ) : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] rep u))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gam M₀ t) :
    (⇑(listProd gg (Lst M₀ t)) : ℍ → ℂ) ∣[((Lst M₀ t).length : ℤ) * k] γ
      = ⇑(listProd gg (Lst M₀ t)) := by
  have hγ0 : γ ∈ Gamma0 (M₀ * t) := gam_le_Gamma0 hM₀t hγ
  let e : Ker M₀ t := ⟨unitOf hγ0, unitOf_mem hγ hγ0⟩
  have h1 : ∀ u : Ker M₀ t, (⇑(gg u) : ℍ → ℂ) ∣[k] γ
      = (fun _ => ((D u : ℤ) : ℂ)) * ((⇑g : ℍ → ℂ) ∣[k] rep (u * e)) := by
    intro u
    rw [hgg u, ModularForm.SL_smul_slash, ← SlashAction.slash_mul,
      slash_eq_of_apply_eq g (mul_mem (rep_mem_Gamma0 u) hγ0) (rep_mem_Gamma0 (u * e))
        (rep_mul_apply u hγ hγ0), smul_eq_const_mul]
  have h2 : ∀ u : Ker M₀ t, (⇑(gg u) : ℍ → ℂ)
      = (fun _ => ((D u : ℤ) : ℂ)) * ((⇑g : ℍ → ℂ) ∣[k] rep u) := fun u => by
    rw [hgg u, smul_eq_const_mul]
  rw [slash_listProd, coe_listProd, List.map_congr_left (fun u _ => h1 u),
    List.map_congr_left (fun u _ => h2 u), List.prod_map_mul, List.prod_map_mul]
  congr 1
  rw [Lst, Finset.prod_map_toList, Finset.prod_map_toList]
  exact Fintype.prod_equiv (Equiv.mulRight e) _ _ (fun u => rfl)

omit hM₀t in

theorem qC_gg {k : ℤ} (g : ModularForm Γ₁(M₀ * t) k) (D : Ker M₀ t → ℤ)
    (gg : Ker M₀ t → ModularForm Γ₁(M₀ * t) k)
    (hgg : ∀ u, (⇑(gg u) : ℍ → ℂ) = ((D u : ℤ) : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] rep u)) (u : Ker M₀ t) :
    qC ⇑(gg u) = HahnSeries.C ((D u : ℤ) : ℂ) * qC ((⇑g : ℍ → ℂ) ∣[k] rep u) := by
  have : (⇑(gg u) : ℍ → ℂ) = ⇑(((D u : ℤ) : ℂ) • diamondSlash (rep u) (rep_mem_Gamma0 u) g) := by
    rw [hgg u, ModularForm.IsGLPos.coe_smul, coe_diamondSlash_SL]
  rw [this, qC_smul, coe_diamondSlash_SL, HahnSeries.C_mul_eq_smul]

theorem smul_mul_prod_slash_eq {k : ℤ} (f g : ModularForm Γ₁(M₀ * t) k) (y : LaurentSeries ℂ)
    (hcross : ∀ γ : SL(2, ℤ), γ ∈ Gam M₀ t →
      y * qC ((⇑g : ℍ → ℂ) ∣[k] γ) = qC ((⇑f : ℍ → ℂ) ∣[k] γ))
    (D : Ker M₀ t → ℤ) (gg : Ker M₀ t → ModularForm Γ₁(M₀ * t) k)
    (hgg : ∀ u, (⇑(gg u) : ℍ → ℂ) = ((D u : ℤ) : ℂ) • ((⇑g : ℍ → ℂ) ∣[k] rep u))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gam M₀ t) :
    (⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))) : ℍ → ℂ) ∣[k + ((Lst' M₀ t).length : ℤ) * k] γ
      = ⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))) := by
  have hγ0 : γ ∈ Gamma0 (M₀ * t) := gam_le_Gamma0 hM₀t hγ

  have hfun : (⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))) : ℍ → ℂ)
        ∣[k + ((Lst' M₀ t).length : ℤ) * k] γ
      = ⇑(((D 1 : ℤ) : ℂ) • ((diamondSlash γ hγ0 f).mul
          (listProd (fun u => diamondSlash γ hγ0 (gg u)) (Lst' M₀ t)))) := by
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.coe_mul, ModularForm.SL_smul_slash,
      ModularForm.mul_slash_SL2, slash_listProd, ModularForm.IsGLPos.coe_smul, ModularForm.coe_mul,
      coe_diamondSlash_SL, coe_listProd]
    simp only [coe_diamondSlash_SL]
  rw [hfun]
  apply coe_eq_of_qC_eq
  rw [qC_smul, qC_coe_mul, qC_listProd, coe_diamondSlash_SL, qC_smul, qC_coe_mul, qC_listProd]
  simp only [coe_diamondSlash_SL]

  have hg1 : qC ((⇑(gg 1) : ℍ → ℂ) ∣[k] γ)
      = HahnSeries.C ((D 1 : ℤ) : ℂ) * qC ((⇑g : ℍ → ℂ) ∣[k] γ) := by
    rw [hgg 1, slash_rep_one, ModularForm.SL_smul_slash, ← coe_diamondSlash_SL γ hγ0 g,
      ← ModularForm.IsGLPos.coe_smul, qC_smul, HahnSeries.C_mul_eq_smul]
  have hgg1 : qC (⇑(gg 1) : ℍ → ℂ) = HahnSeries.C ((D 1 : ℤ) : ℂ) * qC (⇑g : ℍ → ℂ) := by
    rw [qC_gg g D gg hgg 1, slash_rep_one]
  have hfg : y * qC (⇑g : ℍ → ℂ) = qC (⇑f : ℍ → ℂ) := by
    have := hcross 1 (one_mem _)
    rwa [SlashAction.slash_one, SlashAction.slash_one] at this
  have hA : ((Lst M₀ t).map fun u => qC ((⇑(gg u) : ℍ → ℂ) ∣[k] γ)).prod
      = ((Lst M₀ t).map fun u => qC (⇑(gg u) : ℍ → ℂ)).prod := by
    have h := prod_slash_eq hM₀t g D gg hgg hγ
    rw [slash_listProd] at h
    have h' : (⇑(listProd (fun u => diamondSlash γ hγ0 (gg u)) (Lst M₀ t)) : ℍ → ℂ)
        = ⇑(listProd gg (Lst M₀ t)) := by
      rw [← h, coe_listProd]
      simp only [coe_diamondSlash_SL]
    have h'' := congrArg qC h'
    rw [qC_listProd, qC_listProd] at h''
    simpa only [coe_diamondSlash_SL] using h''
  have hA' : qC ((⇑(gg 1) : ℍ → ℂ) ∣[k] γ) * ((Lst' M₀ t).map fun u => qC ((⇑(gg u) : ℍ → ℂ) ∣[k] γ)).prod
      = qC (⇑(gg 1) : ℍ → ℂ) * ((Lst' M₀ t).map fun u => qC (⇑(gg u) : ℍ → ℂ)).prod := by
    have e1 := List.prod_map_erase (l := Lst M₀ t) (fun u => qC ((⇑(gg u) : ℍ → ℂ) ∣[k] γ)) one_mem_Lst
    have e2 := List.prod_map_erase (l := Lst M₀ t) (fun u => qC (⇑(gg u) : ℍ → ℂ)) one_mem_Lst
    exact e1.trans (hA.trans e2.symm)

  change ((D 1 : ℤ) : ℂ) • (qC ((⇑f : ℍ → ℂ) ∣[k] γ)
        * ((Lst' M₀ t).map fun u => qC ((⇑(gg u) : ℍ → ℂ) ∣[k] γ)).prod)
      = ((D 1 : ℤ) : ℂ) • (qC (⇑f : ℍ → ℂ) * ((Lst' M₀ t).map fun u => qC (⇑(gg u) : ℍ → ℂ)).prod)
  rw [← hcross γ hγ, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul]
  rw [show HahnSeries.C ((D 1 : ℤ) : ℂ) * (y * qC ((⇑g : ℍ → ℂ) ∣[k] γ)
        * ((Lst' M₀ t).map fun u => qC ((⇑(gg u) : ℍ → ℂ) ∣[k] γ)).prod)
      = y * ((HahnSeries.C ((D 1 : ℤ) : ℂ) * qC ((⇑g : ℍ → ℂ) ∣[k] γ))
        * ((Lst' M₀ t).map fun u => qC ((⇑(gg u) : ℍ → ℂ) ∣[k] γ)).prod) by ring,
    ← hg1, hA', hgg1,
    show y * (HahnSeries.C ((D 1 : ℤ) : ℂ) * qC (⇑g : ℍ → ℂ)
        * ((Lst' M₀ t).map fun u => qC (⇑(gg u) : ℍ → ℂ)).prod)
      = HahnSeries.C ((D 1 : ℤ) : ℂ) * ((y * qC (⇑g : ℍ → ℂ))
        * ((Lst' M₀ t).map fun u => qC (⇑(gg u) : ℍ → ℂ)).prod) by ring,
    hfg]

theorem mem_x1x0_of_forall_diamondAut_eq (hex : DiamondsExist (M₀ * t))
    (x : x1FunctionField (M₀ * t))
    (hx : ∀ u : Ker M₀ t, diamondAut (M₀ * t) (kval M₀ t u) x = x) :
    (x : LaurentSeries ℚ) ∈ x1x0FunctionFieldC ℚ M₀ t := by

  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hxeq⟩ := isIntRatio_of_mem x.2
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  have hy : toC (x : LaurentSeries ℚ) = qC ⇑f / qC ⇑g := by rw [hxeq, toC_ratio hf hg]

  have hcross : ∀ γ : SL(2, ℤ), γ ∈ Gam M₀ t →
      toC (x : LaurentSeries ℚ) * qC ((⇑g : ℍ → ℂ) ∣[k] γ) = qC ((⇑f : ℍ → ℂ) ∣[k] γ) := by
    intro γ hγ
    have hγ0 : γ ∈ Gamma0 (M₀ * t) := gam_le_Gamma0 hM₀t hγ
    let u : Ker M₀ t := ⟨unitOf hγ0, unitOf_mem hγ hγ0⟩
    have hγu : ((γ 0 0 : ℤ) : ZMod (M₀ * t)) = (kval M₀ t u : ZMod (M₀ * t)) := by
      rw [natCast_kval]; rfl
    have h1 := toC_apply_generator (isDiamondAut_diamondAut' hex (kval_coprime u)) f g hf hg hg0 hγ0 hγu
    have hxgen : (⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        x1FunctionField (M₀ * t)) = x := (Subtype.ext hxeq).symm
    rw [hxgen, hx u] at h1
    rw [h1, div_mul_cancel₀ _ (qC_slash_ne_zero γ hγ0 hqg)]

  choose D gg pp hD hpp hgg using fun u : Ker M₀ t =>
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M₀ * t) g hg (rep u) (rep_mem_Gamma0 u)

  have hN0 : qC (⇑(listProd gg (Lst M₀ t)) : ℍ → ℂ) ≠ 0 := by
    rw [qC_listProd]
    apply List.prod_ne_zero
    intro h0
    obtain ⟨u, -, hu⟩ := List.mem_map.mp h0
    rw [qC_gg g D gg hgg u] at hu
    exact mul_ne_zero (HahnSeries.C_ne_zero (Int.cast_ne_zero.mpr (hD u)))
      (qC_slash_ne_zero _ (rep_mem_Gamma0 u) hqg) hu
  have hyN : toC (x : LaurentSeries ℚ) * qC (⇑(listProd gg (Lst M₀ t)) : ℍ → ℂ)
      = qC (⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))) : ℍ → ℂ) := by
    have hfg : toC (x : LaurentSeries ℚ) * qC (⇑g : ℍ → ℂ) = qC (⇑f : ℍ → ℂ) := by
      rw [hy, div_mul_cancel₀ _ hqg]
    rw [qC_smul, qC_coe_mul, qC_listProd, qC_listProd, Lst',
      ← List.prod_map_erase (fun u => qC (⇑(gg u) : ℍ → ℂ)) one_mem_Lst, qC_gg g D gg hgg 1,
      slash_rep_one, ← HahnSeries.C_mul_eq_smul, ← hfg]
    ring

  let G₂ : ModularForm ((Gam M₀ t : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      (((Lst M₀ t).length : ℤ) * k) :=
    { toFun := ⇑(listProd gg (Lst M₀ t))
      slash_action_eq' := fun A hA => by
        obtain ⟨γ, hγ, rfl⟩ := hA
        show (⇑(listProd gg (Lst M₀ t)) : ℍ → ℂ) ∣[((Lst M₀ t).length : ℤ) * k] (γ : GL (Fin 2) ℝ) = _
        rw [← ModularForm.SL_slash]
        exact prod_slash_eq hM₀t g D gg hgg hγ
      holo' := (listProd gg (Lst M₀ t)).holo'
      bdd_at_cusps' := fun hc => (listProd gg (Lst M₀ t)).bdd_at_cusps' (isCusp_transfer hc) }
  let B₂ : ModularForm ((Gam M₀ t : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      (((Lst M₀ t).length : ℤ) * k) :=
    { toFun := ⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t))))
      slash_action_eq' := fun A hA => by
        obtain ⟨γ, hγ, rfl⟩ := hA
        show (⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))) : ℍ → ℂ)
          ∣[((Lst M₀ t).length : ℤ) * k] (γ : GL (Fin 2) ℝ) = _
        rw [← ModularForm.SL_slash, ← weight_eq]
        exact smul_mul_prod_slash_eq hM₀t f g _ hcross D gg hgg hγ
      holo' := (((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))).holo'
      bdd_at_cusps' := fun hc => by
        rw [← weight_eq]
        exact (((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))).bdd_at_cusps'
          (isCusp_transfer hc) }
  have hG₂ : IsIntegralQExp (⇑G₂) ((Lst M₀ t).map pp).prod := isIntegralQExp_listProd gg hpp _
  have hB₂ : IsIntegralQExp (⇑B₂) (PowerSeries.C (D 1) * (pf * ((Lst' M₀ t).map pp).prod)) :=
    isIntegralQExp_intSmul (isIntegralQExp_mul hf (isIntegralQExp_listProd gg hpp _)) (D 1)
  have hG0 : intSeriesC ℚ ((Lst M₀ t).map pp).prod ≠ 0 := intSeriesC_ne_zero_of_qC_ne_zero hG₂ hN0
  have hmem := div_mem_qExpFunctionFieldC B₂ G₂ hB₂ hG₂ hG0

  have hxBG : (x : LaurentSeries ℚ)
      = intSeriesC ℚ (PowerSeries.C (D 1) * (pf * ((Lst' M₀ t).map pp).prod))
        / intSeriesC ℚ ((Lst M₀ t).map pp).prod := by
    apply toC_injective
    rw [toC_ratio hB₂ hG₂]
    change toC (x : LaurentSeries ℚ) = qC (⇑(((D 1 : ℤ) : ℂ) • (f.mul (listProd gg (Lst' M₀ t)))) : ℍ → ℂ)
      / qC (⇑(listProd gg (Lst M₀ t)) : ℍ → ℂ)
    rw [← hyN, mul_div_cancel_right₀ _ hN0]
  rw [hxBG]
  exact hmem

end Hard

section Assembly

variable (M₀ t : ℕ) [NeZero M₀] [NeZero t] (hM₀t : Nat.Coprime M₀ t)
  (hex : DiamondsExist (M₀ * t))
include hM₀t hex

theorem galois (x : x1FunctionField (M₀ * t)) :
    (x : LaurentSeries ℚ) ∈ x1x0FunctionFieldC ℚ M₀ t ↔ ∀ u : Ker M₀ t, delta M₀ t hex u x = x :=
  ⟨fun hx u => diamondAut_apply_eq_self hex u x hx,
    fun hx => mem_x1x0_of_forall_diamondAut_eq hM₀t hex x hx⟩

end Assembly

end X1DiamondGalois
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff.X1DiamondGalois"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff.X1DiamondGalois"

open ModularCurve in
theorem solution
    (M₀ t : ℕ) [NeZero M₀] [NeZero t] (hM₀t : Nat.Coprime M₀ t)
    (hdia : ∀ d : ℕ, Nat.Coprime d (M₀ * t) →
      ∃ σ : ModularCurve.x1FunctionField (M₀ * t) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * t),
        ModularCurve.IsDiamondAut (M₀ * t) d σ) :
    ∃ δ : (ZMod.unitsMap (dvd_mul_right M₀ t)).ker →*
        (ModularCurve.x1FunctionField (M₀ * t) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * t)),
      (∀ u : (ZMod.unitsMap (dvd_mul_right M₀ t)).ker,
          δ u = ModularCurve.diamondAut (M₀ * t)
            (((u : (ZMod (M₀ * t))ˣ) : ZMod (M₀ * t)).val)) ∧
      ∀ x : ModularCurve.x1FunctionField (M₀ * t),
        (x : LaurentSeries ℚ) ∈ ModularCurve.x1x0FunctionFieldC ℚ M₀ t ↔
          ∀ u : (ZMod.unitsMap (dvd_mul_right M₀ t)).ker, δ u x = x :=
  ⟨X1DiamondGalois.delta M₀ t hdia, fun _ => rfl, X1DiamondGalois.galois M₀ t hM₀t hdia⟩

end S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
end P2MW
export P2MW.S_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff (solution)
