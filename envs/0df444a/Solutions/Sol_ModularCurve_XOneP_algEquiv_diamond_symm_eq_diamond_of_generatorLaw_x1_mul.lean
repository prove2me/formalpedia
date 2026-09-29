-- Prove2me | solution 1 for ModularCurve.XOneP.algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/929a2e6a-a062-5027-b436-99e66f0a93da

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries
open scoped MatrixGroups ModularForm Manifold

namespace CONJ5

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

theorem qC_add {a : ℤ} (f g : ModularForm Γ₁(M) a) :
    qC (⇑(f + g)) = qC ⇑f + qC ⇑g := by
  rw [ModularForm.coe_add, qC, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) f g,
    map_add]
  rfl

theorem qC_neg {a : ℤ} (f : ModularForm Γ₁(M) a) : qC (⇑(-f)) = -qC ⇑f := by
  rw [ModularForm.coe_neg, qC, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods M) f,
    map_neg]
  rfl

theorem qC_smul {a : ℤ} (c : ℂ) (f : ModularForm Γ₁(M) a) : qC (⇑(c • f)) = c • qC ⇑f := by
  rw [ModularForm.IsGLPos.coe_smul, qC,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f, qC,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by
  rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by
  rw [qC, qExpansion_one, map_one]

theorem qC_coe_zero {a : ℤ} : qC (⇑(0 : ModularForm Γ₁(M) a)) = 0 := by
  rw [ModularForm.coe_zero]; exact qC_zero

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

theorem slash_inv_slash (F : ℍ → ℂ) (γ : SL(2, ℤ)) : (F ∣[k] γ⁻¹) ∣[k] γ = F := by
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

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

theorem mul_inv_mem_Gamma1 {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 0 0 : ℤ) : ZMod M) = ((γ' 0 0 : ℤ) : ZMod M)) : γ * γ'⁻¹ ∈ Gamma1 M := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ'
  have hdet : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) h1
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  have hdet' : ((γ' 0 0 : ℤ) : ZMod M) * ((γ' 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : (γ' 0 0 : ℤ) * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by
      have := γ'.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) h1
    push_cast at this
    rw [hc', mul_zero, sub_zero] at this
    exact this
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

end Slash

section Rational

open ModularCurve IntermediateField

variable (M : ℕ) [NeZero M]

abbrev toC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

omit [NeZero M] in
theorem toC_injective : Function.Injective toC := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact (algebraMap ℚ ℂ).injective this

variable {M}

omit [NeZero M] in

theorem toC_intSeriesC {k : ℤ} {f : ModularForm Γ₁(M) k} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) : toC (intSeriesC ℚ p) = qC ⇑f := by
  ext n
  rw [coeffMap_coeff, intSeriesC, qC, ← hp, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · exact map_zero _
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

omit [NeZero M] in
theorem toC_ratio {k : ℤ} {f g : ModularForm Γ₁(M) k} {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    toC (intSeriesC ℚ pf / intSeriesC ℚ pg) = qC ⇑f / qC ⇑g := by
  rw [map_div₀, toC_intSeriesC hf, toC_intSeriesC hg]

omit [NeZero M] in
theorem qC_ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm Γ₁(M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC ⇑g ≠ 0 := by
  rw [← toC_intSeriesC hg]
  exact fun h => hg0 (toC_injective (by rw [h, map_zero]))

omit [NeZero M] in
theorem toC_algebraMap (c : ℚ) :
    toC (algebraMap ℚ (LaurentSeries ℚ) c) = HahnSeries.C (algebraMap ℚ ℂ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

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

end Rational

section Coeff

open ModularCurve

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)

theorem coeffMap_injective : Function.Injective (coeffMap ι) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff k) h
  exact ι.injective (by simpa using this)

theorem coeffMap_coeffEmb (x : LaurentSeries ℚ) : coeffMap ι (coeffEmb L x) = toC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun q => by simp [eq_ratCast]) x

omit [CharZero L] in
theorem coeffMap_algebraMap' (l : L) : coeffMap ι (algebraMap L (LaurentSeries L) l) = HahnSeries.C (ι l) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]; rfl

end Coeff

section Diamond

open ModularCurve

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ) {N : ℕ} [NeZero N]

theorem coeffMap_diamond_generator {d : ℕ} (hd : d.Coprime N)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 N) (hδ00 : ((δ 0 0 : ℤ) : ZMod N) = (d : ZMod N))
    (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField N))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(laurentBaseChange L (x1FunctionField N))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((baseChangeAut L (diamondAut N d) x' : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L))
    {k : ℤ} (f g : ModularForm Γ₁(N) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (x : ↥K) (hx : (x : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg)) :
    coeffMap ι ((θ x : ↥K) : LaurentSeries L) = qC ⇑(diamondSlash δ hδ f) / qC ⇑(diamondSlash δ hδ g) ∧
      qC ⇑(diamondSlash δ hδ g) ≠ 0 := by

  let y : ↥(x1FunctionField N) := ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
  let x' : ↥(laurentBaseChange L (x1FunctionField N)) := ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩
  have h1 : ((θ x : ↥K) : LaurentSeries L) = ((baseChangeAut L (diamondAut N d) x' : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L) :=
    hθ x x' (by rw [hx])

  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover L (x1FunctionField N) (diamondAut N d).toRingEquiv
  have hbc : IsBaseChangeAutOf L (diamondAut N d) (baseChangeAut L (diamondAut N d)) :=
    isBaseChangeAutOf_baseChangeAut ⟨τ, fun z => hτ z⟩
  have h2 : ((baseChangeAut L (diamondAut N d) x' : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L) =
      coeffEmb L ((diamondAut N d y : ↥(x1FunctionField N)) : LaurentSeries ℚ) := hbc y

  have hD : IsDiamondAut N d (diamondAut N d) := isDiamondAut_diamondAut (ModularCurve.exists_isDiamondAut N hd)
  have h3 := hD.2 k f g pf pg hf hg hg0 δ hδ hδ00

  have e1 : slashQExpC k (⇑g) δ = qC ⇑(diamondSlash δ hδ g) := by
    rw [slashQExpC]; rfl
  have e2 : slashQExpC k (⇑f) δ = qC ⇑(diamondSlash δ hδ f) := by
    rw [slashQExpC]; rfl
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  have hg' : g ≠ 0 := fun h => hqg (by rw [h]; exact qC_coe_zero)
  have hne : qC ⇑(diamondSlash δ hδ g) ≠ 0 := fun h => diamondSlash_ne_zero hδ hg' ((qC_eq_zero_iff _).mp h)
  refine ⟨?_, hne⟩
  rw [h1, h2, coeffMap_coeffEmb]
  rw [e1, e2] at h3
  exact eq_div_of_mul_eq hne h3

end Diamond

section Helpers

open ModularCurve

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem qC_finset_sum {ιx : Type} (s : Finset ιx) (G : ιx → ModularForm Γ₁(N) k) :
    qC ⇑(∑ i ∈ s, G i) = ∑ i ∈ s, qC ⇑(G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact qC_coe_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qC_add, ih]

theorem qC_sum_smul {n : ℕ} (c : Fin n → ℂ) (F : Fin n → ModularForm Γ₁(N) k) :
    qC ⇑(∑ i, c i • F i) = ∑ i, HahnSeries.C (c i) * qC ⇑(F i) := by
  rw [qC_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [qC_smul, HahnSeries.C_mul_eq_smul]

def diamondSlashₗ (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 N) : ModularForm Γ₁(N) k →ₗ[ℂ] ModularForm Γ₁(N) k where
  toFun := diamondSlash δ hδ
  map_add' f g := DFunLike.ext' (by
    rw [coe_diamondSlash, ModularForm.coe_add, ModularForm.coe_add, coe_diamondSlash, coe_diamondSlash, SlashAction.add_slash])
  map_smul' c f := DFunLike.ext' (by
    rw [coe_diamondSlash_SL, RingHom.id_apply, ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, coe_diamondSlash_SL,
      ModularForm.SL_smul_slash])

theorem diamondSlash_sum_smul (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 N) {n : ℕ} (c : Fin n → ℂ)
    (F : Fin n → ModularForm Γ₁(N) k) :
    diamondSlash δ hδ (∑ i, c i • F i) = ∑ i, c i • diamondSlash δ hδ (F i) := by
  show diamondSlashₗ δ hδ (∑ i, c i • F i) = ∑ i, c i • diamondSlashₗ δ hδ (F i)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_smul _ _ _)

theorem diamondSlash_smul (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 N) (c : ℂ) (F : ModularForm Γ₁(N) k) :
    diamondSlash δ hδ (c • F) = c • diamondSlash δ hδ F :=
  map_smul (diamondSlashₗ δ hδ) c F

theorem eq_smul_of_coe_eq {f g : ModularForm Γ₁(N) k} {c : ℂ} (h : (⇑f : ℍ → ℂ) = c • ⇑g) : f = c • g :=
  DFunLike.ext' (by rw [h, ModularForm.IsGLPos.coe_smul])

theorem qC_of_coe_eq_smul {f g : ModularForm Γ₁(N) k} {c : ℂ} (h : (⇑f : ℍ → ℂ) = c • ⇑g) :
    qC ⇑f = HahnSeries.C c * qC ⇑g := by
  rw [eq_smul_of_coe_eq h, qC_smul, HahnSeries.C_mul_eq_smul]

end Helpers

section Emb

open ModularCurve

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ) (K : IntermediateField L (LaurentSeries L))

def emb : ↥K →+* LaurentSeries ℂ := (coeffMap ι).comp (algebraMap ↥K (LaurentSeries L))

theorem emb_apply (x : ↥K) : emb ι K x = coeffMap ι (x : LaurentSeries L) := rfl

theorem emb_injective : Function.Injective (emb ι K) := (coeffMap_injective ι).comp Subtype.val_injective

theorem emb_smul (c : L) (x : ↥K) : emb ι K (c • x) = HahnSeries.C (ι c) * emb ι K x := by
  rw [emb_apply, emb_apply, IntermediateField.coe_smul, Algebra.smul_def, map_mul, coeffMap_algebraMap']

theorem emb_algEquiv_smul (θ : ↥K ≃ₐ[L] ↥K) (c : L) (x : ↥K) : θ (c • x) = c • θ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

end Emb

section Generator

open ModularCurve

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] [NeZero (M * p)]

def Wfun (γ : SL(2, ℤ)) (k : ℤ) (h : ℍ → ℂ) : ℍ → ℂ := fun τ => (h ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)

omit [Fact p.Prime] in
theorem Wfun_smul (γ : SL(2, ℤ)) (k : ℤ) (c : ℂ) (h : ℍ → ℂ) : Wfun (p := p) γ k (c • h) = c • Wfun (p := p) γ k h := by
  ext τ; simp [Wfun, ModularForm.SL_smul_slash]

theorem Wfun_eq_zero_iff (γ : SL(2, ℤ)) (k : ℤ) (h : ℍ → ℂ) : Wfun (p := p) γ k h = 0 ↔ h = 0 := by
  constructor
  · intro hW
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have h1 : h ∣[k] γ = 0 := by
      funext τ

      have : (h ∣[k] γ) (ModularForm.heckeDiagMatrix p • ((ModularForm.heckeDiagMatrix p)⁻¹ • τ)) = 0 := by
        have := congrFun hW ((ModularForm.heckeDiagMatrix p)⁻¹ • τ)
        simpa [Wfun] using this
      rwa [smul_inv_smul] at this
    have : (h ∣[k] γ) ∣[k] γ⁻¹ = 0 := by rw [h1, SlashAction.zero_slash]
    rwa [slash_slash_inv] at this
  · rintro rfl; ext τ; simp [Wfun, SlashAction.zero_slash]

variable (hpM : ¬ p ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
variable (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField (M * p)))
variable (σ : ↥K ≃ₐ[L] ↥K)

def GenLaw : Prop :=
  ∀ (k : ℤ) (f g : ModularForm Γ₁(M * p) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg → intSeriesC ℚ pg ≠ 0 →
    ∀ x : ↥K, (x : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) →
    ∃ (φf φg : ModularForm Γ₁(M * p) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
      (⇑φf : ℍ → ℂ) = (Df : ℂ) • Wfun (p := p) γ k ⇑f ∧
      (⇑φg : ℍ → ℂ) = (Dg : ℂ) • Wfun (p := p) γ k ⇑g ∧
      (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm Γ₁(M * p) k) (r : Fin n → PowerSeries ℤ),
          (∀ i, IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
      (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm Γ₁(M * p) k) (r : Fin n → PowerSeries ℤ),
          (∀ i, IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
      emb ι K (σ x) * HahnSeries.C (Df : ℂ) * qC ⇑φg = HahnSeries.C (Dg : ℂ) * qC ⇑φf

def Pin (d : ℕ) (θ : ↥K ≃ₐ[L] ↥K) : Prop :=
  ∀ (x : ↥K) (x' : ↥(laurentBaseChange L (x1FunctionField (M * p)))),
    (x : LaurentSeries L) = (x' : LaurentSeries L) →
      ((θ x : ↥K) : LaurentSeries L) =
        ((baseChangeAut L (diamondAut (M * p) d) x' : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L)

variable {K σ γ hpM}

include hK in

theorem gen_mem {k : ℤ} (f g : ModularForm Γ₁(M * p) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ K := by
  rw [hK]; exact coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f g hf hg hg0)

def gen {k : ℤ} (f g : ModularForm Γ₁(M * p) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : ↥K :=
  ⟨coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg), gen_mem (L := L) hK f g hf hg hg0⟩

theorem emb_gen {k : ℤ} (f g : ModularForm Γ₁(M * p) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    emb ι K (gen hK f g hf hg hg0) = qC ⇑f / qC ⇑g := by
  rw [emb_apply, gen, coeffMap_coeffEmb, toC_ratio hf hg]

include hpM hγ hγp in

theorem generator_identity (hW : GenLaw (M := M) (p := p) ι γ K σ)
    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)
    (θd θd' : ↥K ≃ₐ[L] ↥K) (hθd : Pin (M := M) (p := p) K d θd) (hθd' : Pin (M := M) (p := p) K d' θd')
    (δ δ' : SL(2, ℤ)) (hδ : δ ∈ Gamma0 (M * p)) (hδ' : δ' ∈ Gamma0 (M * p))
    (hδ00 : ((δ 0 0 : ℤ) : ZMod (M * p)) = (d : ZMod (M * p)))
    (hδ'00 : ((δ' 0 0 : ℤ) : ZMod (M * p)) = (d' : ZMod (M * p)))
    {k : ℤ} (f g : ModularForm Γ₁(M * p) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    emb ι K (σ (θd (gen hK f g hf hg hg0))) = emb ι K (θd' (σ (gen hK f g hf hg hg0))) := by
  classical
  set x := gen hK f g hf hg hg0 with hxdef
  have hx : (x : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) := rfl
  have hqg : qC ⇑g ≠ 0 := qC_ne_zero_of_intSeriesC_ne_zero hg hg0
  have hg' : g ≠ 0 := fun h => hqg (by rw [h]; exact qC_coe_zero)

  obtain ⟨hθx, hB⟩ := coeffMap_diamond_generator ι hd δ hδ hδ00 K hK θd hθd f g hf hg hg0 x hx

  set A := qC ⇑(diamondSlash δ hδ f)
  set B := qC ⇑(diamondSlash δ hδ g)

  obtain ⟨D1, f1, p1, hD1, hp1, hf1⟩ := ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * p) f hf δ hδ
  obtain ⟨D2, g1, p2, hD2, hp2, hg1⟩ := ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * p) g hg δ hδ
  have hf1c : (⇑f1 : ℍ → ℂ) = (D1 : ℂ) • ⇑(diamondSlash δ hδ f) := by rw [hf1, coe_diamondSlash_SL]
  have hg1c : (⇑g1 : ℍ → ℂ) = (D2 : ℂ) • ⇑(diamondSlash δ hδ g) := by rw [hg1, coe_diamondSlash_SL]
  have hqf1 : qC ⇑f1 = HahnSeries.C (D1 : ℂ) * A := qC_of_coe_eq_smul hf1c
  have hqg1 : qC ⇑g1 = HahnSeries.C (D2 : ℂ) * B := qC_of_coe_eq_smul hg1c
  have hD1c : (D1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD1
  have hD2c : (D2 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD2
  have hCD1 : (HahnSeries.C (D1 : ℂ) : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hD1c
  have hCD2 : (HahnSeries.C (D2 : ℂ) : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hD2c
  have hqg1ne : qC ⇑g1 ≠ 0 := by rw [hqg1]; exact mul_ne_zero hCD2 hB
  have hp20 : intSeriesC ℚ p2 ≠ 0 := by
    intro h; apply hqg1ne; rw [← toC_intSeriesC hp2, h, map_zero]

  set x₁ := gen hK f1 g1 hp1 hp2 hp20
  have hex₁ : emb ι K x₁ = HahnSeries.C (D1 : ℂ) * A / (HahnSeries.C (D2 : ℂ) * B) := by
    rw [emb_gen, hqf1, hqg1]
  let c : L := algebraMap ℚ L ((D2 : ℚ) / D1)
  have hιc : ι c = (D2 : ℂ) / D1 := by
    simp [c, eq_ratCast, map_ratCast, Rat.cast_div, Rat.cast_intCast]
  have hθx' : θd x = c • x₁ := by
    apply emb_injective ι K
    rw [emb_smul, hex₁, emb_apply, hθx, hιc, map_div₀]
    field_simp

  obtain ⟨φ1, φ2, E1, E2, hE1, hE2, hφ1, hφ2, -, -, hEq1⟩ := hW k f1 g1 p1 p2 hp1 hp2 hp20 x₁ rfl

  obtain ⟨φf, φg, Df, Dg, hDf, hDg, hφf, hφg, ⟨n, cs, F, r, hF, hφfs⟩, ⟨n', cs', G, r', hG, hφgs⟩, hEq⟩ :=
    hW k f g pf pg hf hg hg0 x hx
  have hDfc : (Df : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hDf
  have hDgc : (Dg : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hDg
  have hE1c : (E1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hE1
  have hE2c : (E2 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hE2

  have hWf : Wfun (p := p) γ k ⇑f = (Df : ℂ)⁻¹ • ⇑φf := by
    rw [hφf, smul_smul, inv_mul_cancel₀ hDfc, one_smul]
  have hWg : Wfun (p := p) γ k ⇑g = (Dg : ℂ)⁻¹ • ⇑φg := by
    rw [hφg, smul_smul, inv_mul_cancel₀ hDgc, one_smul]

  have hφg0 : qC ⇑φg ≠ 0 := by
    intro h
    have hz : φg = 0 := (qC_eq_zero_iff _).mp h
    have : Wfun (p := p) γ k ⇑g = 0 := by rw [hWg, hz]; simp
    exact hg' (DFunLike.ext' (((Wfun_eq_zero_iff γ k _).mp this).trans ModularForm.coe_zero.symm))

  have hDW_f := ModularCurve.atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul p M hpM f γ hγ hγp
    d d' hd hd' hdM hdp δ δ' hδ hδ' hδ00 hδ'00
  have hDW_g := ModularCurve.atkinLehnerSlashFun_slash_eq_slash_atkinLehnerSlashFun_of_upperLeft_gamma1_mul p M hpM g γ hγ hγp
    d d' hd hd' hdM hdp δ δ' hδ hδ' hδ00 hδ'00

  have hWf1 : Wfun (p := p) γ k ((⇑f : ℍ → ℂ) ∣[k] δ) = (Wfun (p := p) γ k ⇑f) ∣[k] δ' := hDW_f
  have hWg1 : Wfun (p := p) γ k ((⇑g : ℍ → ℂ) ∣[k] δ) = (Wfun (p := p) γ k ⇑g) ∣[k] δ' := hDW_g
  have hφ1c : (⇑φ1 : ℍ → ℂ) = ((E1 : ℂ) * D1 / Df) • ⇑(diamondSlash δ' hδ' φf) := by
    rw [hφ1, hf1, Wfun_smul, hWf1, hWf, ModularForm.SL_smul_slash, coe_diamondSlash_SL, smul_smul, smul_smul]
    congr 1
    try field_simp
  have hφ2c : (⇑φ2 : ℍ → ℂ) = ((E2 : ℂ) * D2 / Dg) • ⇑(diamondSlash δ' hδ' φg) := by
    rw [hφ2, hg1, Wfun_smul, hWg1, hWg, ModularForm.SL_smul_slash, coe_diamondSlash_SL, smul_smul, smul_smul]
    congr 1
    try field_simp
  have hq1 : qC ⇑φ1 = HahnSeries.C (E1 : ℂ) * HahnSeries.C (D1 : ℂ) / HahnSeries.C (Df : ℂ) * qC ⇑(diamondSlash δ' hδ' φf) := by
    rw [qC_of_coe_eq_smul hφ1c, map_div₀, map_mul]
  have hq2 : qC ⇑φ2 = HahnSeries.C (E2 : ℂ) * HahnSeries.C (D2 : ℂ) / HahnSeries.C (Dg : ℂ) * qC ⇑(diamondSlash δ' hδ' φg) := by
    rw [qC_of_coe_eq_smul hφ2c, map_div₀, map_mul]

  have hφg' : φg ≠ 0 := fun h => hφg0 (by rw [h]; exact qC_coe_zero)
  have hB' : qC ⇑(diamondSlash δ' hδ' φg) ≠ 0 :=
    fun h => diamondSlash_ne_zero hδ' hφg' ((qC_eq_zero_iff _).mp h)
  have hCDf : (HahnSeries.C (Df : ℂ) : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hDfc
  have hCDg : (HahnSeries.C (Dg : ℂ) : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hDgc
  have hCE1 : (HahnSeries.C (E1 : ℂ) : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hE1c
  have hCE2 : (HahnSeries.C (E2 : ℂ) : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hE2c
  have hq2ne : qC ⇑φ2 ≠ 0 := by
    rw [hq2]; exact mul_ne_zero (div_ne_zero (mul_ne_zero hCE2 hCD2) hCDg) hB'

  have hσx₁ : emb ι K (σ x₁) = HahnSeries.C (E2 : ℂ) * qC ⇑φ1 / (HahnSeries.C (E1 : ℂ) * qC ⇑φ2) := by
    have hne : HahnSeries.C (E1 : ℂ) * qC ⇑φ2 ≠ 0 := mul_ne_zero ((map_ne_zero HahnSeries.C).mpr hE1c) hq2ne
    rw [eq_div_iff hne, ← hEq1]; ring
  have LHS : emb ι K (σ (θd x)) =
      HahnSeries.C ((Dg : ℂ) / Df) * (qC ⇑(diamondSlash δ' hδ' φf) / qC ⇑(diamondSlash δ' hδ' φg)) := by
    rw [hθx', emb_algEquiv_smul, emb_smul, hιc, hσx₁, hq1, hq2, map_div₀, map_div₀]
    field_simp

  let z : Fin n → ↥K := fun i => gen hK (F i) g (hF i) hg hg0
  let w : Fin n' → ↥K := fun j => gen hK (G j) g (hG j) hg hg0
  let u : ↥K := ∑ i, cs i • z i
  let v : ↥K := ∑ j, cs' j • w j
  have hu : emb ι K u = qC ⇑φf / qC ⇑g := by
    simp only [u, map_sum, emb_smul, z, emb_gen]
    rw [hφfs, qC_sum_smul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hv : emb ι K v = qC ⇑φg / qC ⇑g := by
    simp only [v, map_sum, emb_smul, w, emb_gen]
    rw [hφgs, qC_sum_smul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hv0 : v ≠ 0 := by
    intro h; apply hφg0
    have := hv; rw [h, map_zero] at this
    exact (div_eq_zero_iff.mp this.symm).resolve_right hqg
  let c₂ : L := algebraMap ℚ L ((Dg : ℚ) / Df)
  have hιc₂ : ι c₂ = (Dg : ℂ) / Df := by
    simp [c₂, eq_ratCast, map_ratCast, Rat.cast_div, Rat.cast_intCast]
  have hσx : σ x = c₂ • (u / v) := by
    apply emb_injective ι K
    have hne : HahnSeries.C (Df : ℂ) * qC ⇑φg ≠ 0 := mul_ne_zero ((map_ne_zero HahnSeries.C).mpr hDfc) hφg0
    have h1 : emb ι K (σ x) = HahnSeries.C (Dg : ℂ) * qC ⇑φf / (HahnSeries.C (Df : ℂ) * qC ⇑φg) := by
      rw [eq_div_iff hne, ← hEq]; ring
    rw [h1, emb_smul, map_div₀, hu, hv, hιc₂, map_div₀]
    field_simp

  have hθz : ∀ i, emb ι K (θd' (z i)) = qC ⇑(diamondSlash δ' hδ' (F i)) / qC ⇑(diamondSlash δ' hδ' g) := fun i =>
    (coeffMap_diamond_generator ι hd' δ' hδ' hδ'00 K hK θd' hθd' (F i) g (hF i) hg hg0 (z i) rfl).1
  have hθw : ∀ j, emb ι K (θd' (w j)) = qC ⇑(diamondSlash δ' hδ' (G j)) / qC ⇑(diamondSlash δ' hδ' g) := fun j =>
    (coeffMap_diamond_generator ι hd' δ' hδ' hδ'00 K hK θd' hθd' (G j) g (hG j) hg hg0 (w j) rfl).1
  have hBg : qC ⇑(diamondSlash δ' hδ' g) ≠ 0 :=
    (coeffMap_diamond_generator ι hd' δ' hδ' hδ'00 K hK θd' hθd' f g hf hg hg0 x hx).2
  have hθu : emb ι K (θd' u) = qC ⇑(diamondSlash δ' hδ' φf) / qC ⇑(diamondSlash δ' hδ' g) := by
    simp only [u, map_sum, emb_algEquiv_smul, emb_smul, hθz]
    rw [hφfs, diamondSlash_sum_smul, qC_sum_smul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hθv : emb ι K (θd' v) = qC ⇑(diamondSlash δ' hδ' φg) / qC ⇑(diamondSlash δ' hδ' g) := by
    simp only [v, map_sum, emb_algEquiv_smul, emb_smul, hθw]
    rw [hφgs, diamondSlash_sum_smul, qC_sum_smul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have RHS : emb ι K (θd' (σ x)) =
      HahnSeries.C ((Dg : ℂ) / Df) * (qC ⇑(diamondSlash δ' hδ' φf) / qC ⇑(diamondSlash δ' hδ' φg)) := by
    rw [hσx, emb_algEquiv_smul, emb_smul, hιc₂, map_div₀, map_div₀, map_div₀, hθu, hθv]
    field_simp
  rw [LHS, RHS]

end Generator

section Extension

open ModularCurve

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] [NeZero (M * p)]
variable (hpM : ¬ p ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
variable (K : IntermediateField L (LaurentSeries L)) (hK : K = laurentBaseChange L (x1FunctionField (M * p)))
variable (σ : ↥K ≃ₐ[L] ↥K)

include hK hpM hγ hγp in
set_option maxHeartbeats 3200000 in

theorem conj_eq (hW : GenLaw (M := M) (p := p) ι γ K σ)
    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)
    (θd θd' : ↥K ≃ₐ[L] ↥K) (hθd : Pin (M := M) (p := p) K d θd) (hθd' : Pin (M := M) (p := p) K d' θd') :
    ∀ y : ↥K, σ (θd y) = θd' (σ y) := by
  classical
  obtain ⟨δ, hδ, hδ00⟩ := exists_gamma0_apply_eq hd
  obtain ⟨δ', hδ', hδ'00⟩ := exists_gamma0_apply_eq hd'

  let Ψ₁ : ↥K →ₐ[L] ↥K := (σ : ↥K →ₐ[L] ↥K).comp (θd : ↥K →ₐ[L] ↥K)
  let Ψ₂ : ↥K →ₐ[L] ↥K := (θd' : ↥K →ₐ[L] ↥K).comp (σ : ↥K →ₐ[L] ↥K)
  have hΨ₁ : ∀ y, Ψ₁ y = σ (θd y) := fun _ => rfl
  have hΨ₂ : ∀ y, Ψ₂ y = θd' (σ y) := fun _ => rfl

  have hgen : ∀ {k : ℤ} (f g : ModularForm Γ₁(M * p) k) {pf pg : PowerSeries ℤ}
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      Ψ₁ (gen hK f g hf hg hg0) = Ψ₂ (gen hK f g hf hg hg0) := by
    intro k f g pf pg hf hg hg0
    apply emb_injective ι K
    exact generator_identity ι (hpM := hpM) (hγ := hγ) (hγp := hγp) (hK := hK) hW d d' hd hd' hdM hdp θd θd' hθd hθd'
      δ δ' hδ hδ' hδ00 hδ'00 f g hf hg hg0

  have hKmem : ∀ z : ↥(x1FunctionField (M * p)), coeffEmb L (z : LaurentSeries ℚ) ∈ K := fun z => by
    rw [hK]; exact coeffEmb_mem_laurentBaseChange L z.2
  let θ₀ : ↥(x1FunctionField (M * p)) →+* ↥K :=
    RingHom.codRestrict ((coeffEmb L).comp (x1FunctionField (M * p)).toSubring.subtype) K (fun z => hKmem z)
  have hθ₀ : ∀ z, (θ₀ z : ↥K) = ⟨coeffEmb L (z : LaurentSeries ℚ), hKmem z⟩ := fun _ => rfl
  have hF : ∀ z, z ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 (M * p))) →
      ∀ hz : z ∈ x1FunctionField (M * p), Ψ₁ (θ₀ ⟨z, hz⟩) = Ψ₂ (θ₀ ⟨z, hz⟩) := by
    intro z hz'
    induction hz' using IntermediateField.adjoin_induction with
    | mem y hy =>
      intro hz
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      have e : θ₀ ⟨_, hz⟩ = gen hK f g hf hg hg0 := Subtype.ext rfl
      rw [e]
      exact hgen f g hf hg hg0
    | algebraMap q =>
      intro hz
      have e : (⟨algebraMap ℚ (LaurentSeries ℚ) q, hz⟩ : ↥(x1FunctionField (M * p))) = ((q : ℚ) : ↥(x1FunctionField (M * p))) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) q = (((q : ℚ) : ↥(x1FunctionField (M * p))) : LaurentSeries ℚ)
        rw [eq_ratCast, SubfieldClass.coe_ratCast]
      rw [e, map_ratCast, map_ratCast, map_ratCast]
    | add y w hy hw ihy ihw =>
      intro h
      rw [show (⟨y + w, h⟩ : ↥(x1FunctionField (M * p))) = ⟨y, hy⟩ + ⟨w, hw⟩ from rfl, map_add, map_add, map_add, ihy hy, ihw hw]
    | inv y hy ihy =>
      intro h
      rw [show (⟨y⁻¹, h⟩ : ↥(x1FunctionField (M * p))) = (⟨y, hy⟩ : ↥(x1FunctionField (M * p)))⁻¹ from rfl,
        map_inv₀, map_inv₀, map_inv₀, ihy hy]
    | mul y w hy hw ihy ihw =>
      intro h
      rw [show (⟨y * w, h⟩ : ↥(x1FunctionField (M * p))) = ⟨y, hy⟩ * ⟨w, hw⟩ from rfl, map_mul, map_mul, map_mul, ihy hy, ihw hw]

  suffices H : ∀ w, w ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪
        ⇑(coeffEmb L) '' (x1FunctionField (M * p) : Set (LaurentSeries ℚ))) → ∀ hw : w ∈ K, Ψ₁ ⟨w, hw⟩ = Ψ₂ ⟨w, hw⟩ by
    intro y
    rw [← hΨ₁, ← hΨ₂]
    have hy : (y : LaurentSeries L) ∈ laurentBaseChange L (x1FunctionField (M * p)) := hK ▸ y.2
    exact H y ((mem_laurentBaseChange_iff (L := L)).mp hy) y.2
  intro w hw
  induction hw using Subfield.closure_induction with
  | mem w hw =>
    intro hwK
    rcases hw with ⟨l, rfl⟩ | ⟨z, hz, rfl⟩
    · have e : (⟨algebraMap L (LaurentSeries L) l, hwK⟩ : ↥K) = algebraMap L (↥K) l := Subtype.ext rfl
      rw [e, AlgHom.commutes, AlgHom.commutes]
    · have e : (⟨coeffEmb L z, hwK⟩ : ↥K) = θ₀ ⟨z, hz⟩ := Subtype.ext rfl
      rw [e]
      exact hF z hz hz
  | one =>
    intro h

    have h1 : (algebraMap L (LaurentSeries L) 1) ∈ K := by rw [map_one]; exact one_mem K
    have e : (⟨_, h⟩ : ↥K) = ⟨algebraMap L (LaurentSeries L) 1, h1⟩ := Subtype.ext (map_one _).symm
    have e' : (⟨algebraMap L (LaurentSeries L) 1, h1⟩ : ↥K) = algebraMap L (↥K) 1 := Subtype.ext rfl
    rw [e, e', AlgHom.commutes, AlgHom.commutes]
  | add a b ha hb iha ihb =>
    intro h
    have haK : a ∈ K := by rw [hK, mem_laurentBaseChange_iff]; exact ha
    have hbK : b ∈ K := by rw [hK, mem_laurentBaseChange_iff]; exact hb
    rw [show (⟨a + b, h⟩ : ↥K) = ⟨a, haK⟩ + ⟨b, hbK⟩ from rfl, map_add, map_add, iha haK, ihb hbK]
  | neg a ha iha =>
    intro h
    have haK : a ∈ K := by rw [hK, mem_laurentBaseChange_iff]; exact ha
    rw [show (⟨-a, h⟩ : ↥K) = -⟨a, haK⟩ from rfl, map_neg, map_neg, iha haK]
  | inv a ha iha =>
    intro h
    have haK : a ∈ K := by rw [hK, mem_laurentBaseChange_iff]; exact ha
    rw [show (⟨a⁻¹, h⟩ : ↥K) = (⟨a, haK⟩ : ↥K)⁻¹ from rfl, map_inv₀, map_inv₀, iha haK]
  | mul a b ha hb iha ihb =>
    intro h
    have haK : a ∈ K := by rw [hK, mem_laurentBaseChange_iff]; exact ha
    have hbK : b ∈ K := by rw [hK, mem_laurentBaseChange_iff]; exact hb
    rw [show (⟨a * b, h⟩ : ↥K) = ⟨a, haK⟩ * ⟨b, hbK⟩ from rfl, map_mul, map_mul, iha haK, ihb hbK]

end Extension

end CONJ5
p2m_reactivate "P2MW.S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul.CONJ5"

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul.CONJ5"

open scoped MatrixGroups ModularForm

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hWσ : ∃ (ι : L →+* ℂ) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ 1 1 ∧
        ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ))) :
    (∀ (d d' : ℕ), d.Coprime (M * p) → d'.Coprime (M * p) →
        ((d' : ZMod M) = (d : ZMod M)) → ((d' : ZMod p) * (d : ZMod p) = 1) →
        ∀ (θd θd' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) := by
  intro d d' hd hd' hdM hdp θd θd' hθd hθd' x
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ι, γ, hγ, hγp, hWgen⟩ := hWσ
  have hW : CONJ5.GenLaw (M := M) (p := p) ι γ K σ := hWgen
  have key := CONJ5.conj_eq ι hpM γ hγ hγp K hK σ hW d d' hd hd' hdM hdp θd θd' hθd hθd' (σ.symm x)
  rw [AlgEquiv.apply_symm_apply] at key
  rw [key]

#print axioms solution

end S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul (solution)
