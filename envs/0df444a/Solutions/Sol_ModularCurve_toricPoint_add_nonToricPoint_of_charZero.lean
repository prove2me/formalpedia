-- Prove2me | solution 1 for ModularCurve.toricPoint_add_nonToricPoint_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/671ccc93-3806-59b4-9f5c-f0c1c5491315

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_TateCurve_point_mul_eq_add_of_norm_le_one
import Theorems.Thm_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst
import Theorems.Thm_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd
import Theorems.Thm_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst
import Theorems.Thm_ModularCurve_tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd
import Theorems.Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

p2m_open "HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries Filter MonoidWithZeroHom"
open scoped Topology Uniformity

namespace HahnSeries
p2m_export "HahnSeries" "support coeff_sub orderTop C_apply coeff_eq_zero_of_lt_orderTop single C_ne_zero embDomain le_orderTop_iff_forall order mem_support C_zero coeff single_pow pow_add orderTop_single C_injective C map C_one embDomain_notin_range embDomainRingHom single_ne_zero orderTop_neg addVal coeff_single_of_ne coeff_single embDomain_coeff isPWO_support' isWF_support isAlgClosed_rat"
namespace XAdicRatSlot
p2m_open "HahnSeries"

variable (K : Type*) [Field K]

scoped instance valued : Valued (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  Valued.mk' (AddValuation.toValuation (HahnSeries.addVal ℚ K))

theorem valued_apply (x : HahnSeries ℚ K) :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ)
      = Multiplicative.ofAdd (OrderDual.toDual x.orderTop) := rfl

theorem valued_lt_valued_iff (x y : HahnSeries ℚ K) :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) < Valued.v y ↔ y.orderTop < x.orderTop := by
  rw [valued_apply, valued_apply]; exact Iff.rfl

theorem valued_le_valued_iff (x y : HahnSeries ℚ K) :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) ≤ Valued.v y ↔ y.orderTop ≤ x.orderTop := by
  rw [valued_apply, valued_apply]; exact Iff.rfl

theorem valued_lt_one_iff (x : HahnSeries ℚ K) :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) < 1 ↔ 0 < x.orderTop := by
  rw [valued_apply]; exact Iff.rfl

scoped instance mulArchimedean : MulArchimedean (Multiplicative (WithTop ℚ)ᵒᵈ) where
  arch x y hy := by
    have hg : OrderDual.ofDual (Multiplicative.toAdd y) < (0 : WithTop ℚ) := hy
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (hg.ne_top)
    rw [← hq] at hg
    have hq0 : q < 0 := by exact_mod_cast hg
    rcases eq_or_ne (OrderDual.ofDual (Multiplicative.toAdd x)) ⊤ with hx | hx
    · refine ⟨0, ?_⟩
      rw [pow_zero]
      change (0 : WithTop ℚ) ≤ OrderDual.ofDual (Multiplicative.toAdd x)
      exact hx ▸ le_top
    · obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨n, hn⟩ := Archimedean.arch (-p) (neg_pos.mpr hq0)
      refine ⟨n, ?_⟩
      change (n • OrderDual.ofDual (Multiplicative.toAdd y) : WithTop ℚ)
        ≤ OrderDual.ofDual (Multiplicative.toAdd x)
      rw [← hq, ← hp, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
      rw [nsmul_eq_mul] at hn; linarith

theorem single_ne_zero' (r : ℚ) : (single r (1 : K) : HahnSeries ℚ K) ≠ 0 :=
  HahnSeries.single_ne_zero one_ne_zero

scoped instance isNontrivial :
    (Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).IsNontrivial := by
  refine ⟨⟨single (1 : ℚ) (1 : K), (Valuation.ne_zero_iff _).mpr (single_ne_zero' K 1), ?_⟩⟩
  intro h
  have h1 : (0 : WithTop ℚ) < (single (1 : ℚ) (1 : K)).orderTop := by
    rw [orderTop_single one_ne_zero]; exact_mod_cast one_pos
  have := (valued_lt_one_iff K _).mpr h1
  rw [h] at this
  exact lt_irrefl _ this

theorem nonempty_rankOne :
    Nonempty ((Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).RankOne) :=
  Valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance

scoped instance rankOne :
    (Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).RankOne :=
  (nonempty_rankOne K).some

scoped instance nontriviallyNormedField : NontriviallyNormedField (HahnSeries ℚ K) :=
  Valued.toNontriviallyNormedField (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)

scoped instance isUltrametricDist : IsUltrametricDist (HahnSeries ℚ K) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ))

scoped instance (priority := low) decidableEq : DecidableEq (HahnSeries ℚ K) := Classical.decEq _

example : (nontriviallyNormedField K).toNormedField.toField = (inferInstance : Field (HahnSeries ℚ K)) := rfl

private theorem _root_.HahnSeries.XAdicRatSlot.norm_lt_one_iff (x : HahnSeries ℚ K) : ‖x‖ < 1 ↔ 0 < x.orderTop := by
  rw [Valued.toNormedField.norm_lt_one_iff, valued_lt_one_iff]

p2m_export "HahnSeries.XAdicRatSlot" "norm_lt_one_iff"

variable {K}

structure IsBallChain {ι : Type*} [LinearOrder ι]
    (r : ι → HahnSeries ℚ K) (δ : ι → WithTop ℚ) : Prop where
  δ_mono : Monotone δ
  mem_ball : ∀ ⦃i j : ι⦄, i ≤ j → δ i ≤ (r j - r i).orderTop

open Classical in
def pseudoLimitCoeff {ι : Type*} [LinearOrder ι]
    (r : ι → HahnSeries ℚ K) (δ : ι → WithTop ℚ) (g : ℚ) : K :=
  if h : ∃ i, (g : WithTop ℚ) < δ i then (r h.choose).coeff g else 0

theorem IsBallChain.coeff_eq_of_lt {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries ℚ K} {δ : ι → WithTop ℚ} (h : IsBallChain r δ)
    {i j : ι} {g : ℚ} (hgi : (g : WithTop ℚ) < δ i) (hgj : (g : WithTop ℚ) < δ j) :
    (r i).coeff g = (r j).coeff g := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hgj hgi (le_of_not_ge hij)).symm
  have hdiff : (r j - r i).coeff g = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hgi (h.mem_ball hij))
  rw [HahnSeries.coeff_sub, sub_eq_zero] at hdiff
  exact hdiff.symm

open Classical in
theorem IsBallChain.pseudoLimitCoeff_eq {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries ℚ K} {δ : ι → WithTop ℚ} (h : IsBallChain r δ)
    {g : ℚ} {i : ι} (hgi : (g : WithTop ℚ) < δ i) :
    pseudoLimitCoeff r δ g = (r i).coeff g := by
  unfold pseudoLimitCoeff
  rw [dif_pos ⟨i, hgi⟩]
  exact h.coeff_eq_of_lt (Exists.choose_spec (p := fun i => (g : WithTop ℚ) < δ i) ⟨i, hgi⟩) hgi

open Classical in
theorem IsBallChain.isPWO_support_pseudoLimitCoeff {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries ℚ K} {δ : ι → WithTop ℚ} (h : IsBallChain r δ) :
    (Function.support (pseudoLimitCoeff r δ)).IsPWO := by
  refine Set.IsWF.isPWO ?_
  rw [Set.isWF_iff_no_descending_seq]
  intro f hanti hf
  have hf0 : pseudoLimitCoeff r δ (f 0) ≠ 0 := hf 0
  have hex : ∃ i, ((f 0 : ℚ) : WithTop ℚ) < δ i := by
    by_contra hnone
    rw [pseudoLimitCoeff, dif_neg hnone] at hf0; exact hf0 rfl
  obtain ⟨i₀, hi₀⟩ := hex
  have hfk : ∀ k, f k ∈ (r i₀).support := by
    intro k
    have hfk0 : f k ≤ f 0 := hanti.antitone (Nat.zero_le k)
    have hfklt : ((f k : ℚ) : WithTop ℚ) < δ i₀ :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr hfk0) hi₀
    have heq := h.pseudoLimitCoeff_eq hfklt
    rw [HahnSeries.mem_support, ← heq]
    exact hf k
  have hWF := (r i₀).isWF_support
  rw [Set.isWF_iff_no_descending_seq] at hWF
  exact hWF f hanti hfk

def IsBallChain.pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries ℚ K} {δ : ι → WithTop ℚ} (h : IsBallChain r δ) :
    HahnSeries ℚ K where
  coeff := pseudoLimitCoeff r δ
  isPWO_support' := h.isPWO_support_pseudoLimitCoeff

theorem IsBallChain.coeff_pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries ℚ K} {δ : ι → WithTop ℚ} (h : IsBallChain r δ)
    {g : ℚ} {i : ι} (hgi : (g : WithTop ℚ) < δ i) :
    h.pseudoLimit.coeff g = (r i).coeff g :=
  h.pseudoLimitCoeff_eq hgi

theorem IsBallChain.le_orderTop_sub_pseudoLimit {ι : Type*} [LinearOrder ι]
    {r : ι → HahnSeries ℚ K} {δ : ι → WithTop ℚ} (h : IsBallChain r δ) (i : ι) :
    δ i ≤ (h.pseudoLimit - r i).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  rw [HahnSeries.coeff_sub, h.coeff_pseudoLimit hg, sub_self]

variable (K)

def gammaN (n : ℕ) : (ValueGroup₀ (.ofClass (Valued.v (R := HahnSeries ℚ K))))ˣ :=
  Units.mk0 (Valued.v.restrict (single (n : ℚ) (1 : K)))
    ((Valued.v.restrict).ne_zero_iff.mpr (HahnSeries.single_ne_zero one_ne_zero))

theorem lt_gammaN_iff (n : ℕ) (z : HahnSeries ℚ K) :
    Valued.v.restrict z < (gammaN K n : ValueGroup₀ (.ofClass (Valued.v (R := HahnSeries ℚ K))))
      ↔ ((n : ℚ) : WithTop ℚ) < z.orderTop := by
  rw [gammaN, Units.val_mk0, Valuation.restrict_lt_iff, valued_lt_valued_iff,
    HahnSeries.orderTop_single (one_ne_zero : (1:K) ≠ 0)]

theorem gamma0_ne_zero_iff (a : Multiplicative (WithTop ℚ)ᵒᵈ) :
    a ≠ 0 ↔ OrderDual.ofDual (Multiplicative.toAdd a) ≠ (⊤ : WithTop ℚ) :=
  ⟨fun ha h ↦ ha (Multiplicative.toAdd.injective (OrderDual.ofDual.injective h)),
   fun h ha ↦ h (ha ▸ rfl)⟩

scoped instance completeSpace : CompleteSpace (HahnSeries ℚ K) := by
  refine UniformSpace.complete_of_convergent_controlled_sequences
    (fun n ↦ {p : _ × _ | ((n : ℚ) : WithTop ℚ) < (p.2 - p.1).orderTop}) ?_ ?_
  · intro n
    refine (Valued.hasBasis_uniformity (HahnSeries ℚ K)
        (Multiplicative (WithTop ℚ)ᵒᵈ)).mem_of_superset (i := gammaN K n) trivial ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    exact (lt_gammaN_iff K n _).mp hp
  · intro u hctrl
    have hbc : IsBallChain u (fun N : ℕ ↦ ((N : ℚ) : WithTop ℚ)) := by
      refine ⟨fun i j hij ↦ by exact_mod_cast hij, fun i j hij ↦ ?_⟩
      have h := hctrl i i j le_rfl hij
      simp only [Set.mem_setOf_eq] at h
      exact le_of_lt h
    refine ⟨hbc.pseudoLimit, ?_⟩
    rw [← tendsto_sub_nhds_zero_iff,
        (Valued.hasBasis_nhds_zero (HahnSeries ℚ K) _).tendsto_right_iff]
    rintro γ -
    have hγemb : ValueGroup₀.embedding (↑γ : ValueGroup₀ (.ofClass (Valued.v (R := HahnSeries ℚ K))))
        ≠ (0 : Multiplicative (WithTop ℚ)ᵒᵈ) := fun h ↦
      γ.ne_zero (ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
    obtain ⟨Mγ, hMγ⟩ := WithTop.ne_top_iff_exists.mp ((gamma0_ne_zero_iff _).mp hγemb)
    obtain ⟨N, hN⟩ := exists_nat_gt Mγ
    refine eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_lt_iff_lt_embedding, valued_apply]
    change (OrderDual.ofDual (Multiplicative.toAdd
        (ValueGroup₀.embedding ((γ : ValueGroup₀ (.ofClass (Valued.v (R := HahnSeries ℚ K)))))))
      : WithTop ℚ) < (u n - hbc.pseudoLimit).orderTop
    rw [← hMγ]
    calc ((Mγ : ℚ) : WithTop ℚ) < ((N : ℚ) : WithTop ℚ) := by exact_mod_cast hN
      _ ≤ ((n : ℚ) : WithTop ℚ) := by exact_mod_cast hn
      _ ≤ (hbc.pseudoLimit - u n).orderTop := hbc.le_orderTop_sub_pseudoLimit n
      _ = (u n - hbc.pseudoLimit).orderTop := by rw [← HahnSeries.orderTop_neg, neg_sub]

variable {K}
variable {F : Type*} [Field F]

def coeffRingHom (f : F →+* K) : LaurentSeries F →+* LaurentSeries K where
  toFun x := HahnSeries.map x f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (f : F →ₙ+* K)
  map_zero' := HahnSeries.map_zero (f : ZeroHom F K)
  map_add' _ _ := HahnSeries.map_add (f : F →+ K)

@[scoped simp] theorem coeff_coeffRingHom (f : F →+* K) (x : LaurentSeries F) (n : ℤ) :
    (coeffRingHom f x).coeff n = f (x.coeff n) := rfl

def intToRat : LaurentSeries K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (Int.castAddHom ℚ) Int.cast_injective (fun _ _ => Int.cast_le)

def laurentEmb (f : F →+* K) : LaurentSeries F →+* HahnSeries ℚ K :=
  (intToRat (K := K)).comp (coeffRingHom f)

theorem laurentEmb_coeff_intCast (f : F →+* K) (x : LaurentSeries F) (n : ℤ) :
    (laurentEmb f x).coeff (n : ℚ) = f (x.coeff n) := by
  show (HahnSeries.embDomain ⟨⟨((↑) : ℤ → ℚ), Int.cast_injective⟩, Int.cast_le⟩
    (coeffRingHom f x)).coeff (n : ℚ) = f (x.coeff n)
  have := @HahnSeries.embDomain_coeff ℤ ℚ K _ _ _
    ⟨⟨((↑) : ℤ → ℚ), Int.cast_injective⟩, Int.cast_le⟩ (coeffRingHom f x) n
  exact this

theorem laurentEmb_coeff_of_not_mem (f : F →+* K) (x : LaurentSeries F) {g : ℚ}
    (hg : g ∉ Set.range ((↑) : ℤ → ℚ)) : (laurentEmb f x).coeff g = 0 := by
  show (HahnSeries.embDomain ⟨⟨((↑) : ℤ → ℚ), Int.cast_injective⟩, Int.cast_le⟩
    (coeffRingHom f x)).coeff g = 0
  exact HahnSeries.embDomain_notin_range hg

theorem laurentEmb_single (f : F →+* K) (n : ℤ) (a : F) :
    laurentEmb f (HahnSeries.single n a) = HahnSeries.single (n : ℚ) (f a) := by
  ext g
  by_cases hmem : g ∈ Set.range ((↑) : ℤ → ℚ)
  · obtain ⟨m, rfl⟩ := hmem
    rw [laurentEmb_coeff_intCast, HahnSeries.coeff_single, HahnSeries.coeff_single]
    by_cases h : m = n
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (by exact_mod_cast h')), map_zero]
  · rw [laurentEmb_coeff_of_not_mem f _ hmem, HahnSeries.coeff_single_of_ne]
    rintro rfl
    exact hmem ⟨n, rfl⟩

theorem laurentEmb_C (f : F →+* K) (a : F) :
    laurentEmb f (HahnSeries.C a) = HahnSeries.C (f a) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, laurentEmb_single, Int.cast_zero]

theorem laurentEmb_injective (f : F →+* K) : Function.Injective (laurentEmb f) :=
  (laurentEmb f).injective

theorem le_orderTop_laurentEmb (f : F →+* K) (x : LaurentSeries F) (D : ℤ)
    (h : ∀ n : ℤ, n < D → x.coeff n = 0) :
    ((D : ℚ) : WithTop ℚ) ≤ (laurentEmb f x).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  by_cases hmem : g ∈ Set.range ((↑) : ℤ → ℚ)
  · obtain ⟨n, rfl⟩ := hmem
    have hn : n < D := by exact_mod_cast (WithTop.coe_lt_coe.mp hg)
    rw [laurentEmb_coeff_intCast, h n hn, map_zero]
  · exact laurentEmb_coeff_of_not_mem f x hmem

open scoped LaurentSeries.XAdic in

theorem continuous_laurentEmb (f : F →+* K) : Continuous (laurentEmb f) := by
  apply continuous_of_continuousAt_zero (laurentEmb f).toAddMonoidHom
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero (LaurentSeries F) (WithZero (Multiplicative ℤ))).tendsto_iff
      (Valued.hasBasis_nhds_zero (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ))]
  rintro γ -

  have hγemb : ValueGroup₀.embedding (↑γ : ValueGroup₀ (.ofClass (Valued.v (R := HahnSeries ℚ K))))
      ≠ (0 : Multiplicative (WithTop ℚ)ᵒᵈ) := fun h ↦
    γ.ne_zero (ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  obtain ⟨Mγ, hMγ⟩ := WithTop.ne_top_iff_exists.mp ((gamma0_ne_zero_iff _).mp hγemb)
  obtain ⟨D, hD⟩ := exists_int_gt Mγ

  refine ⟨Units.mk0 (Valued.v.restrict (HahnSeries.single D (1 : F) : LaurentSeries F))
      ((Valued.v.restrict).ne_zero_iff.mpr (HahnSeries.single_ne_zero one_ne_zero)), trivial, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  rw [LaurentSeries.valuation_single_zpow] at hx
  have hcoeff : ∀ n : ℤ, n < D → x.coeff n = 0 :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := F)).mp hx.le
  have hord := le_orderTop_laurentEmb f x D hcoeff
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, valued_apply]
  change (OrderDual.ofDual (Multiplicative.toAdd
      (ValueGroup₀.embedding ((γ : ValueGroup₀ (.ofClass (Valued.v (R := HahnSeries ℚ K)))))))
    : WithTop ℚ) < ((laurentEmb f).toAddMonoidHom x).orderTop
  rw [← hMγ]
  calc ((Mγ : ℚ) : WithTop ℚ) < ((D : ℚ) : WithTop ℚ) := by exact_mod_cast hD
    _ ≤ (laurentEmb f x).orderTop := hord

section TateCompat

open scoped LaurentSeries.XAdic

theorem laurentEmb_tsum (f : F →+* K) {ι : Type*} {g : ι → LaurentSeries F} (hg : Summable g) :
    laurentEmb f (∑' i, g i) = ∑' i, laurentEmb f (g i) :=
  (hg.hasSum.map (laurentEmb f) (continuous_laurentEmb f)).tsum_eq.symm

theorem laurentEmb_xfun (f : F →+* K) (w : LaurentSeries F) :
    laurentEmb f (TateCurve.xfun w) = TateCurve.xfun (laurentEmb f w) := by
  simp only [TateCurve.xfun, map_div₀, map_pow, map_sub, map_one]

theorem laurentEmb_yfun (f : F →+* K) (w : LaurentSeries F) :
    laurentEmb f (TateCurve.yfun w) = TateCurve.yfun (laurentEmb f w) := by
  simp only [TateCurve.yfun, map_div₀, map_pow, map_sub, map_one]

theorem laurentEmb_term (f : F →+* K) (c : ℕ → ℕ) (q : LaurentSeries F) (n : ℕ) :
    laurentEmb f (TateCurve.term c q n) = TateCurve.term c (laurentEmb f q) n := by
  simp only [TateCurve.term, map_mul, map_natCast, map_div₀, map_sub, map_one, map_pow]

theorem laurentEmb_coeffSum (f : F →+* K) (c : ℕ → ℕ) {q : LaurentSeries F} (hq : ‖q‖₊ < 1) :
    laurentEmb f (TateCurve.coeffSum c q) = TateCurve.coeffSum c (laurentEmb f q) := by
  rw [TateCurve.coeffSum, TateCurve.coeffSum, laurentEmb_tsum f (TateCurve.summable_term c hq)]
  exact tsum_congr fun n => laurentEmb_term f c q n

theorem laurentEmb_a₄ (f : F →+* K) {q : LaurentSeries F} (hq : ‖q‖₊ < 1) :
    laurentEmb f (TateCurve.a₄ q) = TateCurve.a₄ (laurentEmb f q) := by
  rw [TateCurve.a₄, TateCurve.a₄, map_neg, laurentEmb_coeffSum f _ hq]

theorem laurentEmb_a₆ (f : F →+* K) {q : LaurentSeries F} (hq : ‖q‖₊ < 1) :
    laurentEmb f (TateCurve.a₆ q) = TateCurve.a₆ (laurentEmb f q) := by
  rw [TateCurve.a₆, TateCurve.a₆, map_neg, laurentEmb_coeffSum f _ hq]

theorem curve_map_laurentEmb (f : F →+* K) {q : LaurentSeries F} (hq : ‖q‖₊ < 1) :
    (TateCurve.curve q).map (laurentEmb f) = TateCurve.curve (laurentEmb f q) := by
  simp only [TateCurve.curve, WeierstrassCurve.map, map_one, map_zero, laurentEmb_a₄ f hq,
    laurentEmb_a₆ f hq]

theorem laurentEmb_s₁ (f : F →+* K) {q : LaurentSeries F} (hq : ‖q‖₊ < 1) :
    laurentEmb f (TateCurve.s₁ q) = TateCurve.s₁ (laurentEmb f q) := by
  rw [TateCurve.s₁, TateCurve.s₁, laurentEmb_coeffSum f _ hq]

theorem laurentEmb_xTerm (f : F →+* K) (q u : LaurentSeries F) (n : ℤ) :
    laurentEmb f (TateCurve.xTerm q u n) = TateCurve.xTerm (laurentEmb f q) (laurentEmb f u) n := by
  rw [TateCurve.xTerm, TateCurve.xTerm, laurentEmb_xfun, map_mul, map_zpow₀]

theorem laurentEmb_yTerm (f : F →+* K) (q u : LaurentSeries F) (n : ℤ) :
    laurentEmb f (TateCurve.yTerm q u n) = TateCurve.yTerm (laurentEmb f q) (laurentEmb f u) n := by
  rw [TateCurve.yTerm, TateCurve.yTerm, laurentEmb_yfun, map_mul, map_zpow₀]

theorem laurentEmb_pointX (f : F →+* K) {q u : LaurentSeries F} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) :
    laurentEmb f (TateCurve.pointX q u) = TateCurve.pointX (laurentEmb f q) (laurentEmb f u) := by
  rw [TateCurve.pointX, TateCurve.pointX, map_sub, map_mul, map_ofNat, laurentEmb_s₁ f hq,
    laurentEmb_tsum f (TateCurve.summable_xTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => laurentEmb_xTerm f q u n

theorem laurentEmb_pointY (f : F →+* K) {q u : LaurentSeries F} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) :
    laurentEmb f (TateCurve.pointY q u) = TateCurve.pointY (laurentEmb f q) (laurentEmb f u) := by
  rw [TateCurve.pointY, TateCurve.pointY, map_add, laurentEmb_s₁ f hq,
    laurentEmb_tsum f (TateCurve.summable_yTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => laurentEmb_yTerm f q u n

end TateCompat

end HahnSeries.XAdicRatSlot
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries"

namespace HahnSeries
p2m_export "HahnSeries" "support coeff_sub orderTop C_apply coeff_eq_zero_of_lt_orderTop single C_ne_zero embDomain le_orderTop_iff_forall order mem_support C_zero coeff single_pow pow_add orderTop_single C_injective C map C_one embDomain_notin_range embDomainRingHom single_ne_zero orderTop_neg addVal coeff_single_of_ne coeff_single embDomain_coeff isPWO_support' isWF_support isAlgClosed_rat"
namespace XAdicRatSlot
p2m_open "HahnSeries"

variable {K : Type*} [Field K]

private theorem _root_.HahnSeries.XAdicRatSlot.norm_C_eq_one {a : K} (ha : a ≠ 0) : ‖(HahnSeries.C a : HahnSeries ℚ K)‖ = 1 := by
  have hord : (HahnSeries.C a : HahnSeries ℚ K).orderTop = 0 := by
    rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha, WithTop.coe_zero]
  have hone : (1 : HahnSeries ℚ K).orderTop = 0 := by
    rw [← HahnSeries.C_one, HahnSeries.C_apply, HahnSeries.orderTop_single one_ne_zero,
      WithTop.coe_zero]
  refine le_antisymm ?_ ?_
  · rw [Valued.toNormedField.norm_le_one_iff,
      ← (Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).map_one,
      valued_le_valued_iff, hord, hone]
  · rw [Valued.toNormedField.one_le_norm_iff,
      ← (Valued.v : Valuation (HahnSeries ℚ K) (Multiplicative (WithTop ℚ)ᵒᵈ)).map_one,
      valued_le_valued_iff, hord, hone]

p2m_export "HahnSeries.XAdicRatSlot" "norm_C_eq_one"
end HahnSeries.XAdicRatSlot
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"

namespace LaurentSeries
p2m_export "LaurentSeries" "valuation_single_zpow valuation_le_iff_coeff_lt_eq_zero valued XAdic.norm_X_lt_one XAdic.nnnorm_X_pow_lt_one XAdic.X_pow_ne_zero XAdic.charZero"
namespace XAdicSlot
p2m_open "LaurentSeries"

open scoped LaurentSeries.XAdic

variable {F : Type*} [Field F]

theorem norm_C_le_one (a : F) : ‖(HahnSeries.C a : LaurentSeries F)‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff]
  have h : Valued.v (HahnSeries.C a : LaurentSeries F) ≤ WithZero.exp (-(0 : ℤ)) := by
    rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
    intro n hn
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne]
  simpa using h

theorem norm_C_eq_one {a : F} (ha : a ≠ 0) : ‖(HahnSeries.C a : LaurentSeries F)‖ = 1 := by
  have h1 := norm_C_le_one a
  have h2 := norm_C_le_one a⁻¹
  have hprod : ‖(HahnSeries.C a : LaurentSeries F)‖ * ‖(HahnSeries.C a⁻¹ : LaurentSeries F)‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, norm_one]
  have h0 : 0 ≤ ‖(HahnSeries.C a : LaurentSeries F)‖ := norm_nonneg _
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖(HahnSeries.C a : LaurentSeries F)‖ * ‖(HahnSeries.C a⁻¹ : LaurentSeries F)‖ :=
        hprod.symm
    _ ≤ ‖(HahnSeries.C a : LaurentSeries F)‖ * 1 := mul_le_mul_of_nonneg_left h2 h0
    _ = _ := mul_one _

end LaurentSeries.XAdicSlot
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"

namespace ModularCurve
p2m_export "ModularCurve" "tateToricPoint_eq_toricPoint nonToricPoint tateBase toricPoint tateCurve_pointX_C_eq_tateToricPoint_fst tateCurve_pointY_C_eq_tateToricPoint_snd tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd tateCurve_curve_X_pow_eq_tateBase equation_tateBase_nonToricPoint"
namespace P2MSlotAdd
p2m_open "ModularCurve"

open scoped LaurentSeries.XAdic HahnSeries.XAdicRatSlot NNReal
open HahnSeries.XAdicRatSlot TateCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
variable (F : Type u) [Field F] (M : ℕ) [NeZero M]

theorem point_some_congr {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x x' y y' : R}
    (hx : x = x') (hy : y = y')
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

abbrev tt : LaurentSeries F := HahnSeries.single (1 : ℤ) (1 : F)

theorem curve_eq : TateCurve.curve (tt F ^ M) = tateBase F M :=
  ModularCurve.tateCurve_curve_X_pow_eq_tateBase F M

theorem pointX_C_eq (c : Fˣ) (hc1 : (c : F) ≠ 1) :
    TateCurve.pointX (tt F ^ M) (HahnSeries.C (c : F)) = (toricPoint F M (c : F)).1 := by
  rw [show TateCurve.pointX (tt F ^ M) (HahnSeries.C (c : F)) = _ from
    ModularCurve.tateCurve_pointX_C_eq_tateToricPoint_fst F M c hc1, tateToricPoint_eq_toricPoint]

theorem pointY_C_eq (c : Fˣ) (hc1 : (c : F) ≠ 1) :
    TateCurve.pointY (tt F ^ M) (HahnSeries.C (c : F)) = (toricPoint F M (c : F)).2 := by
  rw [show TateCurve.pointY (tt F ^ M) (HahnSeries.C (c : F)) = _ from
    ModularCurve.tateCurve_pointY_C_eq_tateToricPoint_snd F M c hc1, tateToricPoint_eq_toricPoint]

theorem pointX_C_mul_eq (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    TateCurve.pointX (tt F ^ M) (HahnSeries.C (c : F) * tt F ^ j) = (nonToricPoint F M c j).1 :=
  ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst F M c j hj hjM

theorem pointY_C_mul_eq (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    TateCurve.pointY (tt F ^ M) (HahnSeries.C (c : F) * tt F ^ j) = (nonToricPoint F M c j).2 :=
  ModularCurve.tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd F M c j hj hjM

theorem tt_pow_ne_zero (n : ℕ) : tt F ^ n ≠ 0 := LaurentSeries.XAdic.X_pow_ne_zero F n

theorem nnnorm_q_lt_one : ‖tt F ^ M‖₊ < 1 := LaurentSeries.XAdic.nnnorm_X_pow_lt_one F (NeZero.ne M)

theorem C_ne_zero (c : Fˣ) : (HahnSeries.C (c : F) : LaurentSeries F) ≠ 0 := fun h =>
  c.ne_zero (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))

theorem C_mul_ne_zero (c : Fˣ) (j : ℕ) : (HahnSeries.C (c : F) * tt F ^ j : LaurentSeries F) ≠ 0 :=
  mul_ne_zero (C_ne_zero F c) (tt_pow_ne_zero F j)

theorem nonsingular_C_mul (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) (HahnSeries.C (c : F) * tt F ^ j))
      (pointY (tt F ^ M) (HahnSeries.C (c : F) * tt F ^ j)) := by
  rw [curve_eq, pointX_C_mul_eq F M c j hj hjM, pointY_C_mul_eq F M c j hj hjM]
  exact equation_iff_nonsingular.mp (ModularCurve.equation_tateBase_nonToricPoint F M c j hj hjM)

variable [CharZero F]

theorem nonsingular_C (c : Fˣ) (hc1 : (c : F) ≠ 1) :
    (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) (HahnSeries.C (c : F)))
      (pointY (tt F ^ M) (HahnSeries.C (c : F))) := by
  haveI : CharZero (LaurentSeries F) := LaurentSeries.XAdic.charZero F
  have hq1 : ‖tt F ^ M‖ < 1 := by exact_mod_cast nnnorm_q_lt_one F M
  have hC1 : (HahnSeries.C (c : F) : LaurentSeries F) ≠ 1 := fun h =>
    hc1 (HahnSeries.C_injective (h.trans HahnSeries.C_one.symm))
  exact nonsingular_point (tt_pow_ne_zero F M) (nnnorm_q_lt_one F M) (C_ne_zero F c)
    (offLattice_of_norm_eq_one (tt_pow_ne_zero F M) hq1 (LaurentSeries.XAdicSlot.norm_C_eq_one c.ne_zero) hC1)

theorem addX_slope_map {L : Type*} [Field L] [DecidableEq (LaurentSeries F)] [DecidableEq L]
    (W : WeierstrassCurve (LaurentSeries F)) (f : LaurentSeries F →+* L)
    (x₁ x₂ y₁ y₂ : LaurentSeries F) :
    (W.map f).toAffine.addX (f x₁) (f x₂) ((W.map f).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂))
      = f (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) := by
  rw [map_slope, map_addX]

theorem addY_slope_map {L : Type*} [Field L] [DecidableEq (LaurentSeries F)] [DecidableEq L]
    (W : WeierstrassCurve (LaurentSeries F)) (f : LaurentSeries F →+* L)
    (x₁ x₂ y₁ y₂ : LaurentSeries F) :
    (W.map f).toAffine.addY (f x₁) (f x₂) (f y₁)
        ((W.map f).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂))
      = f (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) := by
  rw [map_slope, map_addY]

theorem add_of_emb [DecidableEq (LaurentSeries F)] {u₁ u₂ : LaurentSeries F}
    (hu₁0 : u₁ ≠ 0) (hu₂0 : u₂ ≠ 0)
    (n₁ : ‖laurentEmb (algebraMap F (AlgebraicClosure F)) u₁‖ ≤ 1)
    (n₂ : ‖laurentEmb (algebraMap F (AlgebraicClosure F)) u₂‖ ≤ 1)
    (n₁₂ : ‖laurentEmb (algebraMap F (AlgebraicClosure F)) (tt F ^ M)‖
      < ‖laurentEmb (algebraMap F (AlgebraicClosure F)) u₁
          * laurentEmb (algebraMap F (AlgebraicClosure F)) u₂‖)
    (e₁ : laurentEmb (algebraMap F (AlgebraicClosure F)) u₁ ≠ 1)
    (e₂ : laurentEmb (algebraMap F (AlgebraicClosure F)) u₂ ≠ 1)
    (e₁₂ : laurentEmb (algebraMap F (AlgebraicClosure F)) u₁
      * laurentEmb (algebraMap F (AlgebraicClosure F)) u₂ ≠ 1)
    (h₁ : (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) (u₁ * u₂))
      (pointY (tt F ^ M) (u₁ * u₂)))
    (h₂ : (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) u₁) (pointY (tt F ^ M) u₁))
    (h₃ : (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) u₂) (pointY (tt F ^ M) u₂)) :
    (Point.some _ _ h₁ : (curve (tt F ^ M)).toAffine.Point) = Point.some _ _ h₂ + Point.some _ _ h₃ := by
  set q : LaurentSeries F := tt F ^ M with hqdef
  haveI : CharZero (LaurentSeries F) := LaurentSeries.XAdic.charZero F
  have hq0 : q ≠ 0 := tt_pow_ne_zero F M
  have hqn : ‖q‖₊ < 1 := nnnorm_q_lt_one F M

  let Fb : Type u := AlgebraicClosure F
  let ι : LaurentSeries F →+* HahnSeries ℚ Fb := laurentEmb (algebraMap F Fb)
  haveI : IsAlgClosed (HahnSeries ℚ Fb) := HahnSeries.isAlgClosed_rat
  haveI : CharZero (HahnSeries ℚ Fb) :=
    charZero_of_injective_ringHom (f := (HahnSeries.C : Fb →+* HahnSeries ℚ Fb))
      HahnSeries.C_injective
  set qH : HahnSeries ℚ Fb := ι q with hqH
  have hqHt : qH = HahnSeries.single (M : ℚ) (1 : Fb) := by
    rw [hqH]
    show laurentEmb (algebraMap F Fb) (tt F ^ M) = _
    rw [map_pow, laurentEmb_single, map_one, Int.cast_one, HahnSeries.single_pow, one_pow]
    simp
  have hqH0 : qH ≠ 0 := (map_ne_zero ι).mpr hq0
  have hqHn : ‖qH‖₊ < 1 := by
    have h : ‖qH‖ < 1 := by
      rw [norm_lt_one_iff, hqHt, HahnSeries.orderTop_single one_ne_zero]
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    exact_mod_cast h

  have hX : ∀ {a : LaurentSeries F}, a ≠ 0 → ι (pointX q a) = pointX qH (ι a) := fun ha => by
    rw [hqH]; exact laurentEmb_pointX _ hq0 hqn ha
  have hY : ∀ {a : LaurentSeries F}, a ≠ 0 → ι (pointY q a) = pointY qH (ι a) := fun ha => by
    rw [hqH]; exact laurentEmb_pointY _ hq0 hqn ha
  have hcurve : (curve q).map ι = curve qH := by rw [hqH]; exact curve_map_laurentEmb _ hqn
  have hιinj : Function.Injective ι := ι.injective

  have hns : ∀ {a : LaurentSeries F}, a ≠ 0 →
      (curve q).toAffine.Nonsingular (pointX q a) (pointY q a) →
      (curve qH).toAffine.Nonsingular (pointX qH (ι a)) (pointY qH (ι a)) := by
    intro a ha h
    have h2 : ((curve q).map ι).toAffine.Nonsingular (ι (pointX q a)) (ι (pointY q a)) :=
      (Affine.map_nonsingular (curve q) hιinj (pointX q a) (pointY q a)).mpr h
    rw [hcurve, hX ha, hY ha] at h2
    exact h2
  have hu0 : u₁ * u₂ ≠ 0 := mul_ne_zero hu₁0 hu₂0
  have hmul : ι (u₁ * u₂) = ι u₁ * ι u₂ := map_mul ι u₁ u₂
  have hns1 : (curve qH).toAffine.Nonsingular (pointX qH (ι u₁ * ι u₂)) (pointY qH (ι u₁ * ι u₂)) := by
    rw [← hmul]; exact hns hu0 h₁
  have hn12 : ‖qH‖ < ‖ι u₁ * ι u₂‖ := n₁₂

  have hsum := TateCurve.point_mul_eq_add_of_norm_le_one hqH0 hqHn n₁ n₂ hn12 e₁ e₂ e₁₂ hns1
    (hns hu₁0 h₂) (hns hu₂0 h₃)

  have hxyH : ¬(pointX qH (ι u₁) = pointX qH (ι u₂) ∧
      pointY qH (ι u₁) = (curve qH).toAffine.negY (pointX qH (ι u₂)) (pointY qH (ι u₂))) := by
    rintro ⟨hx, hy⟩
    rw [Point.add_of_Y_eq hx hy] at hsum
    exact Point.some_ne_zero _ hsum
  rw [Point.add_some hxyH] at hsum
  simp only [Point.some.injEq] at hsum
  obtain ⟨hxH, hyH⟩ := hsum

  set x₁ := pointX q u₁ with hx₁
  set y₁ := pointY q u₁ with hy₁
  set x₂ := pointX q u₂ with hx₂
  set y₂ := pointY q u₂ with hy₂
  have hxyF : ¬(x₁ = x₂ ∧ y₁ = (curve q).toAffine.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    apply hxyH
    refine ⟨?_, ?_⟩
    · rw [← hX hu₁0, ← hX hu₂0, ← hx₁, ← hx₂, hx]
    · rw [← hY hu₁0, ← hX hu₂0, ← hY hu₂0, ← hy₁, ← hx₂, ← hy₂, hy, ← hcurve, map_negY]
  have hx3 : pointX q (u₁ * u₂)
      = (curve q).toAffine.addX x₁ x₂ ((curve q).toAffine.slope x₁ x₂ y₁ y₂) := by
    apply hιinj
    rw [hX hu0, hmul, hxH, ← hX hu₁0, ← hX hu₂0, ← hY hu₁0, ← hY hu₂0, ← hcurve, addX_slope_map]
  have hy3 : pointY q (u₁ * u₂)
      = (curve q).toAffine.addY x₁ x₂ y₁ ((curve q).toAffine.slope x₁ x₂ y₁ y₂) := by
    apply hιinj
    rw [hY hu0, hmul, hyH, ← hX hu₁0, ← hX hu₂0, ← hY hu₁0, ← hY hu₂0, ← hcurve, addY_slope_map]
  rw [Point.add_some hxyF]
  exact point_some_congr hx3 hy3 _ _

theorem norm_emb_C (a : Fˣ) :
    ‖laurentEmb (algebraMap F (AlgebraicClosure F)) (HahnSeries.C (a : F) : LaurentSeries F)‖ = 1 := by
  rw [laurentEmb_C]
  exact norm_C_eq_one ((map_ne_zero (algebraMap F (AlgebraicClosure F))).mpr a.ne_zero)

theorem norm_emb_tt_lt_one :
    ‖laurentEmb (algebraMap F (AlgebraicClosure F)) (tt F)‖ < 1 := by
  rw [show laurentEmb (algebraMap F (AlgebraicClosure F)) (tt F) = HahnSeries.single (1 : ℚ) 1 by
    rw [laurentEmb_single, map_one, Int.cast_one], norm_lt_one_iff, HahnSeries.orderTop_single one_ne_zero]
  exact_mod_cast one_pos

theorem norm_emb_tt_pos :
    0 < ‖laurentEmb (algebraMap F (AlgebraicClosure F)) (tt F)‖ :=
  norm_pos_iff.mpr ((map_ne_zero _).mpr (by simpa using tt_pow_ne_zero F 1))

theorem emb_C_ne_one (c : Fˣ) (hc1 : (c : F) ≠ 1) :
    laurentEmb (algebraMap F (AlgebraicClosure F)) (HahnSeries.C (c : F) : LaurentSeries F) ≠ 1 := by
  rw [laurentEmb_C]
  intro h
  apply hc1
  have h2 := HahnSeries.C_injective (h.trans HahnSeries.C_one.symm)
  exact (algebraMap F (AlgebraicClosure F)).injective (h2.trans (map_one _).symm)

theorem ne_one_of_norm_lt_one {L : Type*} [NormedField L] {a : L} (h : ‖a‖ < 1) : a ≠ 1 := by
  intro h1; rw [h1, norm_one] at h; exact lt_irrefl _ h

theorem clause1 [DecidableEq (LaurentSeries F)] (c d : Fˣ) (j : ℕ) (hc1 : (c : F) ≠ 1)
    (hj : 0 < j) (hjM : j < M) :
    ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2)
      (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
      (hcd : (tateBase F M).toAffine.Nonsingular
        (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2),
      (Point.some (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2 hc :
          (tateBase F M).toAffine.Point)
        + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
        = Point.some (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2 hcd := by
  set ι := laurentEmb (F := F) (algebraMap F (AlgebraicClosure F)) with hι
  set u₁ : LaurentSeries F := HahnSeries.C (c : F) with hu₁
  set u₂ : LaurentSeries F := HahnSeries.C (d : F) * tt F ^ j with hu₂
  have hprod : u₁ * u₂ = HahnSeries.C ((c * d : Fˣ) : F) * tt F ^ j := by
    rw [hu₁, hu₂, Units.val_mul, map_mul, mul_assoc]
  have h₂ := nonsingular_C F M c hc1
  have h₃ := nonsingular_C_mul F M d j hj hjM
  have h₁ : (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) (u₁ * u₂))
      (pointY (tt F ^ M) (u₁ * u₂)) := by
    rw [hprod]; exact nonsingular_C_mul F M (c * d) j hj hjM

  set ρ : ℝ := ‖ι (tt F)‖ with hρ
  have hρ1 : ρ < 1 := norm_emb_tt_lt_one F
  have hρ0 : 0 < ρ := norm_emb_tt_pos F
  have hnu₁ : ‖ι u₁‖ = 1 := norm_emb_C F c
  have hnu₂ : ‖ι u₂‖ = ρ ^ j := by rw [hu₂, map_mul, map_pow, norm_mul, norm_pow, norm_emb_C, one_mul]
  have hnq : ‖ι (tt F ^ M)‖ = ρ ^ M := by rw [map_pow, norm_pow]
  have n₁ : ‖ι u₁‖ ≤ 1 := hnu₁.le
  have n₂ : ‖ι u₂‖ ≤ 1 := by rw [hnu₂]; exact pow_le_one₀ hρ0.le hρ1.le
  have n₁₂ : ‖ι (tt F ^ M)‖ < ‖ι u₁ * ι u₂‖ := by
    rw [hnq, norm_mul, hnu₁, hnu₂, one_mul]; exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hjM
  have e₁ : ι u₁ ≠ 1 := emb_C_ne_one F c hc1
  have hlt₂ : ‖ι u₂‖ < 1 := by rw [hnu₂]; exact pow_lt_one₀ hρ0.le hρ1 (by omega)
  have e₂ : ι u₂ ≠ 1 := ne_one_of_norm_lt_one hlt₂
  have e₁₂ : ι u₁ * ι u₂ ≠ 1 := ne_one_of_norm_lt_one (by rw [norm_mul, hnu₁, one_mul]; exact hlt₂)
  have hsum := add_of_emb F M (C_ne_zero F c) (C_mul_ne_zero F d j) n₁ n₂ n₁₂ e₁ e₂ e₁₂ h₁ h₂ h₃

  have ec : ∀ {W W' : WeierstrassCurve (LaurentSeries F)} (hW : W = W')
      {a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' : LaurentSeries F}
      (ea₁ : a₁ = a₁') (eb₁ : b₁ = b₁') (ea₂ : a₂ = a₂') (eb₂ : b₂ = b₂') (ea₃ : a₃ = a₃') (eb₃ : b₃ = b₃')
      (g₁ : W.toAffine.Nonsingular a₁ b₁) (g₂ : W.toAffine.Nonsingular a₂ b₂)
      (g₃ : W.toAffine.Nonsingular a₃ b₃)
      (h : (Point.some a₃ b₃ g₃ : W.toAffine.Point) = Point.some a₁ b₁ g₁ + Point.some a₂ b₂ g₂),
      ∃ (g₁' : W'.toAffine.Nonsingular a₁' b₁') (g₂' : W'.toAffine.Nonsingular a₂' b₂')
        (g₃' : W'.toAffine.Nonsingular a₃' b₃'),
        (Point.some a₁' b₁' g₁' : W'.toAffine.Point) + Point.some a₂' b₂' g₂' = Point.some a₃' b₃' g₃' := by
    intro W W' hW a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' ea₁ eb₁ ea₂ eb₂ ea₃ eb₃ g₁ g₂ g₃ h
    subst hW ea₁ eb₁ ea₂ eb₂ ea₃ eb₃
    exact ⟨g₁, g₂, g₃, h.symm⟩
  exact ec (curve_eq F M) (pointX_C_eq F M c hc1) (pointY_C_eq F M c hc1)
    (pointX_C_mul_eq F M d j hj hjM) (pointY_C_mul_eq F M d j hj hjM)
    (by rw [hprod]; exact pointX_C_mul_eq F M (c * d) j hj hjM)
    (by rw [hprod]; exact pointY_C_mul_eq F M (c * d) j hj hjM) h₂ h₃ h₁ hsum

theorem clause2 [DecidableEq (LaurentSeries F)] (c d : Fˣ) (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hijM : i + j < M) :
    ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c i).1 (nonToricPoint F M c i).2)
      (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
      (hcd : (tateBase F M).toAffine.Nonsingular
        (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2),
      (Point.some (nonToricPoint F M c i).1 (nonToricPoint F M c i).2 hc :
          (tateBase F M).toAffine.Point)
        + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
        = Point.some (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2
            hcd := by
  set ι := laurentEmb (F := F) (algebraMap F (AlgebraicClosure F)) with hι
  set u₁ : LaurentSeries F := HahnSeries.C (c : F) * tt F ^ i with hu₁
  set u₂ : LaurentSeries F := HahnSeries.C (d : F) * tt F ^ j with hu₂
  have hprod : u₁ * u₂ = HahnSeries.C ((c * d : Fˣ) : F) * tt F ^ (i + j) := by
    rw [hu₁, hu₂, Units.val_mul, map_mul, _root_.pow_add]; ring
  have hiM : i < M := by omega
  have hjM : j < M := by omega
  have h₂ := nonsingular_C_mul F M c i hi hiM
  have h₃ := nonsingular_C_mul F M d j hj hjM
  have h₁ : (curve (tt F ^ M)).toAffine.Nonsingular (pointX (tt F ^ M) (u₁ * u₂))
      (pointY (tt F ^ M) (u₁ * u₂)) := by
    rw [hprod]; exact nonsingular_C_mul F M (c * d) (i + j) (by omega) hijM

  set ρ : ℝ := ‖ι (tt F)‖ with hρ
  have hρ1 : ρ < 1 := norm_emb_tt_lt_one F
  have hρ0 : 0 < ρ := norm_emb_tt_pos F
  have hnu₁ : ‖ι u₁‖ = ρ ^ i := by rw [hu₁, map_mul, map_pow, norm_mul, norm_pow, norm_emb_C, one_mul]
  have hnu₂ : ‖ι u₂‖ = ρ ^ j := by rw [hu₂, map_mul, map_pow, norm_mul, norm_pow, norm_emb_C, one_mul]
  have hnq : ‖ι (tt F ^ M)‖ = ρ ^ M := by rw [map_pow, norm_pow]
  have hlt₁ : ‖ι u₁‖ < 1 := by rw [hnu₁]; exact pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hlt₂ : ‖ι u₂‖ < 1 := by rw [hnu₂]; exact pow_lt_one₀ hρ0.le hρ1 (by omega)
  have n₁₂ : ‖ι (tt F ^ M)‖ < ‖ι u₁ * ι u₂‖ := by
    rw [hnq, norm_mul, hnu₁, hnu₂, ← _root_.pow_add]; exact pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hijM
  have e₁ : ι u₁ ≠ 1 := ne_one_of_norm_lt_one hlt₁
  have e₂ : ι u₂ ≠ 1 := ne_one_of_norm_lt_one hlt₂
  have e₁₂ : ι u₁ * ι u₂ ≠ 1 :=
    ne_one_of_norm_lt_one (by rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt₁ hlt₂.le)
  have hsum := add_of_emb F M (C_mul_ne_zero F c i) (C_mul_ne_zero F d j) hlt₁.le hlt₂.le n₁₂ e₁ e₂
    e₁₂ h₁ h₂ h₃
  have ec : ∀ {W W' : WeierstrassCurve (LaurentSeries F)} (hW : W = W')
      {a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' : LaurentSeries F}
      (ea₁ : a₁ = a₁') (eb₁ : b₁ = b₁') (ea₂ : a₂ = a₂') (eb₂ : b₂ = b₂') (ea₃ : a₃ = a₃') (eb₃ : b₃ = b₃')
      (g₁ : W.toAffine.Nonsingular a₁ b₁) (g₂ : W.toAffine.Nonsingular a₂ b₂)
      (g₃ : W.toAffine.Nonsingular a₃ b₃)
      (h : (Point.some a₃ b₃ g₃ : W.toAffine.Point) = Point.some a₁ b₁ g₁ + Point.some a₂ b₂ g₂),
      ∃ (g₁' : W'.toAffine.Nonsingular a₁' b₁') (g₂' : W'.toAffine.Nonsingular a₂' b₂')
        (g₃' : W'.toAffine.Nonsingular a₃' b₃'),
        (Point.some a₁' b₁' g₁' : W'.toAffine.Point) + Point.some a₂' b₂' g₂' = Point.some a₃' b₃' g₃' := by
    intro W W' hW a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' ea₁ eb₁ ea₂ eb₂ ea₃ eb₃ g₁ g₂ g₃ h
    subst hW ea₁ eb₁ ea₂ eb₂ ea₃ eb₃
    exact ⟨g₁, g₂, g₃, h.symm⟩
  exact ec (curve_eq F M) (pointX_C_mul_eq F M c i hi hiM) (pointY_C_mul_eq F M c i hi hiM)
    (pointX_C_mul_eq F M d j hj hjM) (pointY_C_mul_eq F M d j hj hjM)
    (by rw [hprod]; exact pointX_C_mul_eq F M (c * d) (i + j) (by omega) hijM)
    (by rw [hprod]; exact pointY_C_mul_eq F M (c * d) (i + j) (by omega) hijM) h₂ h₃ h₁ hsum

theorem offLattice_C_mul (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    OffLattice (tt F ^ M) (HahnSeries.C (c : F) * tt F ^ j) := by
  intro n hn
  set r : ℝ := ‖tt F‖ with hr
  have hr1 : r < 1 := LaurentSeries.XAdic.norm_X_lt_one F
  have hr0 : 0 < r := norm_pos_iff.mpr (by simpa using tt_pow_ne_zero F 1)
  have hnorm : ‖(tt F ^ M) ^ n * (HahnSeries.C (c : F) * tt F ^ j)‖ = r ^ ((M : ℤ) * n + j) := by
    rw [norm_mul, norm_zpow, norm_pow, norm_mul, norm_pow, LaurentSeries.XAdicSlot.norm_C_eq_one c.ne_zero,
      one_mul, ← hr, zpow_add₀ hr0.ne', zpow_mul, zpow_natCast, zpow_natCast]
  rw [hn, norm_one] at hnorm
  have hinj := zpow_right_injective₀ hr0 hr1.ne (a₁ := (0 : ℤ)) (a₂ := (M : ℤ) * n + j)
    (show r ^ (0 : ℤ) = r ^ ((M : ℤ) * n + j) by rw [zpow_zero]; exact hnorm)
  have hj' : (0 : ℤ) < j := by exact_mod_cast hj
  have hjM' : (j : ℤ) < M := by exact_mod_cast hjM
  rcases lt_trichotomy n 0 with h | h | h
  · nlinarith
  · rw [h] at hinj; omega
  · nlinarith

theorem clause3 [DecidableEq (LaurentSeries F)] (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c j).1 (nonToricPoint F M c j).2)
      (hc' : (tateBase F M).toAffine.Nonsingular
        (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2),
      (Point.some (nonToricPoint F M c j).1 (nonToricPoint F M c j).2 hc :
          (tateBase F M).toAffine.Point)
        + Point.some (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2 hc'
        = 0 := by
  haveI : CharZero (LaurentSeries F) := LaurentSeries.XAdic.charZero F
  set q : LaurentSeries F := tt F ^ M with hqdef
  have hq0 : q ≠ 0 := tt_pow_ne_zero F M
  have hqn : ‖q‖₊ < 1 := nnnorm_q_lt_one F M
  set u : LaurentSeries F := HahnSeries.C (c : F) * tt F ^ j with hu
  set u' : LaurentSeries F := HahnSeries.C ((c⁻¹ : Fˣ) : F) * tt F ^ (M - j) with hu'
  have hu0 : u ≠ 0 := C_mul_ne_zero F c j
  have hoff : OffLattice q u := offLattice_C_mul F M c j hj hjM
  have hMj : 0 < M - j := by omega
  have hMjM : M - j < M := by omega

  have hqu : q * u⁻¹ = u' := by
    have ht0 : (tt F : LaurentSeries F) ≠ 0 := by simpa using tt_pow_ne_zero F 1
    rw [hqdef, hu, hu', mul_inv, ← map_inv₀, Units.val_inv_eq_inv_val,
      show (M : ℕ) = (M - j) + j by omega, _root_.pow_add]
    field_simp
    ring_nf
    rw [Nat.add_sub_cancel]
  have hXinv : pointX q u⁻¹ = pointX q u' := by rw [← hqu, pointX_q_mul hq0]
  have hYinv : pointY q u⁻¹ = pointY q u' := by
    rw [← hqu, show q * u⁻¹ = q ^ (1 : ℤ) * u⁻¹ by rw [zpow_one], pointY_zpow_mul hq0]
  have h₂ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u) := nonsingular_C_mul F M c j hj hjM
  have h₁' : (curve q).toAffine.Nonsingular (pointX q u') (pointY q u') :=
    nonsingular_C_mul F M c⁻¹ (M - j) hMj hMjM
  have h₁ : (curve q).toAffine.Nonsingular (pointX q u⁻¹) (pointY q u⁻¹) := by
    rw [hXinv, hYinv]; exact h₁'
  have hneg := point_inv_eq_neg hq0 hqn hu0 hoff h₁ h₂
  have hsum : (Point.some (pointX q u) (pointY q u) h₂ : (curve q).toAffine.Point)
      + Point.some (pointX q u') (pointY q u') h₁' = 0 := by
    rw [show (Point.some (pointX q u') (pointY q u') h₁' : (curve q).toAffine.Point)
        = Point.some (pointX q u⁻¹) (pointY q u⁻¹) h₁ from point_some_congr hXinv.symm hYinv.symm _ _,
      hneg, add_neg_cancel]
  have ec : ∀ {W W' : WeierstrassCurve (LaurentSeries F)} (hW : W = W')
      {a₁ b₁ a₂ b₂ a₁' b₁' a₂' b₂' : LaurentSeries F}
      (ea₁ : a₁ = a₁') (eb₁ : b₁ = b₁') (ea₂ : a₂ = a₂') (eb₂ : b₂ = b₂')
      (g₁ : W.toAffine.Nonsingular a₁ b₁) (g₂ : W.toAffine.Nonsingular a₂ b₂)
      (h : (Point.some a₁ b₁ g₁ : W.toAffine.Point) + Point.some a₂ b₂ g₂ = 0),
      ∃ (g₁' : W'.toAffine.Nonsingular a₁' b₁') (g₂' : W'.toAffine.Nonsingular a₂' b₂'),
        (Point.some a₁' b₁' g₁' : W'.toAffine.Point) + Point.some a₂' b₂' g₂' = 0 := by
    intro W W' hW a₁ b₁ a₂ b₂ a₁' b₁' a₂' b₂' ea₁ eb₁ ea₂ eb₂ g₁ g₂ h
    subst hW ea₁ eb₁ ea₂ eb₂
    exact ⟨g₁, g₂, h⟩
  exact ec (curve_eq F M) (pointX_C_mul_eq F M c j hj hjM) (pointY_C_mul_eq F M c j hj hjM)
    (pointX_C_mul_eq F M c⁻¹ (M - j) hMj hMjM) (pointY_C_mul_eq F M c⁻¹ (M - j) hMj hMjM) h₂ h₁' hsum

theorem main [DecidableEq (LaurentSeries F)] :
    (∀ (c d : Fˣ) (j : ℕ), (c : F) ≠ 1 → 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2),
        (Point.some (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2 hcd) ∧
    (∀ (c d : Fˣ) (i j : ℕ), 0 < i → 0 < j → i + j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c i).1 (nonToricPoint F M c i).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2),
        (Point.some (nonToricPoint F M c i).1 (nonToricPoint F M c i).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2
              hcd) ∧
    (∀ (c : Fˣ) (j : ℕ), 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c j).1 (nonToricPoint F M c j).2)
        (hc' : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2),
        (Point.some (nonToricPoint F M c j).1 (nonToricPoint F M c j).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2 hc'
          = 0) :=
  ⟨fun c d j hc1 hj hjM => clause1 F M c d j hc1 hj hjM,
   fun c d i j hi hj hijM => clause2 F M c d i j hi hj hijM,
   fun c j hj hjM => clause3 F M c j hj hjM⟩

end ModularCurve.P2MSlotAdd
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"

end
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.HahnSeries.XAdicRatSlot"

p2m_open "ModularCurve P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"

universe u in
theorem solution
    (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)] (M : ℕ) [NeZero M] :
    (∀ (c d : Fˣ) (j : ℕ), (c : F) ≠ 1 → 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2),
        (Point.some (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2 hcd) ∧
    (∀ (c d : Fˣ) (i j : ℕ), 0 < i → 0 < j → i + j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c i).1 (nonToricPoint F M c i).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2),
        (Point.some (nonToricPoint F M c i).1 (nonToricPoint F M c i).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2
              hcd) ∧
    (∀ (c : Fˣ) (j : ℕ), 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c j).1 (nonToricPoint F M c j).2)
        (hc' : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2),
        (Point.some (nonToricPoint F M c j).1 (nonToricPoint F M c j).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2 hc'
          = 0) :=
  ModularCurve.P2MSlotAdd.main F M

end S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
end P2MW
export P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero (solution)
