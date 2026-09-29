-- Prove2me | solution 1 for ModularCurve.exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e9ff957b-3499-5ef6-a32d-0dea4157cfb4

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped MatrixGroups

noncomputable section

namespace GNormSol

open ModularCurve HahnSeries IntermediateField UpperHalfPlane

section IntSeries

variable {R S : Type*} [CommRing R] [CommRing S]

def intSer (R : Type*) [CommRing R] : PowerSeries ℤ →+* LaurentSeries R :=
  (HahnSeries.ofPowerSeries ℤ R).comp (PowerSeries.map (Int.castRingHom R))

theorem intSer_apply (R : Type*) [CommRing R] (p : PowerSeries ℤ) :
    intSer R p = HahnSeries.ofPowerSeries ℤ R (p.map (Int.castRingHom R)) := rfl

theorem intSeriesC_eq_intSer (K : Type*) [Field K] (p : PowerSeries ℤ) : intSeriesC K p = intSer K p := rfl

theorem coeffMap_intSer (f : R →+* S) (p : PowerSeries ℤ) : coeffMap f (intSer R p) = intSer S p := by
  ext m
  simp only [coeffMap_coeff, intSer_apply, PowerSeries.coeff_coe]
  split_ifs
  · simp
  · simp [PowerSeries.coeff_map]

theorem intSer_coeff_mem_range (p : PowerSeries ℤ) (m : ℤ) : (intSer R p).coeff m ∈ Set.range (Int.cast : ℤ → R) := by
  rw [← coeffMap_intSer (Int.castRingHom R) p, coeffMap_coeff]
  exact ⟨_, rfl⟩

theorem intSer_X_mul_coeff_one {u : PowerSeries ℤ} (hu : PowerSeries.constantCoeff u = 1) :
    (intSer R (PowerSeries.X * u)).coeff 1 = 1 := by
  rw [intSer_apply, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, map_one]

theorem intSer_coeff_zero {u : PowerSeries ℤ} (hu : PowerSeries.constantCoeff u = 1) : (intSer R u).coeff 0 = 1 := by
  rw [intSer_apply, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, map_one]

theorem intSer_X_mul_ne_zero [Nontrivial R] {u : PowerSeries ℤ} (hu : PowerSeries.constantCoeff u = 1) :
    intSer R (PowerSeries.X * u) ≠ 0 := by
  intro h
  have := intSer_X_mul_coeff_one (R := R) hu
  rw [h, HahnSeries.coeff_zero] at this
  exact zero_ne_one this

theorem intSer_ne_zero_of_constantCoeff [Nontrivial R] {u : PowerSeries ℤ} (hu : PowerSeries.constantCoeff u = 1) :
    intSer R u ≠ 0 := by
  intro h
  have := intSer_coeff_zero (R := R) hu
  rw [h, HahnSeries.coeff_zero] at this
  exact zero_ne_one this

end IntSeries

section Primitive

variable {L : Type*} [Field L]

def IsZBounded (x : LaurentSeries L) : Prop :=
  ∃ N : Submodule ℤ L, N.FG ∧ ∀ k : ℤ, x.coeff k ∈ N

theorem isZBounded_zero : IsZBounded (0 : LaurentSeries L) :=
  ⟨⊥, Submodule.fg_bot, fun k => by simp⟩

theorem isZBounded_intSer (p : PowerSeries ℤ) : IsZBounded (intSer L p) := by
  refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span_singleton _, fun k => ?_⟩
  obtain ⟨n, hn⟩ := intSer_coeff_mem_range (R := L) p k
  rw [← hn, show ((n : ℤ) : L) = n • (1 : L) by simp]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem isZBounded_single (k : ℤ) (c : L) : IsZBounded (HahnSeries.single k c) := by
  refine ⟨Submodule.span ℤ {c}, Submodule.fg_span_singleton _, fun m => ?_⟩
  rcases eq_or_ne m k with rfl | hm
  · rw [HahnSeries.coeff_single_same]; exact Submodule.subset_span rfl
  · rw [HahnSeries.coeff_single_of_ne hm]; exact zero_mem _

theorem IsZBounded.add {x y : LaurentSeries L} (hx : IsZBounded x) (hy : IsZBounded y) : IsZBounded (x + y) := by
  obtain ⟨N, hN, hxN⟩ := hx
  obtain ⟨N', hN', hyN⟩ := hy
  exact ⟨N ⊔ N', hN.sup hN', fun k => by
    rw [HahnSeries.coeff_add]
    exact add_mem (Submodule.mem_sup_left (hxN k)) (Submodule.mem_sup_right (hyN k))⟩

theorem IsZBounded.mul {x y : LaurentSeries L} (hx : IsZBounded x) (hy : IsZBounded y) : IsZBounded (x * y) := by
  obtain ⟨N, hN, hxN⟩ := hx
  obtain ⟨N', hN', hyN⟩ := hy
  refine ⟨N * N', hN.mul hN', fun k => ?_⟩
  rw [HahnSeries.coeff_mul]
  exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (hxN _) (hyN _)

theorem IsZBounded.smul {x : LaurentSeries L} (hx : IsZBounded x) (c : L) : IsZBounded (c • x) := by
  rw [← HahnSeries.C_mul_eq_smul, HahnSeries.C_apply]
  exact (isZBounded_single 0 c).mul hx

variable (A : ValuationSubring L)

def leOneSubmodule (c : L) : Submodule ℤ L where
  carrier := {z | A.valuation (c⁻¹ * z) ≤ 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at ha hb ⊢
    exact A.valuation.map_add_le ha hb
  smul_mem' n a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_eq_mul, mul_left_comm, map_mul]
    have hn : A.valuation (n : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A n)
    calc A.valuation (n : L) * A.valuation (c⁻¹ * a) ≤ 1 * A.valuation (c⁻¹ * a) := mul_le_mul_left hn _
      _ = A.valuation (c⁻¹ * a) := one_mul _
      _ ≤ 1 := ha

def ltOneSubmodule (c : L) : Submodule ℤ L where
  carrier := {z | A.valuation (c⁻¹ * z) < 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at ha hb ⊢
    exact A.valuation.map_add_lt ha hb
  smul_mem' n a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [zsmul_eq_mul, mul_left_comm, map_mul]
    have hn : A.valuation (n : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A n)
    calc A.valuation (n : L) * A.valuation (c⁻¹ * a) ≤ 1 * A.valuation (c⁻¹ * a) := mul_le_mul_left hn _
      _ = A.valuation (c⁻¹ * a) := one_mul _
      _ < 1 := ha

theorem fg_of_le {N P : Submodule ℤ L} (hN : N.FG) (h : P ≤ N) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian N hN
  have h1 : (Submodule.comap N.subtype P).FG := IsNoetherian.noetherian _
  have h2 := h1.map N.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr h] at h2

theorem exists_eq_C_mul_coeffMap_of_isZBounded {x : LaurentSeries L} (hx : IsZBounded x) (hx0 : x ≠ 0) :
    ∃ (c : L) (y : LaurentSeries A), c ≠ 0 ∧ x = HahnSeries.C c * coeffMap A.subtype y ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 := by
  classical
  obtain ⟨N, hN, hxN⟩ := hx

  set N' : Submodule ℤ L := Submodule.span ℤ (Set.range x.coeff) with hN'
  have hle : N' ≤ N := Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hxN k)
  obtain ⟨s, hs⟩ := fg_of_le hN hle

  have hs0 : (s.filter (· ≠ 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hbot : N' = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      intro z hz
      by_contra hz0
      exact hcon hz hz0
    apply hx0
    ext k
    have hk : x.coeff k ∈ N' := Submodule.subset_span ⟨k, rfl⟩
    rw [hbot, Submodule.mem_bot] at hk
    simpa using hk

  obtain ⟨c, hcs, hcmax⟩ := Finset.exists_max_image (s.filter (· ≠ 0)) (fun z => A.valuation z) hs0
  have hc0 : c ≠ 0 := (Finset.mem_filter.mp hcs).2
  have hcN' : c ∈ N' := by rw [← hs]; exact Submodule.subset_span (Finset.mem_filter.mp hcs).1

  have hN'le : N' ≤ leOneSubmodule A c := by
    rw [← hs]
    refine Submodule.span_le.mpr fun z hz => ?_
    show A.valuation (c⁻¹ * z) ≤ 1
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have hzv := hcmax z (Finset.mem_filter.mpr ⟨hz, hz0⟩)
      rw [map_mul, map_inv₀]
      have hvc : A.valuation c ≠ 0 := by simpa using hc0
      calc (A.valuation c)⁻¹ * A.valuation z ≤ (A.valuation c)⁻¹ * A.valuation c := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
  have hcoefA : ∀ k : ℤ, c⁻¹ * x.coeff k ∈ A := fun k =>
    (A.valuation_le_one_iff _).mp (hN'le (Submodule.subset_span ⟨k, rfl⟩))

  let y : LaurentSeries A :=
    { coeff := fun k => ⟨c⁻¹ * x.coeff k, hcoefA k⟩
      isPWO_support' := x.isPWO_support.mono (by
        intro k hk
        rw [HahnSeries.mem_support]
        intro hxk
        apply hk
        exact Subtype.ext (by simp [hxk])) }
  refine ⟨c, y, hc0, ?_, ?_⟩
  · ext k
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul]
    show x.coeff k = c * (c⁻¹ * x.coeff k)
    rw [mul_inv_cancel_left₀ hc0]
  · intro hy0
    have hlt : ∀ k : ℤ, A.valuation (c⁻¹ * x.coeff k) < 1 := by
      intro k
      have hk := congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff k) hy0
      simp only [coeffMap_coeff, HahnSeries.coeff_zero, IsLocalRing.residue_eq_zero_iff] at hk
      exact (A.valuation_lt_one_iff _).mp hk
    have hN'lt : N' ≤ ltOneSubmodule A c := Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hlt k)
    have := hN'lt hcN'
    change A.valuation (c⁻¹ * c) < 1 at this
    rw [inv_mul_cancel₀ hc0, map_one] at this
    exact lt_irrefl _ this

end Primitive

section ConstantsTower

variable {L : Type*} [Field L]

theorem C_eq_algebraMap (c : L) : HahnSeries.C c = algebraMap L (LaurentSeries L) c := by
  rw [HahnSeries.C_apply, ModularCurve.algebraMap_laurentSeries_eq_single]

end ConstantsTower

section Weights

variable (Γ : Subgroup SL(2, ℤ)) (L : Type*) [Field L]

local notation "Γᴳ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def wtGen (w : ℤ) : Set (LaurentSeries L) :=
  {z | ∃ (g : ModularForm Γᴳ w) (p : PowerSeries ℤ), IsIntegralQExp g p ∧ z = intSer L p}

def wtSpan (w : ℤ) : Submodule L (LaurentSeries L) := Submodule.span L (wtGen Γ L w)

variable {Γ L}

theorem intSer_mem_wtGen {w : ℤ} (g : ModularForm Γᴳ w) {p : PowerSeries ℤ} (hp : IsIntegralQExp g p) :
    intSer L p ∈ wtGen Γ L w := ⟨g, p, hp, rfl⟩

theorem one_mem_wtGen : (1 : LaurentSeries L) ∈ wtGen Γ L 0 := by
  refine ⟨1, 1, ?_, by simp⟩
  show IsIntegralQExp (⇑(1 : ModularForm Γᴳ 0)) 1
  rw [ModularForm.one_coe_eq_one]
  exact isIntegralQExp_one

variable (hT : ModularGroup.T ∈ Γ)
include hT

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem isIntegralQExp_mul {a b : ℤ} (f : ModularForm Γᴳ a) (g : ModularForm Γᴳ b) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) : IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
  rw [IsIntegralQExp, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT) f g,
    map_mul, hf, hg]

theorem mul_mem_wtGen {a b : ℤ} {x y : LaurentSeries L} (hx : x ∈ wtGen Γ L a) (hy : y ∈ wtGen Γ L b) :
    x * y ∈ wtGen Γ L (a + b) := by
  obtain ⟨f, pf, hf, rfl⟩ := hx
  obtain ⟨g, pg, hg, rfl⟩ := hy
  exact ⟨f.mul g, pf * pg, isIntegralQExp_mul hT f g hf hg, (map_mul _ _ _).symm⟩

theorem pow_mem_wtGen {a : ℤ} {x : LaurentSeries L} (hx : x ∈ wtGen Γ L a) (n : ℕ) :
    x ^ n ∈ wtGen Γ L (n * a) := by
  induction n with
  | zero => simpa using (one_mem_wtGen (Γ := Γ) (L := L))
  | succ n ih =>
    have h := mul_mem_wtGen hT ih hx
    rw [← pow_succ] at h
    convert h using 2
    push_cast
    ring

theorem intSer_pow_mem_wtGen {a : ℤ} (g : ModularForm Γᴳ a) {p : PowerSeries ℤ} (hp : IsIntegralQExp g p) (n : ℕ) :
    ∃ g' : ModularForm Γᴳ (n * a), IsIntegralQExp g' (p ^ n) := by
  induction n with
  | zero =>
    refine ⟨ModularForm.mcast (by simp) (1 : ModularForm Γᴳ 0), ?_⟩
    show IsIntegralQExp (⇑(1 : ModularForm Γᴳ 0)) (p ^ 0)
    rw [ModularForm.one_coe_eq_one, pow_zero]
    exact isIntegralQExp_one
  | succ n ih =>
    obtain ⟨g', hg'⟩ := ih
    refine ⟨ModularForm.mcast (by push_cast; ring) (g'.mul g), ?_⟩
    show IsIntegralQExp (⇑(g'.mul g)) (p ^ (n + 1))
    rw [pow_succ]
    exact isIntegralQExp_mul hT g' g hg' hp

omit hT in
theorem one_mem_wtSpan : (1 : LaurentSeries L) ∈ wtSpan Γ L 0 := Submodule.subset_span one_mem_wtGen

theorem mul_mem_wtSpan_of_mem_wtGen {a b : ℤ} {x y : LaurentSeries L} (hx : x ∈ wtSpan Γ L a) (hy : y ∈ wtGen Γ L b) :
    x * y ∈ wtSpan Γ L (a + b) := by
  induction hx using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (mul_mem_wtGen hT hz hy)
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]; exact Submodule.smul_mem _ c hu

theorem mul_mem_wtSpan {a b : ℤ} {x y : LaurentSeries L} (hx : x ∈ wtSpan Γ L a) (hy : y ∈ wtSpan Γ L b) :
    x * y ∈ wtSpan Γ L (a + b) := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact mul_mem_wtSpan_of_mem_wtGen hT hx hz
  | zero => rw [mul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]; exact Submodule.smul_mem _ c hu

theorem pow_mem_wtSpan {a : ℤ} {x : LaurentSeries L} (hx : x ∈ wtSpan Γ L a) (n : ℕ) :
    x ^ n ∈ wtSpan Γ L (n * a) := by
  induction n with
  | zero => simpa using (one_mem_wtSpan (Γ := Γ) (L := L))
  | succ n ih =>
    have h := mul_mem_wtSpan hT ih hx
    rw [← pow_succ] at h
    convert h using 2
    push_cast
    ring

omit hT in
theorem isZBounded_of_mem_wtSpan {a : ℤ} {x : LaurentSeries L} (hx : x ∈ wtSpan Γ L a) : IsZBounded x := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, p, hp, rfl⟩ := hz
    exact isZBounded_intSer p
  | zero => exact isZBounded_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

variable (Γ L)

def ratioSubfield : Subfield (LaurentSeries L) where
  carrier := {x | ∃ (w : ℤ) (a b : LaurentSeries L), a ∈ wtSpan Γ L w ∧ b ∈ wtSpan Γ L w ∧ b ≠ 0 ∧ x = a / b}
  mul_mem' := by
    rintro _ _ ⟨w, a, b, ha, hb, hb0, rfl⟩ ⟨w', a', b', ha', hb', hb0', rfl⟩
    exact ⟨w + w', a * a', b * b', mul_mem_wtSpan hT ha ha', mul_mem_wtSpan hT hb hb', mul_ne_zero hb0 hb0',
      (div_mul_div_comm _ _ _ _)⟩
  one_mem' := ⟨0, 1, 1, one_mem_wtSpan, one_mem_wtSpan, one_ne_zero, (div_one 1).symm⟩
  add_mem' := by
    rintro _ _ ⟨w, a, b, ha, hb, hb0, rfl⟩ ⟨w', a', b', ha', hb', hb0', rfl⟩
    refine ⟨w + w', a * b' + b * a', b * b', ?_, mul_mem_wtSpan hT hb hb', mul_ne_zero hb0 hb0', div_add_div _ _ hb0 hb0'⟩
    have h1 := mul_mem_wtSpan hT ha hb'
    have h2 := mul_mem_wtSpan hT hb ha'
    exact add_mem h1 h2
  zero_mem' := ⟨0, 0, 1, zero_mem _, one_mem_wtSpan, one_ne_zero, (zero_div 1).symm⟩
  neg_mem' := by
    rintro _ ⟨w, a, b, ha, hb, hb0, rfl⟩
    exact ⟨w, -a, b, neg_mem ha, hb, hb0, (neg_div b a).symm⟩
  inv_mem' := by
    rintro _ ⟨w, a, b, ha, hb, hb0, rfl⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · exact ⟨0, 0, 1, zero_mem _, one_mem_wtSpan, one_ne_zero, by simp⟩
    · exact ⟨w, b, a, hb, ha, ha0, inv_div a b⟩

def ratioField : IntermediateField L (LaurentSeries L) :=
  (ratioSubfield Γ L hT).toIntermediateField fun c =>
    ⟨0, algebraMap L (LaurentSeries L) c, 1,
      by rw [← C_eq_algebraMap, ← mul_one (HahnSeries.C c), HahnSeries.C_mul_eq_smul]; exact Submodule.smul_mem _ c one_mem_wtSpan,
      one_mem_wtSpan, one_ne_zero, (div_one _).symm⟩

variable {Γ L}

theorem mem_ratioField_iff {x : LaurentSeries L} :
    x ∈ ratioField Γ L hT ↔ ∃ (w : ℤ) (a b : LaurentSeries L), a ∈ wtSpan Γ L w ∧ b ∈ wtSpan Γ L w ∧ b ≠ 0 ∧ x = a / b :=
  Iff.rfl

end Weights

section Containment

variable (Γ : Subgroup SL(2, ℤ)) (L : Type*) [Field L] [Algebra ℚ L]

local notation "Γᴳ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {L} in
theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb L (intSeriesC ℚ p) = intSer L p :=
  coeffMap_intSer (algebraMap ℚ L) p

variable {L} in
theorem coeffMap_algebraMap' {R S : Type*} [Field R] [Field S] (θ : R →+* S) (c : R) :
    coeffMap θ (algebraMap R (LaurentSeries R) c) = algebraMap S (LaurentSeries S) (θ c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single, coeffMap_single]

variable (hT : ModularGroup.T ∈ Γ)
include hT

def ratioField₀ : IntermediateField ℚ (LaurentSeries ℚ) :=
  ((ratioSubfield Γ L hT).comap (coeffEmb L)).toIntermediateField fun c => by
    show coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) ∈ ratioSubfield Γ L hT
    rw [coeffEmb, coeffMap_algebraMap']
    exact (ratioField Γ L hT).algebraMap_mem _

theorem qExpFunctionFieldC_le_ratioField₀ : qExpFunctionFieldC ℚ Γ ≤ ratioField₀ Γ L hT := by
  rw [qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
  rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  show coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ ratioSubfield Γ L hT
  rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  refine ⟨k, intSer L pf, intSer L pg, Submodule.subset_span (intSer_mem_wtGen f hf),
    Submodule.subset_span (intSer_mem_wtGen g hg), ?_, rfl⟩
  intro h0
  apply hg0
  have h1 : coeffEmb L (intSeriesC ℚ pg) = 0 := by rw [coeffEmb_intSeriesC, h0]
  exact (map_eq_zero_iff _ (coeffEmb L).injective).mp h1

theorem laurentBaseChange_le_ratioField : laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤ ratioField Γ L hT := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact qExpFunctionFieldC_le_ratioField₀ Γ L hT hx

theorem div_intSer_mem_laurentBaseChange {w : ℤ} {a : LaurentSeries L} (ha : a ∈ wtSpan Γ L w)
    (g : ModularForm Γᴳ w) {p : PowerSeries ℤ} (hp : IsIntegralQExp g p) (hp0 : intSer L p ≠ 0) :
    a / intSer L p ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
  have hp0' : intSeriesC ℚ p ≠ 0 := by
    intro h0
    apply hp0
    rw [← coeffEmb_intSeriesC, h0, map_zero]
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g', p', hp', rfl⟩ := hz
    have hmem : intSeriesC ℚ p' / intSeriesC ℚ p ∈ qExpFunctionFieldC ℚ Γ := div_mem_qExpFunctionFieldC g' g hp' hp hp0'
    have := coeffEmb_mem_laurentBaseChange L hmem
    rwa [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC] at this
  | zero => rw [zero_div]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_div]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [← HahnSeries.C_mul_eq_smul, mul_div_assoc, C_eq_algebraMap]
    exact mul_mem (IntermediateField.algebraMap_mem _ c) hx

end Containment

section Delta

variable (Γ : Subgroup SL(2, ℤ))

local notation "Γᴳ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def pD : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit

def DeltaΓ : ModularForm Γᴳ 12 := restrictForm (Subgroup.map_le_range _ _) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem isIntegralQExp_DeltaΓ : IsIntegralQExp (⇑(DeltaΓ Γ)) pD := by
  rw [IsIntegralQExp, DeltaΓ, coe_restrictForm]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

variable {R : Type*} [CommRing R]

theorem intSer_pD_mul_inv : intSer R pD * (HahnSeries.single (-1) 1 * intSer R dedekindEtaUnitInv) = 1 := by
  rw [pD, map_mul, intSer_apply R PowerSeries.X, PowerSeries.map_X, HahnSeries.ofPowerSeries_X,
    mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, dedekindEtaUnit_mul_inv, map_one]
  simp

end Delta

section Identity

theorem assembly_identity {K : Type*} [Field K] {a b X Y D Ca Cb Cd : K} {n m wm wp : ℕ}
    (ha : a = Ca * X) (hb : b = Cb * Y) (hb0 : b ≠ 0) (hm : 12 * n = m + 1) (hdn : Cd ^ n * (Ca * Cb ^ m) = 1) :
    a / b * (Cd * (b ^ 12 * D ^ wm / D ^ wp)) ^ n = X * Y ^ m * (D ^ wm * D⁻¹ ^ wp) ^ n := by
  have hE : b ^ 12 * D ^ wm / D ^ wp = b ^ 12 * (D ^ wm * D⁻¹ ^ wp) := by
    rw [div_eq_mul_inv, inv_pow, mul_assoc]
  rw [hE]
  set E := D ^ wm * D⁻¹ ^ wp with hEdef
  have h1 : (Cd * (b ^ 12 * E)) ^ n = Cd ^ n * (b ^ m * b) * E ^ n := by
    rw [mul_pow, mul_pow, ← pow_mul, hm, pow_succ]
    ring
  rw [h1]
  have h2 : a / b * (Cd ^ n * (b ^ m * b) * E ^ n) = a * b ^ m * Cd ^ n * E ^ n := by
    field_simp
  rw [h2, ha, hb, mul_pow]
  linear_combination (X * Y ^ m * E ^ n) * hdn

end Identity

section Assembly

local notation "Qb" => AlgebraicClosure ℚ

variable (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (A : ValuationSubring Qb)

set_option quotPrecheck false
local notation "Γᴳ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "F" => laurentBaseChange Qb (qExpFunctionFieldC ℚ Γ)
local notation "ι" => coeffMap (A.subtype)
local notation "red" => coeffMap (IsLocalRing.residue (↥A))

include hT in
theorem main (n : ℕ) (hn : 0 < n) (f : ↥F) (hf : f ≠ 0) :
    ∃ (h : ↥F) (y : LaurentSeries ↥A), h ≠ 0 ∧ ((f * h ^ n : ↥F) : LaurentSeries Qb) = ι y ∧ red y ≠ 0 := by
  classical

  obtain ⟨w, a, b, ha, hb, hb0, hfab⟩ := (mem_ratioField_iff hT).mp (laurentBaseChange_le_ratioField Γ Qb hT f.2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hf
    exact Subtype.ext (by rw [hfab, zero_div]; rfl)

  obtain ⟨ca, α, hca, haα, hα⟩ := exists_eq_C_mul_coeffMap_of_isZBounded A (isZBounded_of_mem_wtSpan ha) ha0
  obtain ⟨cb, β, hcb, hbβ, hβ⟩ := exists_eq_C_mul_coeffMap_of_isZBounded A (isZBounded_of_mem_wtSpan hb) hb0

  set D : LaurentSeries Qb := intSer Qb pD with hD
  set δ : LaurentSeries ↥A := intSer ↥A pD with hδ
  set δ' : LaurentSeries ↥A := HahnSeries.single (-1) 1 * intSer ↥A dedekindEtaUnitInv with hδ'
  have hDδ : D = ι δ := (coeffMap_intSer _ _).symm
  have hD0 : D ≠ 0 := intSer_X_mul_ne_zero constantCoeff_dedekindEtaUnit
  have hDinv : D⁻¹ = ι δ' := by
    rw [hDδ]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, hδ, hδ', intSer_pD_mul_inv, map_one]
  have hδred : red δ ≠ 0 := by
    rw [hδ, coeffMap_intSer]
    exact intSer_X_mul_ne_zero constantCoeff_dedekindEtaUnit
  have hδ'red : red δ' ≠ 0 := by
    rw [hδ', map_mul, coeffMap_intSer, coeffMap_single, map_one]
    exact mul_ne_zero (by simp) (intSer_ne_zero_of_constantCoeff constantCoeff_dedekindEtaUnitInv)

  set wp : ℕ := w.toNat with hwp
  set wm : ℕ := (-w).toNat with hwm
  have hw : (12 : ℤ) * w + wm * 12 = wp * 12 := by
    have := Int.toNat_sub_toNat_neg w
    rw [← hwp, ← hwm] at this
    linarith

  have hnum : b ^ 12 * D ^ wm ∈ wtSpan Γ Qb ((wp : ℤ) * 12) := by
    have h1 : b ^ 12 ∈ wtSpan Γ Qb ((12 : ℕ) * w) := pow_mem_wtSpan hT hb 12
    have h2 : D ^ wm ∈ wtSpan Γ Qb (wm * 12) :=
      pow_mem_wtSpan hT (Submodule.subset_span (intSer_mem_wtGen (DeltaΓ Γ) (isIntegralQExp_DeltaΓ Γ))) wm
    have h3 := mul_mem_wtSpan hT h1 h2
    push_cast at h3
    rwa [hw] at h3
  obtain ⟨gD, hgD⟩ := intSer_pow_mem_wtGen hT (DeltaΓ Γ) (isIntegralQExp_DeltaΓ Γ) wp
  have hDpow : D ^ wp = intSer Qb (pD ^ wp) := (map_pow _ _ _).symm
  have hDpow0 : intSer Qb (pD ^ wp) ≠ 0 := by rw [← hDpow]; exact pow_ne_zero _ hD0
  have hh₀mem : b ^ 12 * D ^ wm / D ^ wp ∈ F := by
    rw [hDpow]
    exact div_intSer_mem_laurentBaseChange Γ Qb hT hnum gD hgD hDpow0
  have hh₀0 : b ^ 12 * D ^ wm / D ^ wp ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ hD0)) (pow_ne_zero _ hD0)

  obtain ⟨m, hm⟩ : ∃ m : ℕ, 12 * n = m + 1 := ⟨12 * n - 1, by omega⟩

  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((ca * cb ^ m)⁻¹) hn
  have hcacb : ca * cb ^ m ≠ 0 := mul_ne_zero hca (pow_ne_zero _ hcb)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hd
    exact inv_ne_zero hcacb hd.symm

  have hCd : HahnSeries.C d ∈ F := by rw [C_eq_algebraMap]; exact IntermediateField.algebraMap_mem _ d
  refine ⟨⟨HahnSeries.C d * (b ^ 12 * D ^ wm / D ^ wp), mul_mem hCd hh₀mem⟩,
    α * β ^ m * (δ ^ wm * δ' ^ wp) ^ n, ?_, ?_, ?_⟩
  · intro h0
    have := congrArg Subtype.val h0
    simp only [ZeroMemClass.coe_zero, mul_eq_zero] at this
    rcases this with h1 | h2
    · exact hd0 ((map_eq_zero_iff _ (HahnSeries.C_injective)).mp h1)
    · exact hh₀0 h2
  ·
    have hval : ((f * (⟨HahnSeries.C d * (b ^ 12 * D ^ wm / D ^ wp), mul_mem hCd hh₀mem⟩ : ↥F) ^ n : ↥F) :
        LaurentSeries Qb) = (f : LaurentSeries Qb) * (HahnSeries.C d * (b ^ 12 * D ^ wm / D ^ wp)) ^ n := by
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [hval, hfab]
    have hdn : (HahnSeries.C d : LaurentSeries Qb) ^ n *
        (HahnSeries.C ca * (HahnSeries.C cb : LaurentSeries Qb) ^ m) = 1 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, hd, inv_mul_cancel₀ hcacb, map_one]
    rw [assembly_identity (X := ι α) (Y := ι β) (D := D) haα hbβ hb0 hm hdn]
    rw [map_mul, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, ← hDδ, ← hDinv]
  · rw [map_mul, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow]
    exact mul_ne_zero (mul_ne_zero hα (pow_ne_zero _ hβ)) (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hδred) (pow_ne_zero _ hδ'red)))

end Assembly

end GNormSol

end

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (n : ℕ) (hn : 0 < n)
    (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hf : f ≠ 0) :
    ∃ (h : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
      (y : LaurentSeries ↥A),
      h ≠ 0 ∧
      ((f * h ^ n : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
          LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap A.subtype y ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥A) y ≠ 0 :=
  GNormSol.main Γ hT A n hn f hf

end S_ModularCurve_exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_mul_pow_coe_eq_coeffMap_and_coeffMap_residue_ne_zero_laurentBaseChange_qExpFunctionFieldC (solution)
