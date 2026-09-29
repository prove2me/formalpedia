-- Prove2me | solution 1 for ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d0eea085-ee7b-5397-8fb5-60e322260d8c

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Theorems.Thm_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups
p2m_open "IntermediateField AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.ModularCurve PowerSeries"

namespace ModularCurve
p2m_export "ModularCurve" "laurentIntegralPrincipalDivisors LaurentPrincipalGeneratedByIntegral ReductionInputsQExpModL placeReductionQExpModL isPlaceReductionQExpModL_placeReductionQExpModL reductionQExpModL reductionQExpModL_mk IsIntegralQExp isIntegralQExp_one isIntegralQExp_zero intSeriesC intSeriesC_one intSeriesC_mul intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC algebraMap_apply_eq_single coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace GaussQExp
p2m_open "ModularCurve"

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem ι_injective : Function.Injective (ι A) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact h1

theorem ι_eq_zero_iff (x : LaurentSeries A) : ι A x = 0 ↔ x = 0 := by
  rw [← map_zero (ι A)]; exact (ι_injective A).eq_iff

theorem ϖ_eq_zero_iff (y : LaurentSeries A) :
    ϖ A y = 0 ↔ ∀ n, y.coeff n ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)

theorem ι_C (a : A) : ι A (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

theorem ϖ_C (a : A) : ϖ A (HahnSeries.C a) =
    algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext i
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hi
  · exact map_zero φ
  · rw [PowerSeries.coeff_map]

def intSeriesA (p : PowerSeries ℤ) : LaurentSeries A :=
  HahnSeries.ofPowerSeries ℤ A (p.map (Int.castRingHom A))

theorem map_map_intCast {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : PowerSeries ℤ) :
    (p.map (Int.castRingHom R)).map φ = p.map (Int.castRingHom S) := by
  ext n; simp [PowerSeries.coeff_map]

theorem ι_intSeriesA (p : PowerSeries ℤ) : ι A (intSeriesA A p) = intSeriesC L p := by
  rw [intSeriesA, coeffMap_ofPowerSeries, map_map_intCast]; rfl

theorem ϖ_intSeriesA (p : PowerSeries ℤ) :
    ϖ A (intSeriesA A p) = intSeriesC (IsLocalRing.ResidueField A) p := by
  rw [intSeriesA, coeffMap_ofPowerSeries, map_map_intCast]; rfl

def IsInt (f : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ f * ι A y = ι A x

variable {A}

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem IsInt.zero : IsInt A (0 : LaurentSeries L) := ⟨0, 1, by simp, by simp⟩

theorem IsInt.one : IsInt A (1 : LaurentSeries L) := ⟨1, 1, by simp, by simp⟩

theorem IsInt.mul {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.add {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f + g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.neg {f : LaurentSeries L} (hf : IsInt A f) : IsInt A (-f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  exact ⟨-x, y, hy, by rw [map_neg, ← h]; ring⟩

theorem IsInt.cross {f : LaurentSeries L} {x y x' y' : LaurentSeries A}
    (h : f * ι A y = ι A x) (h' : f * ι A y' = ι A x') : x * y' = x' * y := by
  apply ι_injective A
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.inv_of {f : LaurentSeries L} {x y : LaurentSeries A} (hx : ϖ A x ≠ 0)
    (h : f * ι A y = ι A x) : f⁻¹ * ι A x = ι A y := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, ι_eq_zero_iff] at h
    exact hx (by rw [h, map_zero])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

end Coeff

section Forms

variable (Γ : Subgroup SL(2, ℤ))

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

def Lam (κ : ℤ) : Set (PowerSeries ℤ) :=
  {p | ∃ f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ, IsIntegralQExp f p}

theorem zero_mem_Lam (κ : ℤ) : (0 : PowerSeries ℤ) ∈ Lam Γ κ :=
  ⟨0, by rw [ModularForm.coe_zero]; exact isIntegralQExp_zero⟩

theorem one_mem_Lam : (1 : PowerSeries ℤ) ∈ Lam Γ 0 :=
  ⟨1, by rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one⟩

variable {Γ}
variable (hT : ModularGroup.T ∈ Γ)
include hT

theorem add_mem_Lam {κ : ℤ} {p p' : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) (hp' : p' ∈ Lam Γ κ) :
    p + p' ∈ Lam Γ κ := by
  obtain ⟨f, hf⟩ := hp
  obtain ⟨g, hg⟩ := hp'
  refine ⟨f + g, ?_⟩
  rw [IsIntegralQExp, map_add, hf, hg, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods Γ hT)]

theorem neg_mem_Lam {κ : ℤ} {p : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) : -p ∈ Lam Γ κ := by
  obtain ⟨f, hf⟩ := hp
  refine ⟨-f, ?_⟩
  rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
  exact (ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods Γ hT) f).symm

theorem mul_mem_Lam {κ μ : ℤ} {p p' : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) (hp' : p' ∈ Lam Γ μ) :
    p * p' ∈ Lam Γ (κ + μ) := by
  obtain ⟨f, hf⟩ := hp
  obtain ⟨g, hg⟩ := hp'
  refine ⟨f.mul g, ?_⟩
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods Γ hT) f g).symm

theorem Lam_saturated {κ : ℤ} (n : ℤ) (p : PowerSeries ℤ) (hn : n ≠ 0) (h : n • p ∈ Lam Γ κ) :
    p ∈ Lam Γ κ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨((n : ℂ)⁻¹) • f, ?_⟩
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [IsIntegralQExp, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods Γ hT), ← hf, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℂ n, smul_smul, inv_mul_cancel₀ hn', one_smul]

def LamSub (κ : ℤ) : AddSubgroup (PowerSeries ℤ) where
  carrier := Lam Γ κ
  zero_mem' := zero_mem_Lam Γ κ
  add_mem' := fun hp hp' => add_mem_Lam hT hp hp'
  neg_mem' := fun hp => neg_mem_Lam hT hp

theorem coe_LamSub (κ : ℤ) : (LamSub hT κ : Set (PowerSeries ℤ)) = Lam Γ κ := rfl

omit hT in

def homSpan (K : Type*) [Field K] (κ : ℤ) : Submodule K (LaurentSeries K) :=
  Submodule.span K (intSeriesC K '' Lam Γ κ)

omit hT in
theorem intSeriesC_mem_homSpan (K : Type*) [Field K] {κ : ℤ} {p : PowerSeries ℤ} (hp : p ∈ Lam Γ κ) :
    intSeriesC K p ∈ homSpan (Γ := Γ) K κ :=
  Submodule.subset_span ⟨p, hp, rfl⟩

theorem mul_intSeriesC_mem_homSpan (K : Type*) [Field K] {κ μ : ℤ} {U : LaurentSeries K}
    (hU : U ∈ homSpan (Γ := Γ) K κ) {n : PowerSeries ℤ} (hn : n ∈ Lam Γ μ) :
    U * intSeriesC K n ∈ homSpan (Γ := Γ) K (κ + μ) := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    rw [← intSeriesC_mul]
    exact intSeriesC_mem_homSpan K (mul_mem_Lam hT hp hn)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ _ hx

theorem mul_mem_homSpan (K : Type*) [Field K] {κ μ : ℤ} {U V : LaurentSeries K}
    (hU : U ∈ homSpan (Γ := Γ) K κ) (hV : V ∈ homSpan (Γ := Γ) K μ) :
    U * V ∈ homSpan (Γ := Γ) K (κ + μ) := by
  induction hV using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact mul_intSeriesC_mem_homSpan hT K hU hp
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]
    exact Submodule.smul_mem _ _ hx

omit hT in
theorem algebraMap_mem_homSpan (K : Type*) [Field K] (c : K) :
    algebraMap K (LaurentSeries K) c ∈ homSpan (Γ := Γ) K 0 := by
  have h1 : algebraMap K (LaurentSeries K) c = c • intSeriesC K 1 := by
    rw [intSeriesC_one, ← HahnSeries.C_mul_eq_smul, mul_one, HahnSeries.C_apply,
      algebraMap_laurentSeries_eq_single]
  rw [h1]
  exact Submodule.smul_mem _ _ (intSeriesC_mem_homSpan K (one_mem_Lam Γ))

omit hT in

def IsFrac (K : Type*) [Field K] (x : LaurentSeries K) : Prop :=
  ∃ (κ : ℤ) (U : LaurentSeries K) (n : PowerSeries ℤ), U ∈ homSpan (Γ := Γ) K κ ∧ n ∈ Lam Γ κ ∧
    intSeriesC K n ≠ 0 ∧ x * intSeriesC K n = U

omit hT in
theorem isFrac_of_mem_intFormRatiosC (K : Type*) [Field K] {x : LaurentSeries K}
    (hx : x ∈ intFormRatiosC K Γ) : IsFrac (Γ := Γ) K x := by
  obtain ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  exact ⟨κ, intSeriesC K pf, pg, intSeriesC_mem_homSpan K ⟨f, hf⟩, ⟨g, hg⟩, hg0,
    div_mul_cancel₀ _ hg0⟩

omit hT in
theorem isFrac_algebraMap (K : Type*) [Field K] (c : K) :
    IsFrac (Γ := Γ) K (algebraMap K (LaurentSeries K) c) :=
  ⟨0, algebraMap K (LaurentSeries K) c, 1, algebraMap_mem_homSpan K c, one_mem_Lam Γ,
    by rw [intSeriesC_one]; exact one_ne_zero, by rw [intSeriesC_one, mul_one]⟩

theorem IsFrac.add (K : Type*) [Field K] {x y : LaurentSeries K} (hx : IsFrac (Γ := Γ) K x)
    (hy : IsFrac (Γ := Γ) K y) : IsFrac (Γ := Γ) K (x + y) := by
  obtain ⟨κ, U, n, hU, hn, hn0, hxU⟩ := hx
  obtain ⟨μ, U', n', hU', hn', hn0', hyU⟩ := hy
  refine ⟨κ + μ, U * intSeriesC K n' + U' * intSeriesC K n, n * n', ?_, mul_mem_Lam hT hn hn', ?_, ?_⟩
  · refine Submodule.add_mem _ (mul_intSeriesC_mem_homSpan hT K hU hn') ?_
    rw [add_comm κ μ]
    exact mul_intSeriesC_mem_homSpan hT K hU' hn
  · rw [intSeriesC_mul]; exact mul_ne_zero hn0 hn0'
  · rw [intSeriesC_mul, add_mul, ← hxU, ← hyU]; ring

theorem IsFrac.mul (K : Type*) [Field K] {x y : LaurentSeries K} (hx : IsFrac (Γ := Γ) K x)
    (hy : IsFrac (Γ := Γ) K y) : IsFrac (Γ := Γ) K (x * y) := by
  obtain ⟨κ, U, n, hU, hn, hn0, hxU⟩ := hx
  obtain ⟨μ, U', n', hU', hn', hn0', hyU⟩ := hy
  refine ⟨κ + μ, U * U', n * n', mul_mem_homSpan hT K hU hU', mul_mem_Lam hT hn hn', ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hn0 hn0'
  · rw [intSeriesC_mul, ← hxU, ← hyU]; ring

theorem isFrac_of_mem_adjoin (K : Type*) [Field K] {x : LaurentSeries K}
    (hx : x ∈ Algebra.adjoin K (intFormRatiosC K Γ)) : IsFrac (Γ := Γ) K x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact isFrac_of_mem_intFormRatiosC K hx
  | algebraMap c => exact isFrac_algebraMap K c
  | add x y _ _ hx hy => exact hx.add hT K hy
  | mul x y _ _ hx hy => exact hx.mul hT K hy

end Forms

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  rw [coeffEmb, intSeriesC, coeffMap_ofPowerSeries, intSeriesC]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffEmb_injective : Function.Injective (coeffEmb L) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ L).injective h1

theorem laurentBaseChange_le :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤ qExpFunctionFieldC L Γ := by
  change adjoin L _ ≤ adjoin L _
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (intFormRatiosC L Γ)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (intFormRatiosC L Γ)).algebraMap_mem _
  · obtain ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hz
    have hgL : intSeriesC L pg ≠ 0 := by
      rw [← coeffEmb_intSeriesC L]
      exact (map_ne_zero_iff _ (coeffEmb_injective L)).mpr hg0
    have : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) = intSeriesC L pf / intSeriesC L pg := by
      rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    rw [this]
    exact IntermediateField.subset_adjoin L _ ⟨κ, f, g, pf, pg, hf, hg, hgL, rfl⟩

end BaseChange

section FracForm

def ofPS (K : Type*) [Field K] : PowerSeries K →ₗ[K] LaurentSeries K where
  toFun := HahnSeries.ofPowerSeries ℤ K
  map_add' := map_add _
  map_smul' := fun c x => by
    rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      RingHom.id_apply]

theorem ofPS_apply (K : Type*) [Field K] (x : PowerSeries K) : ofPS K x = HahnSeries.ofPowerSeries ℤ K x :=
  rfl

theorem intSeriesC_eq_ofPS (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K p = ofPS K (p.map (Int.castRingHom K)) := rfl

variable {Γ : Subgroup SL(2, ℤ)}

theorem homSpan_eq_map (K : Type*) [Field K] (κ : ℤ) :
    homSpan (Γ := Γ) K κ =
      (Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ κ)).map (ofPS K) := by
  rw [homSpan, Submodule.map_span, ← Set.image_comp]
  rfl

theorem div_mem_qExpFunctionFieldC_of_mem_span (K : Type*) [Field K] {μ : ℤ} {X Y : PowerSeries K}
    (hX : X ∈ Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ μ))
    (hY : Y ∈ Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ μ))
    (hY0 : Y ≠ 0) :
    ofPS K X / ofPS K Y ∈ qExpFunctionFieldC K Γ := by
  classical

  obtain ⟨p₀, hp₀, hp₀0⟩ : ∃ p₀ ∈ Lam Γ μ, intSeriesC K p₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hY0
    have hbot : Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ μ) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨p, hp, rfl⟩
      have h := hall p hp
      rw [intSeriesC_eq_ofPS, ofPS_apply] at h
      exact HahnSeries.ofPowerSeries_injective (by rw [h, map_zero])
    rw [hbot] at hY
    exact (Submodule.mem_bot K).mp hY
  obtain ⟨g₀, hg₀⟩ := hp₀

  have key : ∀ Z ∈ Submodule.span K ((fun p : PowerSeries ℤ => p.map (Int.castRingHom K)) '' Lam Γ μ),
      ofPS K Z * (intSeriesC K p₀)⁻¹ ∈ qExpFunctionFieldC K Γ := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, ⟨f, hf⟩, rfl⟩ := hx
      rw [← intSeriesC_eq_ofPS, ← div_eq_mul_inv]
      exact div_mem_qExpFunctionFieldC f g₀ hf hg₀ hp₀0
    | zero => rw [map_zero, zero_mul]; exact IntermediateField.zero_mem _
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact IntermediateField.add_mem _ hx hy
    | smul a x _ hx =>
      rw [PowerSeries.smul_eq_C_mul, ofPS_apply, map_mul, HahnSeries.ofPowerSeries_C, ← ofPS_apply,
        mul_assoc, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
      exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ a) hx
  have hXY : ofPS K X / ofPS K Y =
      (ofPS K X * (intSeriesC K p₀)⁻¹) / (ofPS K Y * (intSeriesC K p₀)⁻¹) := by
    rw [mul_div_mul_right _ _ (inv_ne_zero hp₀0)]
  rw [hXY]
  exact IntermediateField.div_mem _ (key X hX) (key Y hY)

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (hT : ModularGroup.T ∈ Γ)
include hT

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

theorem exists_primitive_of_mem_homSpan {μ : ℤ} {V : LaurentSeries L} (hV : V ∈ homSpan (Γ := Γ) L μ)
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u₀ : LaurentSeries A), c ≠ 0 ∧ V = algebraMap L (LaurentSeries L) c * ι A u₀ ∧
      ϖ A u₀ ≠ 0 ∧ ∃ ub : PowerSeries kk, ϖ A u₀ = ofPS kk ub ∧
        ub ∈ Submodule.span kk ((fun p : PowerSeries ℤ => p.map (Int.castRingHom kk)) '' Lam Γ μ) := by
  rw [homSpan_eq_map] at hV
  obtain ⟨V₀, hV₀, rfl⟩ := hV
  have hV₀0 : V₀ ≠ 0 := by rintro rfl; exact hV0 (map_zero _)
  obtain ⟨c, u, hc0, hVu, hu0, humem⟩ :=
    PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated A (LamSub hT μ)
      (fun n p hn h => Lam_saturated hT n p hn h)
      (V := V₀) hV₀ hV₀0
  refine ⟨c, HahnSeries.ofPowerSeries ℤ A u, hc0, ?_, ?_, u.map (IsLocalRing.residue A), ?_, humem⟩
  · rw [ofPS_apply, hVu, map_mul, HahnSeries.ofPowerSeries_C, coeffMap_ofPowerSeries,
      HahnSeries.C_apply, algebraMap_laurentSeries_eq_single]
  · rw [coeffMap_ofPowerSeries]
    exact fun h => hu0 (HahnSeries.ofPowerSeries_injective (by rw [h, map_zero]))
  · rw [coeffMap_ofPowerSeries]; rfl

theorem exists_frac_form (f : FF) (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ u₀ w₀ : LaurentSeries A, ϖ A u₀ ≠ 0 ∧ ϖ A w₀ ≠ 0 ∧
      (f : LaurentSeries L) * ι A w₀ = algebraMap L (LaurentSeries L) c * ι A u₀ ∧
      ϖ A u₀ / ϖ A w₀ ∈ qExpFunctionFieldC kk Γ := by
  have hfF : (f : LaurentSeries L) ∈ qExpFunctionFieldC L Γ := laurentBaseChange_le L Γ f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨κ, U, n, hU, hn, hn0, hrU⟩ := isFrac_of_mem_adjoin hT L hr
  obtain ⟨μ, U', n', hU', hn', hn0', hsU⟩ := isFrac_of_mem_adjoin hT L hs

  set V : LaurentSeries L := U * intSeriesC L n' with hVdef
  set W : LaurentSeries L := U' * intSeriesC L n with hWdef
  have hVmem : V ∈ homSpan (Γ := Γ) L (κ + μ) := mul_intSeriesC_mem_homSpan hT L hU hn'
  have hWmem : W ∈ homSpan (Γ := Γ) L (κ + μ) := by
    rw [add_comm]; exact mul_intSeriesC_mem_homSpan hT L hU' hn
  have hW0 : W ≠ 0 := by
    rw [hWdef, ← hsU]; exact mul_ne_zero (mul_ne_zero hs0 hn0') hn0
  have hfW : (f : LaurentSeries L) * W = V := by
    rw [hWdef, hVdef, ← hsU, ← hrU, hrs]
    field_simp
  have hV0 : V ≠ 0 := by rw [← hfW]; exact mul_ne_zero hf0' hW0
  obtain ⟨cV, u₀, hcV, hVu, hu0, ub, hub, hubmem⟩ := exists_primitive_of_mem_homSpan A hT hVmem hV0
  obtain ⟨cW, w₀, hcW, hWw, hw0, wb, hwb, hwbmem⟩ := exists_primitive_of_mem_homSpan A hT hWmem hW0
  refine ⟨cV / cW, div_ne_zero hcV hcW, u₀, w₀, hu0, hw0, ?_, ?_⟩
  · have hcW' : algebraMap L (LaurentSeries L) cW ≠ 0 := (map_ne_zero _).mpr hcW
    have h1 : (f : LaurentSeries L) * (algebraMap L (LaurentSeries L) cW * ι A w₀) =
        algebraMap L (LaurentSeries L) cV * ι A u₀ := by rw [← hWw, hfW, hVu]
    rw [map_div₀]
    field_simp
    linear_combination h1
  · rw [hub, hwb]
    have hwb0 : wb ≠ 0 := by rintro rfl; exact hw0 (by rw [hwb, map_zero])
    exact div_mem_qExpFunctionFieldC_of_mem_span kk hubmem hwbmem hwb0

end FracForm

section Gauss

variable {Γ : Subgroup SL(2, ℤ)}
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

def gaussRing : ValuationSubring FF where
  carrier := {f | IsInt A (f : LaurentSeries L)}
  mul_mem' {f g} hf hg := by
    change IsInt A ((f * g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_mul]; exact hf.mul hg
  one_mem' := by change IsInt A ((1 : FF) : LaurentSeries L); exact IsInt.one
  add_mem' {f g} hf hg := by
    change IsInt A ((f + g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_add]; exact hf.add hg
  zero_mem' := by change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
  neg_mem' {f} hf := by
    change IsInt A ((-f : FF) : LaurentSeries L)
    rw [IntermediateField.coe_neg]; exact hf.neg
  mem_or_inv_mem' f := by
    by_cases hf : f = 0
    · left; subst hf; change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
    obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h, -⟩ := exists_frac_form A hT f hf
    rcases A.mem_or_inv_mem c with hc | hc
    · left
      refine ⟨HahnSeries.C ⟨c, hc⟩ * x₀, y₀, hy₀, ?_⟩
      rw [h, map_mul, ι_C]
    · right
      change IsInt A ((f⁻¹ : FF) : LaurentSeries L)
      refine ⟨HahnSeries.C ⟨c⁻¹, hc⟩ * y₀, x₀, hx₀, ?_⟩
      have hf' : (f : LaurentSeries L) ≠ 0 := fun h' => hf (Subtype.ext h')
      rw [IntermediateField.coe_inv, map_mul, ι_C]
      have hcC : algebraMap L (LaurentSeries L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      calc (f : LaurentSeries L)⁻¹ * ι A x₀
          = (f : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) c)⁻¹ *
              ((f : LaurentSeries L) * ι A y₀) := by rw [h]; field_simp
        _ = algebraMap L (LaurentSeries L) (↑(⟨c⁻¹, hc⟩ : A) : L) * ι A y₀ := by
              rw [map_inv₀]; field_simp

theorem mem_gaussRing_iff (f : FF) : f ∈ gaussRing A hT ↔ IsInt A (f : LaurentSeries L) := Iff.rfl

theorem exists_witness (f : gaussRing A hT) :
    ∃ p : LaurentSeries A × LaurentSeries A,
      ϖ A p.2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A p.2 = ι A p.1 := by
  obtain ⟨x, y, hy, h⟩ := f.2
  exact ⟨(x, y), hy, h⟩

def wit (f : gaussRing A hT) : LaurentSeries A × LaurentSeries A :=
  Classical.choose (exists_witness A hT f)

theorem wit_spec (f : gaussRing A hT) :
    ϖ A (wit A hT f).2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A (wit A hT f).2 = ι A (wit A hT f).1 :=
  Classical.choose_spec (exists_witness A hT f)

def resL (f : gaussRing A hT) : LaurentSeries kk :=
  ϖ A (wit A hT f).1 / ϖ A (wit A hT f).2

theorem resL_eq {f : gaussRing A hT} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resL A hT f = ϖ A x / ϖ A y := by
  obtain ⟨hy', h'⟩ := wit_spec A hT f
  have hc := IsInt.cross (A := A) h' h
  rw [resL, div_eq_div_iff hy' hy, ← map_mul, ← map_mul, hc]

def resHom : gaussRing A hT →+* LaurentSeries kk where
  toFun := resL A hT
  map_one' := by
    rw [resL_eq A hT (x := 1) (y := 1) (by simp) (by simp)]; simp
  map_mul' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A hT f
    obtain ⟨hg, hg'⟩ := wit_spec A hT g
    have h : (((f * g : gaussRing A hT) : FF) : LaurentSeries L) * ι A ((wit A hT f).2 * (wit A hT g).2)
        = ι A ((wit A hT f).1 * (wit A hT g).1) := by
      rw [map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A hT (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A hT f * resL A hT g
    rw [resL, resL, map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    rw [resL_eq A hT (x := 0) (y := 1) (by simp) (by simp)]; simp
  map_add' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A hT f
    obtain ⟨hg, hg'⟩ := wit_spec A hT g
    have h : (((f + g : gaussRing A hT) : FF) : LaurentSeries L) * ι A ((wit A hT f).2 * (wit A hT g).2)
        = ι A ((wit A hT f).1 * (wit A hT g).2 + (wit A hT g).1 * (wit A hT f).2) := by
      rw [map_add, map_mul, map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A hT (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A hT f + resL A hT g
    rw [resL, resL, div_add_div _ _ hf hg, map_add, map_mul, map_mul, map_mul]
    ring

theorem resHom_apply (f : gaussRing A hT) : resHom A hT f = resL A hT f := rfl

theorem resHom_eq {f : gaussRing A hT} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resHom A hT f = ϖ A x / ϖ A y :=
  resL_eq A hT hy h

theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) : (⟨ι A y, hyF⟩ : FF) ∈ gaussRing A hT :=
  ⟨y, 1, by simp, by simp⟩

theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A hT ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A hT hyF⟩ = ϖ A y := by
  rw [resHom_eq A hT (x := y) (y := 1) (by simp) (by simp)]; simp

theorem inv_mem_gaussRing_of_resHom_ne_zero (f : gaussRing A hT) (h0 : resHom A hT f ≠ 0) :
    ((f : FF)⁻¹ : FF) ∈ gaussRing A hT := by
  obtain ⟨hy, h⟩ := wit_spec A hT f
  rw [resHom_eq A hT hy h] at h0
  have hx : ϖ A (wit A hT f).1 ≠ 0 := fun hx => h0 (by rw [hx, zero_div])
  refine ⟨(wit A hT f).2, (wit A hT f).1, hx, ?_⟩
  rw [IntermediateField.coe_inv]
  exact IsInt.inv_of (A := A) hx h

theorem resHom_eq_zero_iff (f : gaussRing A hT) :
    resHom A hT f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (gaussRing A hT) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨hy, h⟩ := wit_spec A hT f
  constructor
  · rintro h0 ⟨u, rfl⟩
    have := congrArg (resHom A hT) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hu
    by_contra h0
    apply hu
    have hinv := inv_mem_gaussRing_of_resHom_ne_zero A hT f h0
    rw [resHom_eq A hT hy h, div_eq_zero_iff, or_iff_left hy] at h0
    have hf0 : ((f : FF) : LaurentSeries L) ≠ 0 := by
      intro hf
      rw [hf, zero_mul, eq_comm, ι_eq_zero_iff] at h
      exact h0 (by rw [h, map_zero])
    have hf0' : (f : FF) ≠ 0 := fun h' => hf0 (by rw [h']; rfl)
    exact ⟨⟨f, ⟨(f : FF)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0'),
      Subtype.ext (inv_mul_cancel₀ hf0')⟩, rfl⟩

theorem ker_resHom : RingHom.ker (resHom A hT) = IsLocalRing.maximalIdeal (gaussRing A hT) := by
  ext f
  rw [RingHom.mem_ker, resHom_eq_zero_iff]

theorem coe_algebraMap (c : L) :
    ((algebraMap L FF c : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl

theorem algebraMap_mem_gaussRing_iff (c : L) : algebraMap L FF c ∈ gaussRing A hT ↔ c ∈ A := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    rw [coe_algebraMap] at h
    by_contra hc
    have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
    have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
    have hcm : (⟨c⁻¹, hci⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hc
      have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
        have := congrArg (fun a : A => (a : L)) u.inv_val
        simpa [hu] using this
      rw [mul_inv_eq_one₀ hc0] at h1
      rw [← h1]; exact SetLike.coe_mem _
    have hyx : y = HahnSeries.C ⟨c⁻¹, hci⟩ * x := by
      apply ι_injective A
      rw [map_mul, ι_C, ← h, ← mul_assoc, ← map_mul]
      simp [inv_mul_cancel₀ hc0]
    apply hy
    rw [ϖ_eq_zero_iff]
    intro n
    rw [hyx, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hcm
  · intro hc
    refine ⟨HahnSeries.C ⟨c, hc⟩, 1, by simp, ?_⟩
    rw [coe_algebraMap, ι_C, map_one, mul_one]

theorem resHom_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A hT) :
    resHom A hT ⟨algebraMap L FF a, h⟩ = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a) := by
  rw [resHom_eq A hT (x := HahnSeries.C a) (y := 1) (by simp)
    (by rw [map_one, mul_one]; change algebraMap L (LaurentSeries L) (a : L) = _; rw [ι_C]),
    ϖ_C, map_one, div_one]

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

theorem exists_smul_mem_gaussRing (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A hT, resHom A hT ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h, -⟩ := exists_frac_form A hT f hf
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ gaussRing A hT := (mem_gaussRing_iff A hT _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A hT (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

theorem resHom_mem (f : gaussRing A hT) : resHom A hT f ∈ qExpFunctionFieldC kk Γ := by
  by_cases hf : (f : FF) = 0
  · have : f = 0 := Subtype.ext hf
    rw [this, map_zero]
    exact IntermediateField.zero_mem _
  obtain ⟨hy, h⟩ := wit_spec A hT f
  obtain ⟨c, hc0, u₀, w₀, hu₀, hw₀, hfrac, hmem⟩ := exists_frac_form A hT (f : FF) hf
  rw [resHom_eq A hT hy h]

  have caseA : c ∈ A → ϖ A (wit A hT f).1 / ϖ A (wit A hT f).2 ∈ qExpFunctionFieldC kk Γ := by
    intro hc
    have hxw : (wit A hT f).1 * w₀ = HahnSeries.C ⟨c, hc⟩ * u₀ * (wit A hT f).2 := by
      apply ι_injective A
      rw [map_mul, map_mul, map_mul, ι_C, ← h, ← hfrac, mul_right_comm]
    have hred := congrArg (ϖ A) hxw
    rw [map_mul, map_mul, map_mul, ϖ_C] at hred
    have hxy : ϖ A (wit A hT f).1 / ϖ A (wit A hT f).2 =
        algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A ⟨c, hc⟩) * (ϖ A u₀ / ϖ A w₀) := by
      rw [← mul_div_assoc, div_eq_div_iff hy hw₀]
      exact hred
    rw [hxy]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _) hmem
  rcases A.mem_or_inv_mem c with hc | hc
  · exact caseA hc
  · by_cases hu : IsUnit (⟨c⁻¹, hc⟩ : A)
    ·
      apply caseA
      obtain ⟨u, hu⟩ := hu
      have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
        have := congrArg (fun a : A => (a : L)) u.inv_val
        simpa [hu] using this
      rw [mul_inv_eq_one₀ hc0] at h1
      rw [← h1]; exact SetLike.coe_mem _
    ·
      exfalso
      have hcm : (⟨c⁻¹, hc⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hu
      have hxw : HahnSeries.C ⟨c⁻¹, hc⟩ * ((wit A hT f).1 * w₀) = u₀ * (wit A hT f).2 := by
        apply ι_injective A
        have e1 : ι A (HahnSeries.C ⟨c⁻¹, hc⟩ * ((wit A hT f).1 * w₀)) =
            algebraMap L (LaurentSeries L) c⁻¹ * ((((f : FF) : LaurentSeries L) * ι A w₀) * ι A (wit A hT f).2) := by
          rw [map_mul, map_mul, ι_C, ← h]; ring
        rw [e1, hfrac, map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      have hred := congrArg (ϖ A) hxw
      have hzero : ϖ A (HahnSeries.C ⟨c⁻¹, hc⟩) = 0 := by
        rw [ϖ_C, (IsLocalRing.residue_eq_zero_iff _).mpr hcm, map_zero]
      rw [map_mul, hzero, zero_mul, map_mul] at hred
      exact mul_ne_zero hu₀ hy hred.symm

def resF : gaussRing A hT →+* qExpFunctionFieldC kk Γ :=
  (resHom A hT).codRestrict (qExpFunctionFieldC kk Γ).toSubring fun f => resHom_mem A hT f

theorem coe_resF (f : gaussRing A hT) : ((resF A hT f : qExpFunctionFieldC kk Γ) : LaurentSeries kk) = resHom A hT f :=
  rfl

theorem resF_ne_zero_iff (f : gaussRing A hT) : resF A hT f ≠ 0 ↔ resHom A hT f ≠ 0 := by
  rw [Ne, Ne, ← coe_resF, ZeroMemClass.coe_eq_zero]

theorem ker_resF : RingHom.ker (resF A hT) = IsLocalRing.maximalIdeal (gaussRing A hT) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resF, ZeroMemClass.coe_eq_zero]

def resRange : IntermediateField kk (LaurentSeries kk) where
  carrier := Set.range (resHom A hT)
  mul_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  algebraMap_mem' a := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    exact ⟨⟨algebraMap L FF a, (algebraMap_mem_gaussRing_iff A hT _).mpr a.2⟩, resHom_algebraMap A hT a _⟩
  inv_mem' := by
    rintro _ ⟨f, rfl⟩
    by_cases h0 : resHom A hT f = 0
    · rw [h0, inv_zero]; exact ⟨0, map_zero _⟩
    · have hinv := inv_mem_gaussRing_of_resHom_ne_zero A hT f h0
      have hf0 : (f : FF) ≠ 0 := by
        intro hf
        apply h0
        have : f = 0 := Subtype.ext hf
        rw [this, map_zero]
      refine ⟨⟨(f : FF)⁻¹, hinv⟩, ?_⟩
      have hprod : resHom A hT ⟨(f : FF)⁻¹, hinv⟩ * resHom A hT f = 1 := by
        rw [← map_mul, ← map_one (resHom A hT)]
        congr 1
        exact Subtype.ext (inv_mul_cancel₀ hf0)
      exact eq_inv_of_mul_eq_one_left hprod

theorem div_intSeriesC_mem {κ : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hgQ : intSeriesC ℚ pg ≠ 0) : intSeriesC L pf / intSeriesC L pg ∈ FF := by
  have : intSeriesC L pf / intSeriesC L pg = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) := by
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  rw [this]
  exact coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f g hf hg hgQ)

theorem qExpFunctionFieldC_le_resRange : qExpFunctionFieldC kk Γ ≤ resRange A hT := by
  change adjoin kk _ ≤ _
  rw [adjoin_le_iff]
  rintro _ ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩

  have hgA : intSeriesA A pg ≠ 0 := by
    intro h; apply hg0; rw [← ϖ_intSeriesA A, h, map_zero]
  have hgL : intSeriesC L pg ≠ 0 := by
    rw [← ι_intSeriesA A]; exact (map_ne_zero_iff _ (ι_injective A)).mpr hgA
  have hgQ : intSeriesC ℚ pg ≠ 0 := by
    intro h; apply hgL; rw [← coeffEmb_intSeriesC L, h, map_zero]

  have hmemF : intSeriesC L pf / intSeriesC L pg ∈ FF := div_intSeriesC_mem (L := L) f g hf hg hgQ
  have hwit : ((⟨_, hmemF⟩ : FF) : LaurentSeries L) * ι A (intSeriesA A pg) = ι A (intSeriesA A pf) := by
    change intSeriesC L pf / intSeriesC L pg * ι A (intSeriesA A pg) = ι A (intSeriesA A pf)
    rw [ι_intSeriesA, ι_intSeriesA, div_mul_cancel₀ _ hgL]
  have hϖ : ϖ A (intSeriesA A pg) ≠ 0 := by rw [ϖ_intSeriesA]; exact hg0
  have hmemO : (⟨_, hmemF⟩ : FF) ∈ gaussRing A hT := ⟨_, _, hϖ, hwit⟩
  refine ⟨⟨_, hmemO⟩, ?_⟩
  rw [resHom_eq A hT (f := ⟨_, hmemO⟩) hϖ hwit, ϖ_intSeriesA, ϖ_intSeriesA]

theorem resF_surjective : Function.Surjective (resF A hT) := by
  intro z
  obtain ⟨f, hf⟩ := qExpFunctionFieldC_le_resRange A hT z.2
  exact ⟨f, Subtype.ext hf⟩

theorem resF_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A hT) :
    resF A hT ⟨algebraMap L FF a, h⟩ = algebraMap kk (qExpFunctionFieldC kk Γ) (IsLocalRing.residue A a) :=
  Subtype.ext (by rw [coe_resF, resHom_algebraMap]; rfl)

theorem exists_smul_mem_resF (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A hT, resF A hT ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A hT f hf
  exact ⟨c, h, (resF_ne_zero_iff A hT _).mpr hne⟩

end Gauss

section PlaceMap

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
variable (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ReductionInputsQExpModL A Γ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

omit [Γ.FiniteIndex] in
theorem coe_ne_zero_of_resHom_ne_zero (u : gaussRing A hT) (hu : resHom A hT u ≠ 0) : (u : FF) ≠ 0 := by
  intro h0
  apply hu
  have : u = 0 := Subtype.ext h0
  rw [this, map_zero]

omit [Γ.FiniteIndex] in
theorem resF_inv (u : gaussRing A hT) (hu : resHom A hT u ≠ 0) :
    resF A hT ⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A hT u hu⟩ = (resF A hT u)⁻¹ := by
  have hu0 := coe_ne_zero_of_resHom_ne_zero hT A u hu
  have hprod : resF A hT ⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A hT u hu⟩ * resF A hT u = 1 := by
    rw [← map_mul, ← map_one (resF A hT)]
    congr 1
    exact Subtype.ext (inv_mul_cancel₀ hu0)
  exact eq_inv_of_mul_eq_one_left hprod

omit [Γ.FiniteIndex] in

theorem exists_unit_of_mem_closure {D : Divisor Qb FF}
    (hD : D ∈ AddSubgroup.closure
      (laurentIntegralPrincipalDivisors A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb)) :
    ∃ u : gaussRing A hT, resHom A hT u ≠ 0 ∧ (∀ P, D P = P.ord ((u : FF) : FF)) ∧
      ∀ Q : Place kk Fb, Finsupp.mapDomain (placeReductionQExpModL h) D Q = Q.ord (resF A hT u : Fb) := by
  have hr := isPlaceReductionQExpModL_placeReductionQExpModL h
  induction hD using AddSubgroup.closure_induction with
  | mem D hD =>
    obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
    refine ⟨⟨⟨_, hy⟩, ι_mem_gaussRing A hT hy⟩, ?_, hDy, fun Q => ?_⟩
    · rw [resHom_ι]; exact hne
    · rw [hr.2 y hy hyk hne D hDy Q]
      congr 1
      exact Subtype.ext (by rw [coe_resF, resHom_ι])
  | zero =>
    exact ⟨1, by rw [map_one]; exact one_ne_zero, fun P => by simp, fun Q => by simp⟩
  | add D E _ _ hD hE =>
    obtain ⟨u, hu, hDu, hru⟩ := hD
    obtain ⟨v, hv, hEv, hrv⟩ := hE
    have hu0 := coe_ne_zero_of_resHom_ne_zero hT A u hu
    have hv0 := coe_ne_zero_of_resHom_ne_zero hT A v hv
    have hru0 : (resF A hT u : Fb) ≠ 0 := (resF_ne_zero_iff A hT u).mpr hu
    have hrv0 : (resF A hT v : Fb) ≠ 0 := (resF_ne_zero_iff A hT v).mpr hv
    refine ⟨u * v, by rw [map_mul]; exact mul_ne_zero hu hv, fun P => ?_, fun Q => ?_⟩
    · rw [Finsupp.add_apply, hDu, hEv]
      exact (P.ord_mul hu0 hv0).symm
    · rw [Finsupp.mapDomain_add, Finsupp.add_apply, hru, hrv, map_mul]
      exact (Q.ord_mul hru0 hrv0).symm
  | neg D _ hD =>
    obtain ⟨u, hu, hDu, hru⟩ := hD
    have hru0 : (resF A hT u : Fb) ≠ 0 := (resF_ne_zero_iff A hT u).mpr hu
    refine ⟨⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A hT u hu⟩, ?_, fun P => ?_, fun Q => ?_⟩
    · rw [← resF_ne_zero_iff, resF_inv hT A u hu]; exact inv_ne_zero hru0
    · rw [Finsupp.neg_apply, hDu, ← Place.ord_inv]
    · rw [← Finsupp.mapDomain.addMonoidHom_apply, map_neg, Finsupp.mapDomain.addMonoidHom_apply,
        Finsupp.neg_apply, hru, resF_inv hT A u hu, ← Place.ord_inv]

set_option maxHeartbeats 1600000 in

theorem mapDomain_placeMap (f : gaussRing A hT) (hf : resF A hT f ≠ 0) (D : Divisor Qb FF)
    (hD : ∀ P, D P = P.ord ((f : FF) : FF)) (Q : Place kk Fb) :
    Finsupp.mapDomain (placeReductionQExpModL h) D Q = Q.ord (resF A hT f : Fb) := by
  have hf' : resHom A hT f ≠ 0 := (resF_ne_zero_iff A hT f).mp hf
  have hf0 : (f : FF) ≠ 0 := coe_ne_zero_of_resHom_ne_zero hT A f hf'

  have hDprin : D ∈ Divisor.principal (K := Qb) (F := FF) := ⟨(f : FF), hf0, hD⟩
  have hgen : LaurentPrincipalGeneratedByIntegral A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb :=
    h.choose_spec.2
  obtain ⟨u, hu, hDu, hru⟩ := exists_unit_of_mem_closure hT A h (hgen hDprin)
  have hu0 : (u : FF) ≠ 0 := coe_ne_zero_of_resHom_ne_zero hT A u hu

  have hgO : (f : FF) * (u : FF)⁻¹ ∈ gaussRing A hT :=
    mul_mem f.2 (inv_mem_gaussRing_of_resHom_ne_zero A hT u hu)
  have hg_ord : ∀ P : Place Qb FF, P.ord ((f : FF) * (u : FF)⁻¹) = 0 := fun P => by
    rw [P.ord_mul hf0 (inv_ne_zero hu0), P.ord_inv, ← hD P, ← hDu P]; ring

  obtain ⟨x, hx, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qb Γ hT
  haveI := hfd
  obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hx hg_ord
  have hcA : c ∈ A := (algebraMap_mem_gaussRing_iff A hT c).mp (by rw [hc]; exact hgO)

  have hfgu : f = ⟨_, hgO⟩ * u :=
    Subtype.ext (by change (f : FF) = (f : FF) * (u : FF)⁻¹ * (u : FF); rw [inv_mul_cancel_right₀ hu0])
  have hgc : (⟨_, hgO⟩ : gaussRing A hT) =
      ⟨algebraMap Qb FF ((⟨c, hcA⟩ : A) : Qb), (algebraMap_mem_gaussRing_iff A hT _).mpr hcA⟩ :=
    Subtype.ext hc.symm
  have hresg : resF A hT ⟨_, hgO⟩ = algebraMap kk Fb (IsLocalRing.residue A ⟨c, hcA⟩) := by
    rw [hgc, resF_algebraMap]
  have hru0 : (resF A hT u : Fb) ≠ 0 := (resF_ne_zero_iff A hT u).mpr hu
  have hres_f : resF A hT f = algebraMap kk Fb (IsLocalRing.residue A ⟨c, hcA⟩) * resF A hT u := by
    rw [hfgu, map_mul, hresg]
  have hcbar : IsLocalRing.residue A ⟨c, hcA⟩ ≠ 0 := by
    intro h0
    apply hf
    rw [hres_f, h0, map_zero, zero_mul]
  rw [hres_f, Q.ord_mul ((_root_.map_ne_zero _).mpr hcbar) hru0,
    ConstantReduction.ord_algebraMap Q hcbar, zero_add, hru Q]

def gaussReduction : ConstantReduction A FF Fb where
  integers := gaussRing A hT
  residue := resF A hT
  placeMap := placeReductionQExpModL h
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A hT
  residue_surjective := resF_surjective A hT
  ker_residue := ker_resF A hT
  residue_algebraMap a := resF_algebraMap A hT a _
  exists_smul_mem := exists_smul_mem_resF A hT
  deg_placeMap := (isPlaceReductionQExpModL_placeReductionQExpModL h).1
  mapDomain_placeMap f hf D hD Q := mapDomain_placeMap hT A h f hf D hD Q

theorem pic0Map_gaussReduction : (gaussReduction hT A h).pic0Map = reductionQExpModL A Γ := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  rw [ConstantReduction.pic0Map_mk, reductionQExpModL_mk h]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem residue_gaussReduction (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF)
    (hyk : coeffMap (IsLocalRing.residue A) y ∈ Fb) :
    ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ (gaussReduction hT A h).integers,
      (gaussReduction hT A h).residue ⟨_, hO⟩ = ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ :=
  ⟨ι_mem_gaussRing A hT hy, Subtype.ext (resHom_ι A hT hy)⟩

include hT in
theorem main :
    ∃ R : ConstantReduction A FF Fb,
      R.placeMap = placeReductionQExpModL h ∧
      R.pic0Map = reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF)
        (hyk : coeffMap (IsLocalRing.residue A) y ∈ Fb),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ :=
  ⟨gaussReduction hT A h, rfl, pic0Map_gaussReduction hT A h, residue_gaussReduction hT A h⟩

end PlaceMap

end ModularCurve.GaussQExp

theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ModularCurve.ReductionInputsQExpModL A Γ) :
    ∃ R : ConstantReduction A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      R.placeMap = ModularCurve.placeReductionQExpModL h ∧
      R.pic0Map = ModularCurve.reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
              ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ :=
  ModularCurve.GaussQExp.main hT A h

end

end S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
end P2MW
export P2MW.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL (solution)
