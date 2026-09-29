-- Prove2me | solution 1 for NumberField.AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/846f48f4-7c60-5863-8f03-f72b974225a3

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_HaarMeasure_HaarChar_Ring
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField IsDedekindDomain"
open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "place InfinitePlace AdeleRing TateGlobal.ideleNorm AdeleRing.secondCountableTopology"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pairHaar pairChar pairChar_apply fourierTransform2 fourierIntegral"
namespace RowModule
p2m_open "NumberField.AdelicFourier NumberField"

section Algebra

variable {A : Type*} [CommRing A]

def upperT (x : A) : GL (Fin 2) A :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; congr <;> ring,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; congr <;> ring⟩

def lowerT (x : A) : GL (Fin 2) A :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; congr <;> ring,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; congr <;> ring⟩

def diagT (u v : Aˣ) : GL (Fin 2) A :=
  ⟨!![(u : A), 0; 0, (v : A)], !![((u⁻¹ : Aˣ) : A), 0; 0, ((v⁻¹ : Aˣ) : A)],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

@[scoped simp] theorem coe_upperT (x : A) : (upperT x : Matrix (Fin 2) (Fin 2) A) = !![1, x; 0, 1] := rfl

@[scoped simp] theorem coe_lowerT (x : A) : (lowerT x : Matrix (Fin 2) (Fin 2) A) = !![1, 0; x, 1] := rfl

@[scoped simp] theorem coe_diagT (u v : Aˣ) :
    (diagT u v : Matrix (Fin 2) (Fin 2) A) = !![(u : A), 0; 0, (v : A)] := rfl

@[scoped simp] theorem inv_upperT (x : A) : (upperT x)⁻¹ = upperT (-x) := by
  refine Units.ext ?_
  show !![1, -x; 0, 1] = !![1, -x; 0, 1]
  rfl

@[scoped simp] theorem inv_lowerT (x : A) : (lowerT x)⁻¹ = lowerT (-x) := by
  refine Units.ext ?_
  show !![1, 0; -x, 1] = !![1, 0; -x, 1]
  rfl

theorem inv_diagT (u v : Aˣ) : (diagT u v)⁻¹ = diagT u⁻¹ v⁻¹ := by
  refine Units.ext ?_
  show !![((u⁻¹ : Aˣ) : A), 0; 0, ((v⁻¹ : Aˣ) : A)] = _
  rfl

theorem det_upperT (x : A) : Matrix.GeneralLinearGroup.det (upperT x) = 1 :=
  Units.ext (by simp [Matrix.det_fin_two_of])

theorem det_lowerT (x : A) : Matrix.GeneralLinearGroup.det (lowerT x) = 1 :=
  Units.ext (by simp [Matrix.det_fin_two_of])

theorem upperT_eq_commutator (u : Aˣ) (y : A) :
    upperT (((u : A) - 1) * y) = diagT u 1 * upperT y * (diagT u 1)⁻¹ * (upperT y)⁻¹ := by
  rw [inv_diagT, inv_upperT, inv_one]
  refine Units.ext ?_
  simp only [Units.val_mul, coe_upperT, coe_diagT, Units.val_one, Matrix.mul_fin_two]
  congr 1
  simp
  ring

theorem lowerT_eq_commutator (u : Aˣ) (y : A) :
    lowerT (((u : A) - 1) * y) = diagT 1 u * lowerT y * (diagT 1 u)⁻¹ * (lowerT y)⁻¹ := by
  rw [inv_diagT, inv_lowerT, inv_one]
  refine Units.ext ?_
  simp only [Units.val_mul, coe_lowerT, coe_diagT, Units.val_one, Matrix.mul_fin_two]
  congr 1
  simp
  ring

theorem map_commutator_eq_one (φ : GL (Fin 2) A →* ℝ≥0) (a b : GL (Fin 2) A) :
    φ (a * b * a⁻¹ * b⁻¹) = 1 := by
  have ha : φ a * φ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hb : φ b * φ b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, map_mul]
  calc φ a * φ b * φ a⁻¹ * φ b⁻¹ = (φ a * φ a⁻¹) * (φ b * φ b⁻¹) := by ring
    _ = 1 := by rw [ha, hb, one_mul]

theorem map_upperT_eq_one (φ : GL (Fin 2) A →* ℝ≥0) (hu : ∃ u : Aˣ, IsUnit ((u : A) - 1)) (x : A) :
    φ (upperT x) = 1 := by
  obtain ⟨u, w, hw⟩ := hu
  have hx : x = ((u : A) - 1) * (((w⁻¹ : Aˣ) : A) * x) := by
    rw [← mul_assoc, ← hw, Units.mul_inv, one_mul]
  rw [hx, upperT_eq_commutator]
  exact map_commutator_eq_one _ _ _

theorem map_lowerT_eq_one (φ : GL (Fin 2) A →* ℝ≥0) (hu : ∃ u : Aˣ, IsUnit ((u : A) - 1)) (x : A) :
    φ (lowerT x) = 1 := by
  obtain ⟨u, w, hw⟩ := hu
  have hx : x = ((u : A) - 1) * (((w⁻¹ : Aˣ) : A) * x) := by
    rw [← mul_assoc, ← hw, Units.mul_inv, one_mul]
  rw [hx, lowerT_eq_commutator]
  exact map_commutator_eq_one _ _ _

theorem isUnit_apply_of_offDiag_eq_zero (g : GL (Fin 2) A)
    (h01 : (g : Matrix (Fin 2) (Fin 2) A) 0 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0)
    (i : Fin 2) : IsUnit ((g : Matrix (Fin 2) (Fin 2) A) i i) := by
  have hmul : ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * (g : Matrix (Fin 2) (Fin 2) A) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hii := congrFun (congrFun hmul i) i
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at hii
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, h10, mul_zero, add_zero] at hii
    exact IsUnit.of_mul_eq_one_right _ hii
  · simp only [Fin.mk_one, Fin.isValue, h01, mul_zero, zero_add] at hii
    exact IsUnit.of_mul_eq_one_right _ hii

theorem inv_mul_apply_zero_zero (g : GL (Fin 2) A) :
    ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 * (g : Matrix (Fin 2) (Fin 2) A) 0 0
      + ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 * (g : Matrix (Fin 2) (Fin 2) A) 1 0 = 1 := by
  have hmul : ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * (g : Matrix (Fin 2) (Fin 2) A) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have h00 := congrFun (congrFun hmul 0) 0
  rwa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h00

end Algebra

section StableRange

theorem exists_isUnit_add_mul_of_isLocalRing {R : Type*} [CommRing R] [IsLocalRing R]
    {a c x y : R} (h : x * a + y * c = 1) : ∃ ε : R, IsUnit (a + ε * c) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (x * a) with hxa | h1
  · exact ⟨0, by simpa using isUnit_of_mul_isUnit_right hxa⟩
  · have hyc : IsUnit (y * c) := by
      have : 1 - x * a = y * c := by rw [← h]; ring
      rwa [this] at h1
    have hc : IsUnit c := isUnit_of_mul_isUnit_right hyc
    refine ⟨(1 - a) * ((hc.unit⁻¹ : Rˣ) : R), ?_⟩
    have : a + (1 - a) * ((hc.unit⁻¹ : Rˣ) : R) * c = 1 := by
      rw [mul_assoc, IsUnit.val_inv_mul, mul_one, add_sub_cancel]
    rw [this]
    exact isUnit_one

theorem exists_isUnit_add_mul_pi {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
    [∀ i, IsLocalRing (R i)] {a c x y : ∀ i, R i} (h : x * a + y * c = 1) :
    ∃ ε : ∀ i, R i, IsUnit (a + ε * c) := by
  have hi : ∀ i, ∃ ε : R i, IsUnit (a i + ε * c i) := fun i =>
    exists_isUnit_add_mul_of_isLocalRing (x := x i) (y := y i) (by
      have := congrFun h i
      simpa using this)
  choose ε hε using hi
  exact ⟨ε, Pi.isUnit_iff.mpr fun i => by simpa using hε i⟩

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_local_pivot (v : HeightOneSpectrum R) {a c x y : v.adicCompletion K}
    (h : x * a + y * c = 1) :
    ∃ ε : v.adicCompletion K, a + ε * c ≠ 0 ∧
      (a ∈ v.adicCompletionIntegers K → c ∈ v.adicCompletionIntegers K →
        x ∈ v.adicCompletionIntegers K → y ∈ v.adicCompletionIntegers K →
          ε ∈ v.adicCompletionIntegers K ∧ Valued.v (a + ε * c) = 1) := by
  by_cases hG : a ∈ v.adicCompletionIntegers K ∧ c ∈ v.adicCompletionIntegers K ∧
      x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K
  · obtain ⟨ha, hc, hx, hy⟩ := hG
    have h' : (⟨x, hx⟩ : v.adicCompletionIntegers K) * ⟨a, ha⟩ + ⟨y, hy⟩ * ⟨c, hc⟩ = 1 := by
      apply Subtype.ext
      exact h
    obtain ⟨ε, hε⟩ := exists_isUnit_add_mul_of_isLocalRing h'
    have hval : Valued.v (a + (ε : v.adicCompletion K) * c) = 1 := by
      have := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hε
      exact this
    refine ⟨ε, ?_, fun _ _ _ _ => ⟨ε.2, hval⟩⟩
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  · obtain ⟨ε, hε⟩ := exists_isUnit_add_mul_of_isLocalRing h
    exact ⟨ε, hε.ne_zero, fun ha hc hx hy => (hG ⟨ha, hc, hx, hy⟩).elim⟩

theorem exists_isUnit_add_mul_finiteAdeleRing {a c x y : FiniteAdeleRing R K}
    (h : x * a + y * c = 1) : ∃ ε : FiniteAdeleRing R K, IsUnit (a + ε * c) := by
  have hv : ∀ v : HeightOneSpectrum R, x v * a v + y v * c v = 1 := fun v =>
    congrArg (fun z : FiniteAdeleRing R K => z v) h
  choose ε hε0 hεint using fun v => exists_local_pivot (K := K) v (hv v)
  have hG : ∀ᶠ v in Filter.cofinite,
      a v ∈ v.adicCompletionIntegers K ∧ c v ∈ v.adicCompletionIntegers K ∧
        x v ∈ v.adicCompletionIntegers K ∧ y v ∈ v.adicCompletionIntegers K :=
    ((a.2.and c.2).and (x.2.and y.2)).mono fun v hv' => ⟨hv'.1.1, hv'.1.2, hv'.2.1, hv'.2.2⟩
  refine ⟨⟨ε, hG.mono fun v hv' => (hεint v hv'.1 hv'.2.1 hv'.2.2.1 hv'.2.2.2).1⟩, ?_⟩
  rw [FiniteAdeleRing.isUnit_iff]
  exact ⟨fun v => hε0 v,
    hG.mono fun v hv' => (hεint v hv'.1 hv'.2.1 hv'.2.2.1 hv'.2.2.2).2⟩

theorem exists_isUnit_add_mul_prod {S T : Type*} [CommRing S] [CommRing T]
    (hS : ∀ a c x y : S, x * a + y * c = 1 → ∃ ε : S, IsUnit (a + ε * c))
    (hT : ∀ a c x y : T, x * a + y * c = 1 → ∃ ε : T, IsUnit (a + ε * c))
    {a c x y : S × T} (h : x * a + y * c = 1) : ∃ ε : S × T, IsUnit (a + ε * c) := by
  obtain ⟨ε₁, h₁⟩ := hS a.1 c.1 x.1 y.1 (by simpa using congrArg Prod.fst h)
  obtain ⟨ε₂, h₂⟩ := hT a.2 c.2 x.2 y.2 (by simpa using congrArg Prod.snd h)
  exact ⟨(ε₁, ε₂), Prod.isUnit_iff.mpr ⟨by simpa using h₁, by simpa using h₂⟩⟩

theorem exists_isUnit_add_mul_adeleRing [NumberField K] {a c x y : AdeleRing R K}
    (h : x * a + y * c = 1) : ∃ ε : AdeleRing R K, IsUnit (a + ε * c) :=
  exists_isUnit_add_mul_prod
    (fun _ _ _ _ h' => exists_isUnit_add_mul_pi (ι := InfinitePlace K)
      (R := fun v => v.Completion) h')
    (fun _ _ _ _ h' => exists_isUnit_add_mul_finiteAdeleRing h') h

end StableRange

section RowMul

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

def rowMul (g : GL (Fin 2) A) : (Fin 2 → A) ≃ₜ+ (Fin 2 → A) where
  toFun x := Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) A)
  invFun x := Matrix.vecMul x ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
  left_inv x := by
    simp only [Matrix.vecMul_vecMul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv x := by
    simp only [Matrix.vecMul_vecMul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.vecMul_one]
  map_add' x y := Matrix.add_vecMul _ x y
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

@[scoped simp] theorem rowMul_apply (g : GL (Fin 2) A) (x : Fin 2 → A) :
    rowMul g x = Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) A) := rfl

theorem rowMul_one : rowMul (1 : GL (Fin 2) A) = ContinuousAddEquiv.refl (Fin 2 → A) := by
  ext x : 1
  simp [rowMul_apply]

theorem rowMul_mul (g h : GL (Fin 2) A) : rowMul (g * h) = (rowMul g).trans (rowMul h) := by
  ext x : 1
  simp only [rowMul_apply, ContinuousAddEquiv.trans_apply, Matrix.vecMul_vecMul,
    Matrix.GeneralLinearGroup.coe_mul]

variable [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

def rowModulus : GL (Fin 2) A →* ℝ≥0 where
  toFun g := addEquivAddHaarChar (rowMul g)
  map_one' := by rw [rowMul_one]; exact addEquivAddHaarChar_refl
  map_mul' g h := by rw [rowMul_mul, addEquivAddHaarChar_trans]

theorem rowModulus_apply (g : GL (Fin 2) A) : rowModulus g = addEquivAddHaarChar (rowMul g) := rfl

theorem rowModulus_eq_of_offDiag_eq_zero (g : GL (Fin 2) A)
    (h01 : (g : Matrix (Fin 2) (Fin 2) A) 0 1 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) :
    rowModulus g = ringHaarChar (isUnit_apply_of_offDiag_eq_zero g h01 h10 0).unit *
      ringHaarChar (isUnit_apply_of_offDiag_eq_zero g h01 h10 1).unit := by
  set u : Fin 2 → Aˣ := fun i => (isUnit_apply_of_offDiag_eq_zero g h01 h10 i).unit with hu
  have hpi := ringHaarChar_pi (A := fun _ : Fin 2 => A) u
  rw [Fin.prod_univ_two] at hpi
  rw [← hpi, ringHaarChar_apply, rowModulus_apply]
  congr 1
  ext x i
  simp only [rowMul_apply, ContinuousAddEquiv.mulLeft_apply]
  rw [Pi.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, h10, mul_zero, add_zero]
    rw [mul_comm]; rfl
  · simp only [Fin.mk_one, Fin.isValue, h01, mul_zero, zero_add]
    rw [mul_comm]; rfl

theorem rowModulus_eq_ringHaarChar_det_of_pivot (hu : ∃ u : Aˣ, IsUnit ((u : A) - 1))
    (g : GL (Fin 2) A)
    (hpiv : ∃ ε : A, IsUnit ((g : Matrix (Fin 2) (Fin 2) A) 0 0 + ε * (g : Matrix (Fin 2) (Fin 2) A) 1 0)) :
    rowModulus g = ringHaarChar (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨ε, hw⟩ := hpiv
  set a := (g : Matrix (Fin 2) (Fin 2) A) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) A) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) A) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) A) 1 1 with hd
  set wi : A := ((hw.unit⁻¹ : Aˣ) : A) with hwi_def
  have hwi : (a + ε * c) * wi = 1 := hw.mul_val_inv
  set M : GL (Fin 2) A := lowerT (-(c * wi)) * upperT ε * g * upperT (-(wi * (b + ε * d))) with hM
  have hg : (g : Matrix (Fin 2) (Fin 2) A) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hMval : (M : Matrix (Fin 2) (Fin 2) A) =
      !![1, 0; -(c * wi), 1] * !![1, ε; 0, 1] * !![a, b; c, d] * !![1, -(wi * (b + ε * d)); 0, 1] := by
    simp only [hM, Units.val_mul, coe_lowerT, coe_upperT, hg]
  have hM01 : (M : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
    rw [hMval]
    simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    linear_combination (-(b + ε * d)) * hwi
  have hM10 : (M : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
    rw [hMval]
    simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    linear_combination (-c) * hwi
  have hρ : rowModulus M = rowModulus g := by
    simp only [hM, map_mul, map_lowerT_eq_one _ hu, map_upperT_eq_one _ hu, one_mul, mul_one]
  have hdet : Matrix.GeneralLinearGroup.det M = Matrix.GeneralLinearGroup.det g := by
    simp only [hM, map_mul, det_upperT, det_lowerT, one_mul, mul_one]
  rw [← hρ, ← hdet, rowModulus_eq_of_offDiag_eq_zero M hM01 hM10, ← map_mul]
  congr 1
  refine Units.ext ?_
  rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, hM01, hM10, mul_zero, sub_zero]

end RowMul

section RingChar

open scoped Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]

theorem ringHaarChar_eq_distribHaarChar (u : Aˣ) : ringHaarChar u = distribHaarChar A u := by
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  set μ : Measure A := Measure.addHaarMeasure K₀ with hμ
  have hK : μ (K₀ : Set A) = 1 := Measure.addHaarMeasure_self
  symm
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := (K₀ : Set A))
    (by rw [hK]; exact one_ne_zero) (by rw [hK]; exact ENNReal.one_ne_top) ?_
  have := addEquivAddHaarChar_smul_preimage μ (ContinuousAddEquiv.mulLeft u)
    (X := u • (K₀ : Set A))
  rw [ContinuousAddEquiv.preimage_mulLeft_smul] at this
  rw [← this, ringHaarChar_apply, ENNReal.smul_def, smul_eq_mul]

end RingChar

section Adele

variable (F : Type) [Field F] [NumberField F]

theorem exists_isUnit_sub_one_adeleRing :
    ∃ u : (AdeleRing (𝓞 F) F)ˣ, IsUnit ((u : AdeleRing (𝓞 F) F) - 1) := by
  refine ⟨Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (2 : F) two_ne_zero), ?_⟩
  have : ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (2 : F) two_ne_zero) :
      (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) - 1 = 1 := by
    simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← map_one (algebraMap F (AdeleRing (𝓞 F) F)), ← map_sub]
    norm_num
  rw [this]
  exact isUnit_one

theorem exists_pivot_adeleRing (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    ∃ ε : AdeleRing (𝓞 F) F,
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0
        + ε * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) :=
  exists_isUnit_add_mul_adeleRing (R := 𝓞 F) (K := F) (inv_mul_apply_zero_zero g)

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]

theorem rowModulus_eq_distribHaarChar_det [SecondCountableTopology (AdeleRing (𝓞 F) F)]
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    rowModulus g = distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g) := by
  rw [rowModulus_eq_ringHaarChar_det_of_pivot (exists_isUnit_sub_one_adeleRing F) g
    (exists_pivot_adeleRing F g), ringHaarChar_eq_distribHaarChar]

theorem regular_of_isAddHaarMeasure [SecondCountableTopology (AdeleRing (𝓞 F) F)]
    (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] : μ.Regular := by
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Fin 2 → AdeleRing (𝓞 F) F)) :=
    inferInstance
  exact Measure.regular_of_isAddLeftInvariant K₀.isCompact K₀.interior_nonempty
    K₀.isCompact.measure_lt_top.ne

theorem map_rowMul [SecondCountableTopology (AdeleRing (𝓞 F) F)]
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] :
    Measure.map (fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) μ
      = (distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g))⁻¹ • μ := by
  haveI := regular_of_isAddHaarMeasure F μ
  have h := addEquivAddHaarChar_smul_map μ (rowMul g)
  rw [← rowModulus_apply, rowModulus_eq_distribHaarChar_det] at h
  have hne : distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g) ≠ 0 :=
    distribHaarChar_pos.ne'
  have := congrArg (fun ν : Measure (Fin 2 → AdeleRing (𝓞 F) F) =>
    (distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g))⁻¹ • ν) h
  simp only [inv_smul_smul₀ hne] at this
  exact this

theorem measure_image_rowMul [SecondCountableTopology (AdeleRing (𝓞 F) F)]
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (s : Set (Fin 2 → AdeleRing (𝓞 F) F)) :
    μ ((fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) '' s)
      = distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g) * μ s := by
  haveI := regular_of_isAddHaarMeasure F μ
  have h := addEquivAddHaarChar_smul_preimage μ (rowMul g) (X := rowMul g '' s)
  rw [Set.preimage_image_eq _ (rowMul g).injective, ← rowModulus_apply,
    rowModulus_eq_distribHaarChar_det, ENNReal.smul_def, smul_eq_mul] at h
  exact h.symm

theorem integral_comp_rowMul [SecondCountableTopology (AdeleRing (𝓞 F) F)]
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (f : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :
    (Integrable (fun x => f (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) μ ↔
        Integrable f μ) ∧
    ∫ x, f (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ∂μ
      = (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ)
          * ∫ x, f x ∂μ := by
  set e : (Fin 2 → AdeleRing (𝓞 F) F) ≃ᵐ (Fin 2 → AdeleRing (𝓞 F) F) :=
    (rowMul g).toHomeomorph.toMeasurableEquiv with he
  have hecoe : (e : (Fin 2 → AdeleRing (𝓞 F) F) → (Fin 2 → AdeleRing (𝓞 F) F))
      = fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := rfl
  set C : ℝ≥0 := distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g) with hC
  have hCne : C ≠ 0 := distribHaarChar_pos.ne'
  have hmap : Measure.map e μ = C⁻¹ • μ := by rw [hecoe]; exact map_rowMul F g μ
  have hmap' : Measure.map e μ = ((C⁻¹ : ℝ≥0) : ENNReal) • μ := by
    rw [hmap, Measure.coe_nnreal_smul]
  refine ⟨?_, ?_⟩
  · have h1 := integrable_map_equiv e f (μ := μ)
    rw [hmap', integrable_smul_measure (by simp [hCne]) ENNReal.coe_ne_top] at h1
    exact h1.symm
  · have h2 := integral_map_equiv e f (μ := μ)
    rw [hmap, integral_smul_nnreal_measure] at h2
    rw [hecoe] at h2
    rw [← h2, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv]
    rfl

theorem fourierTransform2_comp_rowMul [SecondCountableTopology (AdeleRing (𝓞 F) F)]
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (y : Fin 2 → AdeleRing (𝓞 F) F) :
    fourierTransform2 ψ μ₁
        (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) y
      = (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ)
          * fourierTransform2 ψ μ₁ Φ
              (Matrix.mulVec ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
                  Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) y) := by
  haveI : (pairHaar μ₁).IsAddHaarMeasure := by
    unfold pairHaar; infer_instance
  set G : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  set Gi : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
    ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  have hGGi : G * Gi = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]

  set f : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ := fun z =>
    pairChar ψ (-(Matrix.vecMul z Gi * y)) * Φ z with hf
  have hcomp : (fun x => pairChar ψ (-(x * y)) * Φ (Matrix.vecMul x G))
      = fun x => f (Matrix.vecMul x G) := by
    funext x
    simp only [hf, Matrix.vecMul_vecMul, hGGi, Matrix.vecMul_one]

  have hchar : ∀ z : Fin 2 → AdeleRing (𝓞 F) F,
      pairChar ψ (-(Matrix.vecMul z Gi * y)) = pairChar ψ (-(z * Matrix.mulVec Gi y)) := by
    intro z
    simp only [pairChar_apply, Pi.neg_apply, Pi.mul_apply, ← neg_add]
    congr 2
    have h := Matrix.dotProduct_mulVec z Gi y
    simp only [dotProduct, Fin.sum_univ_two] at h
    exact h.symm
  unfold fourierTransform2 fourierIntegral
  rw [hcomp, (integral_comp_rowMul F g (pairHaar μ₁) f).2]
  simp only [hf, hchar]

end Adele

end NumberField.AdelicFourier.RowModule
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier.RowModule"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier"
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier.RowModule"

open _root_.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier NumberField.AdelicFourier.RowModule in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure],
      Measure.map (fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) μ
        = (distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g))⁻¹ • μ) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
      (s : Set (Fin 2 → AdeleRing (𝓞 F) F)),
      μ ((fun x => Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) '' s)
        = distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det g) * μ s) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
      (f : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ),
      (Integrable (fun x => f (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) μ ↔
          Integrable f μ) ∧
      ∫ x, f (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ∂μ
        = (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ)
            * ∫ x, f x ∂μ) ∧
    (∀ (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
      (y : Fin 2 → AdeleRing (𝓞 F) F),
      fourierTransform2 ψ μ₁
          (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) y
        = (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ)
            * fourierTransform2 ψ μ₁ Φ
                (Matrix.mulVec ((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
                    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) y)) := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  exact ⟨fun μ _ => map_rowMul F g μ, fun μ _ s => measure_image_rowMul F g μ s,
    fun μ _ f => integral_comp_rowMul F g μ f,
    fun μ₁ _ ψ Φ y => fourierTransform2_comp_rowMul F g μ₁ ψ Φ y⟩

end S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
end P2MW
export P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul (solution)
