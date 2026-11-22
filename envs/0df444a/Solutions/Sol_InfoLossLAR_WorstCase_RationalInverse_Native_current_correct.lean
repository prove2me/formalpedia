-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RationalInverse.Native.current_correct
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:01:21.349097+00:00
-- url     : https://prove2.me/submissions/6cbb49f3-1a84-41b7-9d95-e58f53c07794

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_NativeSupplement_01
import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_QAlgorithms_Defs_Measurement
import Theorems.Thm_AFT_RationalNumerics_HeightBound_inv
set_option Elab.async true

set_option linter.all false

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics
end InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

/- Helper module AFT.RationalHeight. -/
section P2MDyadicModule0

namespace AFT.RationalNumerics

open scoped BigOperators

namespace HeightBound

theorem mono {value : ℚ} {first second : ℕ} (h : HeightBound value first) (hle : first ≤ second) :
    HeightBound value second := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  exact ⟨h.1.trans hp,h.2.trans hp⟩

private theorem reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))

theorem zero : HeightBound 0 0 := by norm_num [HeightBound]

theorem of_int {value : ℤ} {bits : ℕ} (h : value.natAbs ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  constructor
  · simpa using h
  · simpa using (Nat.one_le_pow bits 2 (by decide))

theorem mul {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first*second) (firstBits+secondBits) := by
  have heq : first*second=Rat.divInt (first.num*second.num) (first.den*second.den : ℤ) := by
    calc
      _ = Rat.divInt first.num first.den * Rat.divInt second.num second.den := by rw [Rat.num_divInt_den,Rat.num_divInt_den]
      _ = _ := Rat.divInt_mul_divInt _ _
  have hr := reduced_le (first.num*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul,← heq] at hr
  simp only [Int.natAbs_mul] at hr
  rw [HeightBound,pow_add]
  exact ⟨hr.1.trans (Nat.mul_le_mul hf.1 hs.1),hr.2.trans (Nat.mul_le_mul hf.2 hs.2)⟩

theorem div {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first/second) (firstBits+secondBits) := by
  simpa only [div_eq_mul_inv] using hf.mul hs.inv

end HeightBound

end AFT.RationalNumerics

end P2MDyadicModule0

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule1

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

theorem realVec_zero {dimension : ℕ} : realVec (0 : QVector dimension)=0 := by ext index;simp [realVec]

theorem realVec_add {dimension : ℕ} (left right : QVector dimension) : realVec (left+right)=realVec left+realVec right := by
  ext index
  exact Rat.cast_add _ _

theorem realVec_sub {dimension : ℕ} (left right : QVector dimension) : realVec (left-right)=realVec left-realVec right := by
  ext index
  exact Rat.cast_sub _ _

theorem realVec_smul {dimension : ℕ} (scalar : ℚ) (vector : QVector dimension) :
    realVec (scalar • vector)=(scalar : ℝ) • realVec vector := by
  ext index
  exact Rat.cast_mul _ _

theorem realVec_list_sum {dimension : ℕ} (vectors : List (QVector dimension)) :
    realVec vectors.sum=(vectors.map realVec).sum := by
  induction vectors with
  | nil => exact realVec_zero
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,realVec_add,ih]

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

theorem cache_length {dimension count : ℕ} (vectors : Fin count → QVector dimension) (steps : ℕ) :
    (cache vectors steps).length=steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [cache,List.length_append,List.length_singleton,ih]

def squaredNorm {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : ℚ := innerQ (orthogonal vectors index) (orthogonal vectors index)

noncomputable section

theorem projection_real {dimension : ℕ} (orthogonal current : QVector dimension) :
    realVec (projection orthogonal current)=
      (inner ℝ (realVec orthogonal) (realVec current)/‖realVec orthogonal‖^2) • realVec orthogonal := by
  rw [projection,realVec_smul,Rat.cast_div,innerQ_real,innerQ_real,real_inner_self_eq_norm_sq]

theorem orthogonalStep_real {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) :
    realVec (orthogonalStep previous current)=realVec current-
      ((previous.map realVec).map (fun orthogonal => (inner ℝ orthogonal (realVec current)/‖orthogonal‖^2) • orthogonal)).sum := by
  rw [orthogonalStep,realVec_sub,realVec_list_sum]
  simp only [List.map_map,Function.comp_def,projection_real]

private theorem sum_Iio_fin {count : ℕ} {Value : Type*} [AddCommMonoid Value]
    (index : Fin count) (function : Fin count → Value) :
    (∑ previous ∈ Finset.Iio index,function previous)=
      ∑ previous : Fin index.val,function ⟨previous.val,previous.isLt.trans index.isLt⟩ := by
  classical
  refine Finset.sum_bij (fun previous membership =>
    (⟨previous.val,show previous < index from Finset.mem_Iio.mp membership⟩ : Fin index.val)) ?_ ?_ ?_ ?_
  · intro previous membership
    exact Finset.mem_univ _
  · intro first hfirst second hsecond hequal
    exact Fin.ext (congrArg (fun value : Fin index.val => value.val) hequal)
  · intro previous membership
    refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,Finset.mem_Iio.mpr (show (⟨previous.val,previous.isLt.trans index.isLt⟩ : Fin count) < index from previous.isLt),?_⟩
    rfl
  · intro previous membership
    congr 1

/-- Every materialized rational cache prefix is exactly the ordinary real
Gram--Schmidt prefix after the actual rational-to-real embedding. -/
theorem cache_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (cache vectors steps).map realVec=List.ofFn (fun index : Fin steps =>
      gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hsteps index)) := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps<count := by omega
    let index : Fin count := ⟨steps,hstep⟩
    rw [cache,List.map_append,List.map_singleton,ih hprevious,List.ofFn_succ_last]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext previous
      congr 1
    · apply congrArg (fun value : Space dimension => [value])
      change realVec (orthogonalStep (cache vectors steps) (if h : steps<count then vectors ⟨steps,h⟩ else 0))=
        gramSchmidt ℝ (fun position => realVec (vectors position)) index
      rw [dif_pos hstep,orthogonalStep_real,ih hprevious]
      simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
      have h := gramSchmidt_def'' ℝ (fun position => realVec (vectors position)) index
      rw [sum_Iio_fin] at h
      have hequal : (∑ previous : Fin steps,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous)‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))=
          ∑ previous : Fin index.val,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩)
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩ := rfl
      rw [hequal]
      exact sub_eq_iff_eq_add.mpr h

theorem orthogonal_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    realVec (orthogonal vectors index)=gramSchmidt ℝ (fun position => realVec (vectors position)) index := by
  have h := congrArg (fun values : List (Space dimension) => values.getD index.val (realVec (0 : QVector dimension)))
    (cache_real vectors count (le_refl count))
  rw [List.getD_map] at h
  simpa [orthogonal,index.isLt] using h

theorem squaredNorm_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    (squaredNorm vectors index : ℝ)=‖gramSchmidt ℝ (fun position => realVec (vectors position)) index‖^2 := by
  rw [squaredNorm,innerQ_real,orthogonal_real,real_inner_self_eq_norm_sq]

/-- Orthogonal projection only decreases the original column's square norm. -/
theorem gramSchmidt_norm_sq_le {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    ‖gramSchmidt ℝ vectors index‖^2 ≤ ‖vectors index‖^2 := by
  let orthogonal := gramSchmidt ℝ vectors
  have heq : inner ℝ (orthogonal index) (vectors index)=inner ℝ (orthogonal index) (orthogonal index) := by
    conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    rw [inner_add_right]
    suffices inner ℝ (orthogonal index)
        (∑ previous ∈ Finset.Iio index,
          (inner ℝ (orthogonal previous) (vectors index)/‖orthogonal previous‖^2) • orthogonal previous)=0 by
      change inner ℝ (orthogonal index) (orthogonal index)+_=inner ℝ (orthogonal index) (orthogonal index)
      rw [this,add_zero]
    simp only [inner_sum,inner_smul_right]
    apply Finset.sum_eq_zero
    intro previous membership
    rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]
  have hnonneg := (real_inner_self_nonneg (x := vectors index-orthogonal index))
  rw [inner_sub_sub_self,real_inner_comm (orthogonal index) (vectors index),heq,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hnonneg
  change ‖orthogonal index‖^2 ≤ _
  linarith

theorem squaredNorm_le {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    squaredNorm vectors index ≤ innerQ (vectors index) (vectors index) := by
  have h := gramSchmidt_norm_sq_le (fun position => realVec (vectors position)) index
  rw [←squaredNorm_real,←real_inner_self_eq_norm_sq,←innerQ_real] at h
  exact_mod_cast h

end

noncomputable section

theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]

theorem inputVectors_independent {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    LinearIndependent ℝ (fun position => realVec (inputVectors basis position)) := by
  simpa only [inputVectors_real basis hdet] using (IntegerBasis.realBasis basis hdet).linearIndependent

end

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeRationalGramSchmidtGeometry. -/
section P2MDyadicModule2

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

/-- Exact rational upper-triangular change from original input columns to
its materialized orthogonal cache. -/
def upper {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) : ℚ :=
  innerQ (orthogonal vectors row) (vectors column)/squaredNorm vectors row

noncomputable section

theorem inner_gramSchmidt_original {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    inner ℝ (gramSchmidt ℝ vectors index) (vectors index)=‖gramSchmidt ℝ vectors index‖^2 := by
  conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [inner_add_right]
  suffices inner ℝ (gramSchmidt ℝ vectors index)
      (∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ vectors previous) (vectors index)/‖gramSchmidt ℝ vectors previous‖^2) •
          gramSchmidt ℝ vectors previous)=0 by
    rw [this,add_zero,real_inner_self_eq_norm_sq]
  simp only [inner_sum,inner_smul_right]
  apply Finset.sum_eq_zero
  intro previous membership
  rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]

theorem upper_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) :
    (upper vectors row column : ℝ)=
      inner ℝ (gramSchmidt ℝ (fun index => realVec (vectors index)) row) (realVec (vectors column))/
        ‖gramSchmidt ℝ (fun index => realVec (vectors index)) row‖^2 := by
  rw [upper,Rat.cast_div,innerQ_real,orthogonal_real,squaredNorm_real]

theorem upper_diagonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (index : Fin count) :
    upper vectors index index=1 := by
  have hreal : (upper vectors index index : ℝ)=1 := by
    rw [upper_real,inner_gramSchmidt_original]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero index independent)))
  exact_mod_cast hreal

theorem upper_triangular {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) (before : column < row) :
    upper vectors row column=0 := by
  have hreal : (upper vectors row column : ℝ)=0 := by
    rw [upper_real,gramSchmidt_inv_triangular ℝ (fun index => realVec (vectors index)) before,zero_div]
  exact_mod_cast hreal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeGramDeterminant. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

noncomputable section

theorem prefixGram_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).map (fun value => (value : ℝ))=
      Matrix.gram ℝ (fun index => realVec (inputVectors basis (Fin.castLE hsteps index))) := by
  ext first second
  simp only [prefixGram,Matrix.map_apply,Matrix.gram_apply,realVec,inputVectors,PiLp.inner_apply,
    Real.inner_apply,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]

theorem prefixGram_det_ne_zero {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).det ≠ 0 := by
  have independent : LinearIndependent ℝ
      (fun index : Fin steps => realVec (inputVectors basis (Fin.castLE hsteps index))) :=
    (inputVectors_independent basis hdet).comp (Fin.castLE hsteps) (Fin.castLE_injective hsteps)
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr independent
  rw [←prefixGram_real,←Int.cast_det] at h
  exact_mod_cast h

/-- The subtraction made by Gram--Schmidt lies in the span of precisely
the original earlier columns, not an assumed short basis. -/
theorem gramSchmidt_correction_mem_prefix {dimension count : ℕ}
    (vectors : Fin count → QVector dimension) (index : Fin count) :
    realVec (vectors index)-realVec (orthogonal vectors index) ∈
      Submodule.span ℝ (Set.range (fun previous : Fin index.val =>
        realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))) := by
  classical
  let family := fun position => realVec (vectors position)
  have hset : Set.range (fun previous : Fin index.val =>
      realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))=family '' Set.Iio index := by
    ext point
    constructor
    · rintro ⟨previous,rfl⟩
      refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,?_,rfl⟩
      exact previous.isLt
    · rintro ⟨previous,hprevious,rfl⟩
      exact ⟨⟨previous.val,hprevious⟩,rfl⟩
  rw [hset,←span_gramSchmidt_Iio ℝ family index,orthogonal_real]
  have h := gramSchmidt_def'' ℝ family index
  have hcorrection : family index-gramSchmidt ℝ family index=
      ∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ family previous) (family index)/‖gramSchmidt ℝ family previous‖^2) •
          gramSchmidt ℝ family previous := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm,RCLike.ofReal_real_eq_id,id_eq] using h)
  change family index-gramSchmidt ℝ family index ∈ _
  rw [hcorrection]
  apply Submodule.sum_mem
  intro previous hprevious
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨previous,Finset.mem_Iio.mp hprevious,rfl⟩

end

def prefixPairing {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (previous : Fin index.val) : ℤ :=
  ∑ row,basis row ⟨previous.val,previous.isLt.trans index.isLt⟩*basis row index

def gramNumerator {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (row : Fin dimension) : ℤ :=
  (prefixGram basis index.val index.isLt.le).det*basis row index-
    ∑ previous : Fin index.val,
      Matrix.cramer (prefixGram basis index.val index.isLt.le) (prefixPairing basis index) previous*
        basis row ⟨previous.val,previous.isLt.trans index.isLt⟩

noncomputable section

/-- Multiplying the cached rational GS vector by the original integer
prefix-Gram determinant gives an explicitly integral Cramer numerator.
This is the denominator control needed for binary, rather than unit-cost,
complexity of the cached rational orthogonalization. -/
theorem gram_determinant_scales_orthogonal {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (index : Fin dimension) :
    ((prefixGram basis index.val index.isLt.le).det : ℚ) • orthogonal (inputVectors basis) index=
      fun row => (gramNumerator basis index row : ℚ) := by
  classical
  let previousColumn (previous : Fin index.val) : Fin dimension :=
    ⟨previous.val,previous.isLt.trans index.isLt⟩
  let family (previous : Fin index.val) := realVec (inputVectors basis (previousColumn previous))
  let gram := prefixGram basis index.val index.isLt.le
  let rhs := prefixPairing basis index
  let castGram := gram.map (fun value => (value : ℝ))
  obtain ⟨coefficients,hcoefficients⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (gramSchmidt_correction_mem_prefix (inputVectors basis) index)
  change (∑ previous,coefficients previous • family previous)=
    realVec (inputVectors basis index)-realVec (orthogonal (inputVectors basis) index) at hcoefficients
  have hinner (first second : Fin index.val) : inner ℝ (family first) (family second)=
      (gram first second : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,
      gram,prefixGram,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
    rfl
  have htarget (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (inputVectors basis index))=(rhs previous : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,prefixPairing,rhs,
      Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
  have horthogonal (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (orthogonal (inputVectors basis) index))=0 := by
    rw [orthogonal_real,real_inner_comm]
    exact gramSchmidt_inv_triangular ℝ (fun position => realVec (inputVectors basis position)) previous.isLt
  have hlinear : castGram.mulVec coefficients=fun previous => (rhs previous : ℝ) := by
    funext previous
    have h := congrArg (fun vector : Space dimension => inner ℝ (family previous) vector) hcoefficients
    simp only [inner_sum,inner_smul_right,inner_sub_right,horthogonal,sub_zero,htarget,hinner] at h
    simpa only [Matrix.mulVec,dotProduct,castGram,Matrix.map_apply,mul_comm] using h
  have hcramer : Matrix.cramer castGram (fun previous => (rhs previous : ℝ))=
      (gram.det : ℝ) • coefficients := by
    rw [←hlinear,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
      Matrix.smul_mulVec,Matrix.one_mulVec,←Int.cast_det]
  have hcramerCast (previous : Fin index.val) :
      Matrix.cramer castGram (fun position => (rhs position : ℝ)) previous=
        (Matrix.cramer gram rhs previous : ℝ) := by
    rw [Matrix.cramer_apply,Matrix.cramer_apply]
    have hmatrix : castGram.updateCol previous (fun position => (rhs position : ℝ))=
        (gram.updateCol previous rhs).map (fun value => (value : ℝ)) := by
      ext first second
      simp only [Matrix.updateCol_apply,Matrix.map_apply,castGram]
      split_ifs <;> rfl
    rw [hmatrix,←Int.cast_det]
  have hscaled : (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=
      ∑ previous,(Matrix.cramer gram rhs previous : ℝ) • family previous := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro previous _
    rw [smul_smul]
    have h := congrArg (fun values : Fin index.val → ℝ => values previous) hcramer
    simp only [Pi.smul_apply,smul_eq_mul,hcramerCast] at h
    rw [←h]
  have h := congrArg (fun vector : Space dimension => (gram.det : ℝ) • vector) hcoefficients
  change (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=_ at h
  rw [hscaled] at h
  ext row
  have hrow := congrArg (fun vector : Space dimension => vector row) h
  simp only [family,previousColumn,realVec,inputVectors,WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_sub,Finset.sum_apply,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Rat.cast_intCast] at hrow
  change (gram.det : ℚ)*orthogonal (inputVectors basis) index row=(gramNumerator basis index row : ℚ)
  apply Rat.cast_injective (α:=ℝ)
  simp only [gramNumerator,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum,Rat.cast_intCast,Int.cast_sub,Int.cast_mul,Int.cast_sum]
  change (gram.det : ℝ)*(orthogonal (inputVectors basis) index row : ℝ)=_
  dsimp [gram,rhs] at hrow ⊢
  linarith

theorem prefixGram_entry_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) (first second : Fin steps) :
    |prefixGram basis steps hsteps first second| ≤ (dimension : ℤ)*bound^2 := by
  unfold prefixGram
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ row,|basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)|) ≤
        ∑ _row : Fin dimension,bound^2 := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul,pow_two]
      exact mul_le_mul (hentries row _) (hentries row _) (abs_nonneg _) hbound
    _ = _ := by simp

/-- Every prefix determinant has a bound whose logarithm is polynomial
in the input dimension and the logarithmic entry bound. -/
theorem prefixGram_det_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) :
    |(prefixGram basis steps hsteps).det| ≤ (steps.factorial : ℤ)*((dimension : ℤ)*bound^2)^steps := by
  have h := Matrix.det_le (abv:=AbsoluteValue.abs)
    (prefixGram_entry_bound basis steps hsteps bound hbound hentries)
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using h

/-- A uniform polynomial exponent bounds every integer prefix Gram
normalizer, directly from an entry bit bound of the original input. -/
theorem prefixGram_det_binary_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height) :
    |(prefixGram basis steps hsteps).det| ≤ (2 : ℤ)^((2*dimension+2*height)*dimension) := by
  have hdimension : (dimension : ℤ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hstep : (steps : ℤ) ≤ 2^dimension := (by exact_mod_cast hsteps : (steps : ℤ) ≤ dimension).trans hdimension
  have hfactorial : (steps.factorial : ℤ) ≤ 2^(dimension*steps) := by
    calc
      _ ≤ (steps : ℤ)^steps := by exact_mod_cast Nat.factorial_le_pow steps
      _ ≤ ((2 : ℤ)^dimension)^steps := pow_le_pow_left₀ (Nat.cast_nonneg steps) hstep _
      _ = _ := by rw [←pow_mul]
  have hentryGram : (dimension : ℤ)*((2 : ℤ)^height)^2 ≤ 2^(dimension+2*height) := by
    calc
      _ ≤ (2 : ℤ)^dimension*((2 : ℤ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimension (sq_nonneg _)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;omega
  calc
    _ ≤ (steps.factorial : ℤ)*((dimension : ℤ)*((2 : ℤ)^height)^2)^steps :=
      prefixGram_det_bound basis steps hsteps ((2 : ℤ)^height) (by positivity) hentries
    _ ≤ (2 : ℤ)^(dimension*steps)*(2^(dimension+2*height))^steps :=
      mul_le_mul hfactorial (pow_le_pow_left₀ (by positivity) hentryGram _)
        (by positivity) (by positivity)
    _ = 2^((2*dimension+2*height)*steps) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left (2*dimension+2*height) hsteps)

/-- Every cached rational coordinate has a small absolute magnitude even
when canonical numerators and denominators require separate control. -/
theorem orthogonal_coordinate_abs_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    |orthogonal (inputVectors basis) index row| ≤ (2 : ℚ)^(dimension+height) := by
  have hcoordinate : orthogonal (inputVectors basis) index row^2 ≤
      squaredNorm (inputVectors basis) index := by
    unfold squaredNorm innerQ
    simp only [←sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ row)
  have hcolumn : innerQ (inputVectors basis index) (inputVectors basis index) ≤
      (dimension : ℚ)*((2 : ℚ)^height)^2 := by
    unfold innerQ inputVectors
    simp only [←sq]
    calc
      _ ≤ ∑ _ : Fin dimension,((2 : ℚ)^height)^2 := by
        apply Finset.sum_le_sum
        intro position _
        have hentry : |(basis position index : ℚ)| ≤ (2 : ℚ)^height := by
          exact_mod_cast hentries position index
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hentry
      _ = _ := by simp
  have hdimension : (dimension : ℚ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hpower : (1 : ℚ) ≤ 2^dimension := one_le_pow₀ (by norm_num)
  have hdimensionSquare : (dimension : ℚ) ≤ ((2 : ℚ)^dimension)^2 := by nlinarith
  have hsquare : orthogonal (inputVectors basis) index row^2 ≤ ((2 : ℚ)^(dimension+height))^2 := by
    calc
      _ ≤ squaredNorm (inputVectors basis) index := hcoordinate
      _ ≤ innerQ (inputVectors basis index) (inputVectors basis index) := squaredNorm_le _ index
      _ ≤ (dimension : ℚ)*((2 : ℚ)^height)^2 := hcolumn
      _ ≤ ((2 : ℚ)^dimension)^2*((2 : ℚ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimensionSquare (sq_nonneg _)
      _ = _ := by rw [pow_add,mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsquare)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeRationalDenominator. -/
section P2MDyadicModule4

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RationalDenominator

/-- Any nonzero integral clearing denominator is divisible by the canonical
positive denominator of the rational number. -/
theorem den_dvd {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    (r.den : ℤ) ∣ D := by
  have hDQ : (D : ℚ)≠0 := by exact_mod_cast hD
  have hr : r=(N : ℚ)/(D : ℚ) := (eq_div_iff hDQ).mpr (by simpa only [mul_comm] using h)
  rw [hr]
  simpa only [Rat.divInt_eq_div] using Rat.den_dvd N D

/-- Canonical denominators never exceed any nonzero integral clearing denominator. -/
theorem den_le_natAbs {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    r.den≤D.natAbs := by
  have hd := den_dvd hD h
  have hn : r.den ∣ D.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hn

/-- Clearing-denominator bounds control the canonical numerator as well. -/
theorem num_bound_rat {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    |(r.num : ℚ)| ≤ |(D : ℚ)| * |r| := by
  have hd : (r.den : ℚ) ≤ |(D : ℚ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (Nat.cast_le (α := ℚ)).mpr (den_le_natAbs hD h)
  calc
    |(r.num : ℚ)|=|(r.den : ℚ)*r| := congrArg abs (Rat.den_mul_eq_num r).symm
    _ = (r.den : ℚ)*|r| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)

/-- A magnitude bound and clearing-denominator bound yield a natural bound
on both stored rational integer fields. -/
theorem fields_bound {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N)
    (M : ℕ) (hM : |r|≤M) : r.den≤D.natAbs ∧ r.num.natAbs≤D.natAbs*M := by
  refine ⟨den_le_natAbs hD h,?_⟩
  have hn := (num_bound_rat hD h).trans (mul_le_mul_of_nonneg_left hM (abs_nonneg _))
  have hn' : (r.num.natAbs : ℚ) ≤ ((D.natAbs*M : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs] using hn
  exact_mod_cast hn'

end InfoLossLAR.WorstCase.RationalDenominator

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeRationalGramSchmidtHeight. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT.RationalNumerics

open scoped BigOperators

/-- A fixed polynomial in the dimension and input entry height controls
every reduced cached rational coordinate. -/
def coordinateHeight (dimension height : ℕ) : ℕ :=
  (2*dimension+2*height)*dimension+dimension+height

noncomputable section

/-- Canonical numerator and denominator sizes are polynomial, using the
actual integer Gram determinant rather than an arithmetic-operation count. -/
theorem orthogonal_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    HeightBound (orthogonal (inputVectors basis) index row) (coordinateHeight dimension height) := by
  have hnonzero := prefixGram_det_ne_zero basis hdet index.val index.isLt.le
  have hvector := gram_determinant_scales_orthogonal basis index
  have hcoordinate := congrArg (fun vector : QVector dimension => vector row) hvector
  simp only [Pi.smul_apply,smul_eq_mul] at hcoordinate
  have habs := orthogonal_coordinate_abs_bound basis height hentries index row
  have hM : |orthogonal (inputVectors basis) index row| ≤ ((2^(dimension+height) : ℕ) : ℚ) := by
    exact_mod_cast habs
  obtain ⟨hden,hnum⟩ := RationalDenominator.fields_bound hnonzero hcoordinate (2^(dimension+height)) hM
  have hD : (prefixGram basis index.val index.isLt.le).det.natAbs ≤
      2^((2*dimension+2*height)*dimension) := by
    have h := prefixGram_det_binary_bound basis index.val index.isLt.le height hentries
    have hcast : (((prefixGram basis index.val index.isLt.le).det.natAbs : ℕ) : ℤ) ≤
        (2 : ℤ)^((2*dimension+2*height)*dimension) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hcast
  constructor
  · apply hnum.trans
    apply (Nat.mul_le_mul_right (2^(dimension+height)) hD).trans_eq
    rw [←pow_add]
    congr 1
    unfold coordinateHeight
    omega
  · apply (hden.trans hD).trans
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by unfold coordinateHeight;omega)

theorem realVec_injective {dimension : ℕ} : Function.Injective (realVec (dimension:=dimension)) := by
  intro first second hequal
  funext index
  apply Rat.cast_injective (α:=ℝ)
  exact congrArg (fun vector : Space dimension => vector index) hequal

/-- Every materialized prefix consists of the very same final cached
orthogonal vectors, so all prefix state encodings share one height bound. -/
theorem cache_prefix_eq {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    cache vectors steps=List.ofFn (fun index : Fin steps => orthogonal vectors (Fin.castLE hsteps index)) := by
  apply (List.map_injective_iff.mpr realVec_injective)
  rw [cache_real vectors steps hsteps,List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (orthogonal_real vectors _).symm

theorem cache_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) (vector : QVector dimension)
    (membership : vector ∈ cache (inputVectors basis) steps) (row : Fin dimension) :
    HeightBound (vector row) (coordinateHeight dimension height) := by
  rw [cache_prefix_eq _ steps hsteps] at membership
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp membership
  exact orthogonal_coordinate_height basis hdet height hentries _ row

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

theorem rationalTicks_length (value : ℚ) : (rationalTicks value).length=(Ratio.encode value).length := by
  rw [Ratio.encode_length]
  simp only [rationalTicks,List.length_append,List.length_replicate,List.length_flatMap,
    List.map_const',List.sum_replicate,List.length_cons,List.length_nil,nsmul_eq_mul,Nat.cast_id]
  omega

theorem vectorTicks_length (vector : List ℚ) :
    (vectorTicks vector).length=(encodeList Ratio.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [vectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      rationalTicks_length,EncodedList.cons_length] at *
    omega

theorem matrixTicks_length (matrix : List (List ℚ)) :
    (matrixTicks matrix).length=(encodeList (encodeList Ratio.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [matrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      vectorTicks_length,EncodedList.cons_length] at *
    omega

theorem dot_ofFn {dimension : ℕ} (first second : QVector dimension) :
    dot (List.ofFn first,List.ofFn second)=innerQ first second := by
  induction dimension with
  | zero => simp [dot,innerQ]
  | succ dimension ih =>
    simp only [dot,List.ofFn_succ,List.zip_cons_cons,List.map_cons,List.sum_cons]
    change first 0*second 0+dot (List.ofFn (Fin.tail first),List.ofFn (Fin.tail second))= _
    rw [ih]
    simp only [innerQ,Fin.sum_univ_succ,Fin.tail_def]

theorem vector_list_sum_apply {dimension : ℕ} (vectors : List (QVector dimension)) (index : Fin dimension) :
    vectors.sum index=(vectors.map (fun vector => vector index)).sum := by
  induction vectors with
  | nil => rfl
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,Pi.add_apply,ih]

theorem orthogonalStep_ofFn {dimension : ℕ} (previous : List (QVector dimension))
    (current : QVector dimension) :
    orthogonalStep (previous.map List.ofFn,List.ofFn current)=
      List.ofFn (RationalGramSchmidt.orthogonalStep previous current) := by
  apply List.ext_getElem
  · simp only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hrow : row < dimension := by
      simpa only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [orthogonalStep,List.length_ofFn,List.getElem_map,List.getElem_range,rowValue,
      List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some,List.map_map,Function.comp_def,
      projectionEntry,dot_ofFn,List.getElem_ofFn]
    simp only [RationalGramSchmidt.orthogonalStep,Pi.sub_apply,vector_list_sum_apply,List.map_map,
      Function.comp_def,projection,Pi.smul_apply,smul_eq_mul]

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeRationalGramSchmidtCacheBudget. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

noncomputable section

theorem encoded_list_length_bound {Value : Type} (encoding : Value → List Bool)
    (values : List Value) (bound : ℕ) (hbound : ∀ value ∈ values,(encoding value).length ≤ bound) :
    (encodeList encoding values).length ≤ values.length*(2*bound+1) := by
  induction values with
  | nil => simp only [EncodedList.nil,List.length_nil,zero_mul,le_refl]
  | cons head tail ih =>
    rw [EncodedList.cons_length,List.length_cons]
    have hhead := hbound head (by simp)
    have htail := ih (fun value membership => hbound value (by simp [membership]))
    nlinarith

theorem rational_encoding_height {value : ℚ} {height : ℕ} (hvalue : HeightBound value height) :
    (Ratio.encode value).length ≤ 3*height+10 := by
  apply Ratio.length_height
  constructor
  · have h := (Nat.cast_le (α:=ℤ)).mpr hvalue.1
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h
  · exact_mod_cast hvalue.2

theorem vector_encoding_height {dimension : ℕ} (vector : QVector dimension) (height : ℕ)
    (hvector : ∀ row,HeightBound (vector row) height) :
    (encodeList Ratio.encode (List.ofFn vector)).length ≤ dimension*(6*height+21) := by
  have h := encoded_list_length_bound Ratio.encode (List.ofFn vector) (3*height+10) (by
    intro value membership
    obtain ⟨row,rfl⟩ := List.mem_ofFn.mp membership
    exact rational_encoding_height (hvector row))
  simpa only [List.length_ofFn,show 2*(3*height+10)+1=6*height+21 by omega] using h

def cacheEncodingBound (dimension height : ℕ) : ℕ :=
  dimension*(2*dimension*(6*coordinateHeight dimension height+21)+1)

/-- The original determinant-derived height bound controls every complete
native cache-prefix encoding by one public polynomial. -/
theorem cache_encoding_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (encodeList (encodeList Ratio.encode) ((cache (inputVectors basis) steps).map List.ofFn)).length ≤
      cacheEncodingBound dimension height := by
  have h := encoded_list_length_bound (encodeList Ratio.encode)
    ((cache (inputVectors basis) steps).map List.ofFn) (dimension*(6*coordinateHeight dimension height+21)) (by
      intro vector membership
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp membership
      exact vector_encoding_height source _ (cache_coordinate_height basis hdet height hentries steps hsteps source hsource))
  rw [List.length_map,cache_length] at h
  apply h.trans
  unfold cacheEncodingBound
  calc
    steps*(2*(dimension*(6*coordinateHeight dimension height+21))+1) ≤
        dimension*(2*(dimension*(6*coordinateHeight dimension height+21))+1) := Nat.mul_le_mul_right _ hsteps
    _ = _ := by ring

/-- Prefix refinement is proved for the actual guarded list loop. Its
encoding bound is a local arithmetic invariant, discharged below from the
original integer matrix's determinant-derived size bounds. -/
theorem cacheFold_ofFn {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (ticks : List Unit)
    (hbudget : ∀ steps,steps ≤ count →
      (encodeList (encodeList Ratio.encode) ((cache vectors steps).map List.ofFn)).length ≤ ticks.length)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hsteps index)))).foldl cacheStep (ticks,[])=
      (ticks,(cache vectors steps).map List.ofFn) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps < count := by omega
    rw [List.ofFn_succ_last,List.foldl_append]
    change List.foldl cacheStep
      ((List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hprevious index)))).foldl cacheStep (ticks,[]))
      [List.ofFn (vectors ⟨steps,hstep⟩)] = _
    rw [ih hprevious,List.foldl_cons,List.foldl_nil]
    have hnext : (cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))]=
        (cache vectors (steps+1)).map List.ofFn := by
      rw [orthogonalStep_ofFn,cache,List.map_append,List.map_singleton,dif_pos hstep]
    have hguard : (matrixTicks ((cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))])).length ≤ ticks.length := by
      rw [hnext,matrixTicks_length]
      exact hbudget (steps+1) hsteps
    simp only [cacheStep,hguard,if_true]
    exact congrArg (fun matrix => (ticks,matrix)) hnext

/-- For every nonsingular input basis, the actual native cache agrees
exactly with rational Gram--Schmidt once supplied the public polynomial
encoding budget. No oracle or assumed GS algorithm appears. -/
theorem cached_integer_basis {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (ticks : List Unit) (hticks : cacheEncodingBound dimension height ≤ ticks.length) :
    cached (List.ofFn (fun index => List.ofFn (inputVectors basis index)),ticks)=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  have h := cacheFold_ofFn (inputVectors basis) ticks (fun steps hsteps =>
    (cache_encoding_bound basis hdet height hentries steps hsteps).trans hticks) dimension (le_refl dimension)
  change (List.ofFn (fun index : Fin dimension => List.ofFn (inputVectors basis index))).foldl cacheStep (ticks,[])=_ at h
  exact congrArg Prod.snd h

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

theorem integerTicks_length (value : ℤ) : (integerTicks value).length=(Signed.encode value).length := by
  simp only [integerTicks,List.length_append,List.length_replicate,List.length_map,Signed.encode_length]

theorem integerVectorTicks_length (vector : List ℤ) :
    (integerVectorTicks vector).length=(encodeList Signed.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerVectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerTicks_length,EncodedList.cons_length] at *
    omega

theorem integerMatrixTicks_length (matrix : List (List ℤ)) :
    (integerMatrixTicks matrix).length=(encodeList (encodeList Signed.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerMatrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerVectorTicks_length,EncodedList.cons_length] at *
    omega

theorem inputBudget_length (matrix : List (List ℤ)) :
    (inputBudget matrix).length=128*((integerMatrixTicks matrix).length+1)^4 := by
  simp only [inputBudget,List.length_flatMap,List.map_const',List.sum_replicate,List.length_replicate,
    List.length_append,List.length_singleton,nsmul_eq_mul,Nat.cast_id]
  ring

noncomputable section

/-- Coarse fixed polynomial suitable for unconditional guarded runtime. -/
theorem cacheEncodingBound_coarse (dimension height length : ℕ)
    (hdimension : dimension ≤ length) (hheight : height ≤ length) :
    cacheEncodingBound dimension height ≤ 128*(length+1)^4 := by
  have hlinear : length ≤ (length+1)^2 := by nlinarith
  have hcross : height*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hheight hdimension
      _ ≤ _ := by nlinarith
  have hsquare : dimension*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hdimension hdimension
      _ ≤ _ := by nlinarith
  have hcache : coordinateHeight dimension height ≤ 6*(length+1)^2 := by
    unfold coordinateHeight
    nlinarith
  unfold cacheEncodingBound
  calc
    _ ≤ (length+1)*(2*(length+1)*(6*(6*(length+1)^2)+21)+1) := by gcongr <;> omega
    _ ≤ _ := by
      have hpowerOne := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 1 ≤ 4 by omega)
      have hpowerTwo := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 2 ≤ 4 by omega)
      simp only [pow_one] at hpowerOne
      nlinarith

theorem inputColumns_dimension {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    dimension ≤ (integerMatrixTicks (inputColumns basis)).length := by
  rw [integerMatrixTicks_length]
  have h := EncodedList.length_le (encodeList Signed.encode) (inputColumns basis)
  simpa only [inputColumns,List.length_ofFn] using h

theorem inputColumns_entry_height {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (row column : Fin dimension) :
    |basis row column| ≤ (2 : ℤ)^(integerMatrixTicks (inputColumns basis)).length := by
  have hcolumn : List.ofFn (fun position => basis position column) ∈ inputColumns basis :=
    List.mem_ofFn.mpr ⟨column,rfl⟩
  have hentry : basis row column ∈ List.ofFn (fun position => basis position column) :=
    List.mem_ofFn.mpr ⟨row,rfl⟩
  have hcolumnSize := EncodedList.member_length (encodeList Signed.encode) (inputColumns basis) _ hcolumn
  have hentrySize := EncodedList.member_length Signed.encode _ _ hentry
  have hbits : (basis row column).natAbs.bits.length ≤ (integerMatrixTicks (inputColumns basis)).length := by
    rw [integerMatrixTicks_length]
    rw [Signed.encode_length] at hentrySize
    omega
  have hvalue := (NatBinary.le_two_pow_length (basis row column).natAbs).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits)
  have hcast := (Nat.cast_le (α:=ℤ)).mpr hvalue
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using hcast

theorem rationalColumns_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    rationalColumns (inputColumns basis)=List.ofFn (fun index => List.ofFn (inputVectors basis index)) := by
  simp only [rationalColumns,rationalColumn,inputColumns,List.map_ofFn,Function.comp_def]
  rfl

/-- The fully generated binary-input native cache exactly returns the
original nonsingular integer basis's rational orthogonalization. Every
size guard is discharged from the actual input encoding itself. -/
theorem inputCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    inputCache (inputColumns basis)=(cache (inputVectors basis) dimension).map List.ofFn := by
  unfold inputCache
  rw [rationalColumns_input]
  apply cached_integer_basis basis hdet (integerMatrixTicks (inputColumns basis)).length
    (inputColumns_entry_height basis)
  rw [inputBudget_length]
  exact cacheEncodingBound_coarse dimension _ _ (inputColumns_dimension basis) le_rfl

theorem transpose_input_rows {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    transpose (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=inputColumns basis := by
  apply List.ext_getElem
  · simp only [transpose,List.length_map,List.length_range,List.length_ofFn,inputColumns]
  · intro column hfirst hsecond
    have hcolumn : column < dimension := by
      simpa only [transpose,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [transpose,List.length_ofFn,List.getElem_map,List.getElem_range,transposeColumn,
      List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hcolumn,↓reduceDIte,Option.getD_some,
      inputColumns,List.getElem_ofFn]

/-- End-to-end exact native GS caching for the target's original row-major
integer matrix convention, with an unconditional polynomial-time program. -/
theorem basisCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    basisCache (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  rw [basisCache,transpose_input_rows,inputCache_correct basis hdet]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

/-- Analytical Cramer specification only. The native implementation below
will use the cached rational orthogonalization and reverse substitution. -/
def dualVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : QVector n :=
  fun row => (Matrix.cramer B.transpose (Pi.single i 1) row : ℚ)/(B.det : ℚ)

theorem dualVector_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (i k : Fin n) : innerQ (dualVector B i) (inputVectors B k)=if k=i then 1 else 0 := by
  have hD : (B.det : ℚ)≠0 := by exact_mod_cast hdet
  have hh:=congrFun (Matrix.mulVec_cramer B.transpose (Pi.single i 1)) k
  simp only [Matrix.mulVec,dotProduct,Matrix.det_transpose,Pi.smul_apply,smul_eq_mul,
    Matrix.transpose_apply,Pi.single_apply] at hh
  have hcast : (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))=
      (B.det : ℚ)*(if k=i then 1 else 0) := by exact_mod_cast hh
  calc
    _ = (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))/(B.det : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro row _
      simp only [innerQ,dualVector,inputVectors]
      ring
    _ = ((B.det : ℚ)*(if k=i then 1 else 0))/(B.det : ℚ) := by rw [hcast]
    _ = _ := by split_ifs <;> simp [hD]

/-- Pairings with the original input columns determine the entire real
vector, using the actual Euclidean dual basis. -/
theorem real_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : IntegerBasis.Space (dimension:=n))
    (h : ∀ k,inner ℝ x (IntegerBasis.realBasis B hdet k)=inner ℝ y (IntegerBasis.realBasis B hdet k)) : x=y := by
  apply (IntegerBasis.dualRealBasis B hdet).ext_elem
  intro k
  change ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet)).repr x) k=
    ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
      (IntegerBasis.realBasis B hdet)).repr y) k
  rw [LinearMap.BilinForm.dualBasis_repr_apply,LinearMap.BilinForm.dualBasis_repr_apply]
  exact h k

theorem rational_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : QVector n) (h : ∀ k,innerQ x (inputVectors B k)=innerQ y (inputVectors B k)) : x=y := by
  apply realVec_injective
  apply real_pairings_unique B hdet
  intro k
  rw [←inputVectors_real B hdet k,←innerQ_real,←innerQ_real,h k]

/-- A coarse binary determinant bound has polynomial exponent in dimension
and original integer entry height. -/
theorem determinant_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) : |B.det|≤(2 : ℤ)^((n+H)*n) := by
  have hdim : (n : ℤ)≤2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hfac : (n.factorial : ℤ)≤2^(n*n) := by
    calc
      _ ≤ (n : ℤ)^n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ ((2 : ℤ)^n)^n := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim _
      _ = _ := by rw [←pow_mul]
  have hh:=Matrix.det_le (abv:=AbsoluteValue.abs) hentries
  have hd : |B.det|≤(n.factorial : ℤ)*((2 : ℤ)^H)^n := by
    simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using hh
  calc
    _ ≤ (n.factorial : ℤ)*((2 : ℤ)^H)^n := hd
    _ ≤ (2 : ℤ)^(n*n)*((2 : ℤ)^H)^n := mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring

theorem cramer_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    |Matrix.cramer B.transpose (Pi.single i 1) row|≤(2 : ℤ)^((n+H)*n) := by
  rw [Matrix.cramer_apply]
  apply determinant_binary_bound _ H
  intro r c
  simp only [Matrix.updateCol_apply,Matrix.transpose_apply]
  split_ifs
  · simp only [Pi.single_apply]
    split_ifs <;> simp
    exact one_le_pow₀ (by norm_num : (1 : ℤ)≤2)
  · exact hentries c r

theorem dualVector_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    HeightBound (dualVector B i row) (dualHeight n H) := by
  have hnum : (Matrix.cramer B.transpose (Pi.single i 1) row).natAbs≤2^((n+H)*n) := by
    have hh : ((Matrix.cramer B.transpose (Pi.single i 1) row).natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using cramer_binary_bound B H hentries i row
    exact_mod_cast hh
  have hden : B.det.natAbs≤2^((n+H)*n) := by
    have hh : (B.det.natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using determinant_binary_bound B H hentries
    exact_mod_cast hh
  have hh:=(HeightBound.of_int hnum).div (HeightBound.of_int hden)
  simpa only [dualVector,dualHeight,two_mul] using hh

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeRationalInverseRecurrence. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

@[simp] theorem innerQ_sub_left {n : ℕ} (x y z : QVector n) :
    innerQ (x-y) z=innerQ x z-innerQ y z := by simp [innerQ,sub_mul,Finset.sum_sub_distrib]

@[simp] theorem innerQ_smul_left {n : ℕ} (a : ℚ) (x y : QVector n) :
    innerQ (a • x) y=a*innerQ x y := by simp [innerQ,Finset.mul_sum,mul_assoc]

theorem innerQ_sum_left {n : ℕ} {J : Type*} (s : Finset J) (x : J → QVector n) (y : QVector n) :
    innerQ (∑ j∈s,x j) y=∑ j∈s,innerQ (x j) y := by
  simp only [innerQ,Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- One reverse triangular substitution step. Its only arithmetic operands
are the cached original rational orthogonalization and future dual columns. -/
def dualStep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (cache : Fin n → QVector n) (i : Fin n) : QVector n :=
  (squaredNorm (inputVectors B) i)⁻¹ • orthogonal (inputVectors B) i-
    ∑ j∈Finset.Ioi i,upper (inputVectors B) i j • cache j

noncomputable section

theorem dualStep_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i k : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) :
    innerQ (dualStep B cache i) (inputVectors B k)=if k=i then 1 else 0 := by
  rw [dualStep,innerQ_sub_left,innerQ_smul_left,innerQ_sum_left]
  simp only [innerQ_smul_left]
  have hfirst : (squaredNorm (inputVectors B) i)⁻¹*innerQ (orthogonal (inputVectors B) i) (inputVectors B k)=
      upper (inputVectors B) i k := by unfold upper;ring
  rw [hfirst]
  have hsum : (∑ j∈Finset.Ioi i,upper (inputVectors B) i j*innerQ (cache j) (inputVectors B k))=
      if i< k then upper (inputVectors B) i k else 0 := by
    calc
      _ = ∑ j∈Finset.Ioi i,if k=j then upper (inputVectors B) i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcache j (Finset.mem_Ioi.mp hj),dualVector_pairing B hdet]
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_Ioi]
  rw [hsum]
  by_cases he : k=i
  · subst k
    simp [upper_diagonal _ (inputVectors_independent B hdet)]
  · by_cases hi : i< k
    · simp [hi,he]
    · have hk : k< i := lt_of_le_of_ne (le_of_not_gt hi) he
      rw [upper_triangular _ i k hk]
      simp [hi,he]

theorem dualStep_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) : dualStep B cache i=dualVector B i := by
  apply rational_pairings_unique B hdet
  intro k
  rw [dualStep_pairing B hdet cache i k hcache,dualVector_pairing B hdet]

/-- A complete matrix cache is updated from the last column backwards.
Every completed column is already a final original-input dual column. -/
def dualCache {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → QVector n
  | 0 => fun _ => 0
  | steps+1 =>
      let previous :=dualCache B steps
      if h : steps< n then
        let i : Fin n :=⟨n-1-steps,by omega⟩
        Function.update previous i (dualStep B previous i)
      else previous

theorem dualCache_formula {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (steps : ℕ) (hsteps : steps≤ n) (j : Fin n) :
    dualCache B steps j=if n-steps≤ j.val then dualVector B j else 0 := by
  induction steps generalizing j with
  | zero =>
    have hj : ¬n≤ j.val := by omega
    simp [dualCache,hj]
  | succ steps ih =>
    have hs : steps< n := by omega
    let i : Fin n :=⟨n-1-steps,by omega⟩
    have hf : ∀ k,i< k → dualCache B steps k=dualVector B k := by
      intro k hk
      rw [ih (by omega) k]
      have ht : n-steps≤ k.val := by change i.val< k.val at hk;dsimp [i] at hk;omega
      simp only [if_pos ht]
    have he:=dualStep_correct B hdet (dualCache B steps) i hf
    change (if h : steps< n then Function.update (dualCache B steps)
      (⟨n-1-steps,by omega⟩ : Fin n) (dualStep B (dualCache B steps) ⟨n-1-steps,by omega⟩) else dualCache B steps) j=_
    rw [dif_pos hs]
    change Function.update (dualCache B steps) i (dualStep B (dualCache B steps) i) j=_
    rw [he]
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      have ht : n-(steps+1)≤ i.val := by dsimp [i];omega
      simp only [if_pos ht]
    · rw [Function.update_of_ne hj,ih (by omega) j]
      have hv : j.val≠n-1-steps := by intro h;apply hj;exact Fin.ext h
      have ht : (n-steps≤ j.val)=(n-(steps+1)≤ j.val) := propext (by omega)
      simp only [ht]

theorem dualCache_complete {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    dualCache B n=dualVector B := by
  funext j
  rw [dualCache_formula B hdet n (le_refl n)]
  simp

theorem dualCache_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H)
    (steps : ℕ) (hs : steps≤ n) (j row : Fin n) :
    HeightBound (dualCache B steps j row) (coordinateHeight n H) := by
  rw [dualCache_formula B hdet steps hs]
  split_ifs
  · exact (dualVector_height B H hentries j row).mono (by unfold dualHeight coordinateHeight;nlinarith)
  · exact HeightBound.zero.mono (Nat.zero_le _)

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeRationalInverseRefinement. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

noncomputable section

def matrixOf {n : ℕ} (vectors : Fin n → QVector n) : List (List ℚ) :=
  List.ofFn (fun j => List.ofFn (vectors j))

def context {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Context :=
  (matrixOf (inputVectors B),matrixOf (orthogonal (inputVectors B)))

theorem term_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i row j : Fin n) :
    term ((((context B,matrixOf cache),i.val),row.val),j.val)=
      if i< j then upper (inputVectors B) i j*cache j row else 0 := by
  simp only [term,context,matrixOf,List.getElem?_ofFn,i.isLt,j.isLt,row.isLt,
    ↓reduceDIte,Option.getD_some,dot_ofFn]
  rfl

theorem column_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i : Fin n) :
    column ((context B,matrixOf cache),i.val)=List.ofFn (dualStep B cache i) := by
  apply List.ext_getElem
  · simp only [column,context,matrixOf,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hr : row< n := by simpa only [List.length_ofFn] using hsecond
    let r : Fin n :=⟨row,hr⟩
    have hs : (List.range n).map (fun j => term ((((context B,matrixOf cache),i.val),row),j))=
        List.ofFn (fun j : Fin n => if i< j then upper (inputVectors B) i j*cache j r else 0) := by
      apply List.ext_getElem
      · simp
      · intro j hj hk
        have hjn : j< n := by simpa using hj
        simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using term_ofFn B cache i r ⟨j,hjn⟩
    have hi : Finset.Ioi i=Finset.univ.filter (fun j => i< j) := by ext j;simp
    have hlen : (context B).1.length=n := by simp [context,matrixOf]
    simp only [column,hlen,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change entry ((((context B,matrixOf cache),i.val),row))=dualStep B cache i r
    simp only [entry,hlen]
    rw [hs,Fin.sum_ofFn]
    simp only [context,matrixOf,List.getElem?_ofFn,i.isLt,hr,↓reduceDIte,Option.getD_some,dot_ofFn]
    simp only [dualStep,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,hi,Finset.sum_filter,squaredNorm,ite_apply,Pi.zero_apply]
    ring

theorem replaceColumn_ofFn {n : ℕ} (cache : Fin n → QVector n) (i : Fin n) (value : QVector n) :
    replaceColumn ((matrixOf cache,i.val),List.ofFn value)=matrixOf (Function.update cache i value) := by
  apply List.ext_getElem
  · simp [replaceColumn,matrixOf]
  · intro j hj hk
    have hjn : j< n := by simpa only [matrixOf,List.length_ofFn] using hk
    let k : Fin n :=⟨j,hjn⟩
    simp only [replaceColumn,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change (if j=i.val then List.ofFn value else (List.ofFn (fun j => List.ofFn (cache j)))[j]?.getD [])=
      List.ofFn (Function.update cache i value k)
    by_cases h : k=i
    · subst k
      have hjval : j=i.val := congrArg Fin.val h
      simp only [hjval,ite_true,Function.update_self]
    · have hji : j≠i.val := by intro he;apply h;exact Fin.ext he
      simp only [hji,if_false,List.getElem?_ofFn,hjn,↓reduceDIte,Option.getD_some,Function.update_of_ne h]
      rfl

/-- The Cramer bound controls every whole reverse-substitution cache. -/
theorem dualCache_encoding_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤ (2 : ℤ)^H) (steps : ℕ) (hs : steps≤ n) :
    (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ cacheEncodingBound n H := by
  have he := encoded_list_length_bound (encodeList Ratio.encode) (matrixOf (dualCache B steps))
    (n*(6*coordinateHeight n H+21)) (by
      intro vector hv
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hv
      exact vector_encoding_height _ _ (fun row => dualCache_height B hdet H hentries steps hs j row))
  simpa only [matrixOf,List.length_ofFn,cacheEncodingBound,Nat.mul_assoc] using he

theorem step_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (steps : ℕ) (hs : steps< n)
    (hb : (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B (steps+1)))).length≤ ticks.length) :
    step (context B,(ticks,matrixOf (dualCache B steps))) steps=
      (context B,(ticks,matrixOf (dualCache B (steps+1)))) := by
  let i : Fin n :=⟨n-1-steps,by omega⟩
  have hn : replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val))=matrixOf (dualCache B (steps+1)) := by
    rw [column_ofFn,replaceColumn_ofFn]
    rw [dualCache,dif_pos hs]
  have hg : (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length := by
    rw [hn,matrixTicks_length]
    exact hb
  have hlen : (context B).1.length=n := by simp [context,matrixOf]
  simp only [step,hlen]
  change (context B,(ticks,if (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length then _ else []))=_
  rw [if_pos hg,hn]

theorem fold_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ ticks.length)
    (steps : ℕ) (hs : steps≤ n) :
    (List.range steps).foldl step (context B,(ticks,matrixOf (fun _ : Fin n => (0 : QVector n))))=
      (context B,(ticks,matrixOf (dualCache B steps))) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [List.range_succ,List.foldl_append,ih (by omega),List.foldl_cons,List.foldl_nil]
    exact step_ofFn B ticks steps (by omega) (hb (steps+1) hs)

theorem inputRows_dimension {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    n≤ (integerMatrixTicks (inputRows B)).length := inputColumns_dimension B.transpose

theorem inputRows_entry_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (row col : Fin n) :
    |B row col|≤ (2 : ℤ)^(integerMatrixTicks (inputRows B)).length :=
  inputColumns_entry_height B.transpose col row

theorem basisCache_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    basisCache (inputRows B)=matrixOf (orthogonal (inputVectors B)) := by
  rw [inputRows,basisCache_correct B hdet,cache_prefix_eq _ n (le_refl n),List.map_ofFn]
  rfl

/-- Exact refinement of the guarded reverse loop for every nonsingular
original integer input; the public bit-size guard never changes its data. -/
theorem cached_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    cached (inputRows B)=matrixOf (dualVector B) := by
  have hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ (inputBudget (inputRows B)).length := by
    intro steps hs
    apply (dualCache_encoding_bound B hdet (integerMatrixTicks (inputRows B)).length
      (inputRows_entry_height B) steps hs).trans
    rw [inputBudget_length]
    exact cacheEncodingBound_coarse n _ _ (inputRows_dimension B) le_rfl
  have ho : rationalColumns (transpose (inputRows B))=matrixOf (inputVectors B) := by
    rw [inputRows,transpose_input_rows,rationalColumns_input]
    rfl
  have hz : (matrixOf (inputVectors B)).map (fun row => row.map (fun _ => (0 : ℚ)))=
      matrixOf (fun _ : Fin n => (0 : QVector n)) := by
    simp only [matrixOf,List.map_ofFn,Function.comp_def]
    rfl
  unfold cached
  rw [ho,basisCache_matrix B hdet]
  dsimp only
  rw [hz]
  have hl : (inputRows B).length=n := by simp [inputRows]
  rw [hl]
  change ((List.range n).foldl step
    (context B,(inputBudget (inputRows B),matrixOf (fun _ : Fin n => (0 : QVector n))))).2.2=_
  rw [fold_ofFn B _ hb n (le_refl n),dualCache_complete B hdet]

theorem transposeRational_ofFn {n : ℕ} (v : Fin n → QVector n) :
    transposeRational (matrixOf v)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => v col row)) := by
  apply List.ext_getElem
  · simp [transposeRational,matrixOf]
  · intro row hr hs
    have hrow : row< n := by simpa using hs
    simp only [transposeRational,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some]

/-- Row-major output is exactly the original matrix inverse transpose. -/
theorem _root_.solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    current (inputRows B)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => dualVector B col row)) := by
  rw [current,cached_correct B hdet,transposeRational_ofFn]

end

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule11
