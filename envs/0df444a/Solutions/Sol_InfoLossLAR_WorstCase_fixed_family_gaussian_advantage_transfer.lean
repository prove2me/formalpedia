-- Prove2me | solution 1 for InfoLossLAR.WorstCase.fixed_family_gaussian_advantage_transfer
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T00:46:35.939021+00:00
-- url     : https://prove2.me/submissions/d41da16c-b436-461f-aaf1-197106b405e5

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_09
import Mathlib
import Theorems.Thm_AFT_FiniteDist_l1_independent_fin_le
import Theorems.Thm_AFT_FiniteDist_totalVariation_eq_half_l1
import Theorems.Thm_CurrentAFT_ActualConstructiveSampler_accuracy_eventually
import Theorems.Thm_InfoLossLAR_WorstCase_lemma_5_2
import Theorems.Thm_Integration9_9_GaussianRankOnePre_current_value_clipped
set_option maxRecDepth 65536
namespace P2Mf6bd8d28
end P2Mf6bd8d28
open _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits renaming exists_code → AFT.BinaryArithmetic.RationalBits.exists_code
open _root_.InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics.HeightBound renaming mono → AFT.RationalNumerics.HeightBound.mono
open _root_.InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics.HeightBound renaming mul → AFT.RationalNumerics.HeightBound.mul
open _root_.InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics.HeightBound renaming one → AFT.RationalNumerics.HeightBound.one
open _root_.InfoLossLARNativeSupplements.he83cfe7a7db39d44.CurrentAFT.BinaryFiniteProduct renaming current_value → CurrentAFT.BinaryFiniteProduct.current_value
open _root_.InfoLossLARNativeSupplements.hab90893a8a9293a2.CurrentAFT.BinaryListSum renaming current_value → CurrentAFT.BinaryListSum.current_value
open _root_.InfoLossLARNativeSupplements.hb39aff037bdc4326.CurrentAFT.BinarySparseCycleSemantic renaming current_value → CurrentAFT.BinarySparseCycleSemantic.current_value
open _root_.InfoLossLARNativeSupplements.hf362d6b0d865f5c6.CurrentAFT.BinaryTouchedCycleRanks renaming positions_value → CurrentAFT.BinaryTouchedCycleRanks.positions_value
open _root_.InfoLossLARNativeSupplements.h4cdf4f6ad2d19d90.CurrentAFT.BinaryTupleSum renaming current_value → CurrentAFT.BinaryTupleSum.current_value
open _root_.InfoLossLARNativeSupplements.h78d75bb492074482.CurrentAFT.CountedBoundedRootTags.Tag renaming card → CurrentAFT.CountedBoundedRootTags.Tag.card
open _root_.InfoLossLARNativeSupplements.hf6e7f4bd634f80a9.CurrentAFT.CountedBoundedRootTags.Tag renaming read_value → CurrentAFT.CountedBoundedRootTags.Tag.read_value
open _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram renaming encode_value → CurrentAFT.CurrentPublicShiftProgram.encode_value
section
set_option backward.isDefEq.respectTransparency false
namespace AFT
open scoped BigOperators
end AFT
namespace AFT
theorem _root_.P2Mf6bd8d28.h25 (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] _root_.AFT.zeroSumLattice n)
    (B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (c w : Fin (n + 1) → ℤ) (a : Fin n → ℤ)
    (ha : _root_.AFT.pathLoad n a = w - c) (x : (Fin n → ℤ) × ℤ) :
    _root_.AFT.roundingLoad n c (_root_.AFT.blockTransport n (_root_.AFT.edgeBasisChange n treeBasis) B a x) =
      (treeBasis (B x.1) : Fin (n + 1) → ℤ) + x.2 • w := by
  simp only [_root_.AFT.roundingLoad, _root_.AFT.blockTransport, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.AFT.pathLoad_add, _root_.AFT.pathLoad_smul, _root_.AFT.pathLoad_edgeBasisChange, ha, smul_sub]
  abel
open _root_.P2Mf6bd8d28 renaming h25 → _Pp
end AFT
open _root_.P2Mf6bd8d28 renaming h25 → _Pp
namespace AFT
end AFT
namespace AFT
theorem _root_.P2Mf6bd8d28.h23 (n : ℕ) (j : Fin n) :
    _root_.AFT.pathLoad n (fun k => if k = j then 1 else 0) =
      fun i => (if i = j.castSucc then 1 else 0) - (if i = j.succ then 1 else 0) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · have ht : Fin.tail (fun k : Fin (n + 1) => if k = 0 then (1 : ℤ) else 0) = 0 := by
          funext k
          change (if k.succ = 0 then (1 : ℤ) else 0) = 0
          simp
        funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · simp [_root_.AFT.pathLoad]
        · simp [_root_.AFT.pathLoad, ht]
          change (if l = 0 then (1 : ℤ) else 0) =
            (if l.succ = (0 : Fin (n + 1)).succ then 1 else 0)
          simp only [Fin.succ_inj]
      · have ht : Fin.tail (fun l : Fin (n + 1) => if l = k.succ then (1 : ℤ) else 0) =
            (fun l : Fin n => if l = k then 1 else 0) := by
          funext l
          change (if l.succ = k.succ then (1 : ℤ) else 0) =
            (if l = k then 1 else 0)
          simp
        funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · simp [_root_.AFT.pathLoad, eq_comm]
        · simp [_root_.AFT.pathLoad, ht, ih]
          intro _
          exact (Fin.succ_ne_zero k).symm
open _root_.P2Mf6bd8d28 renaming h23 → _Pn
end AFT
open _root_.P2Mf6bd8d28 renaming h23 → _Pn
end
open _root_.P2Mf6bd8d28 renaming h23 → _Pn
open _root_.P2Mf6bd8d28 renaming h25 → _Pp
section
namespace AFT
namespace FiniteDist
open scoped Classical
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
theorem _root_.P2Mf6bd8d28.h11 (p : _root_.AFT.FiniteDist α) (e : α ≃ β)
    (c : γ) (b : β) (d : γ) :
    (p.map (fun a => (e a, c))).weight (b, d) =
      if c = d then p.weight (e.symm b) else 0 := by
  by_cases h : c = d
  · subst d
    simp [_root_.AFT.FiniteDist.map_weight, e.apply_eq_iff_eq_symm_apply]
  · simp [_root_.AFT.FiniteDist.map_weight, Prod.mk.injEq, h]
open _root_.P2Mf6bd8d28 renaming h11 → _Pb
theorem _root_.P2Mf6bd8d28.h14 [Nonempty β] (p : _root_.AFT.FiniteDist α)
    (e : α → β ≃ β) (side : α → γ) :
    p.mix (fun a => (_root_.AFT.FiniteDist.uniform β).map (fun b => (e a b, side a))) =
      (_root_.AFT.FiniteDist.uniform β).prod (p.map side) := by
  ext bc
  rcases bc with ⟨b, c⟩
  simp only [_root_.AFT.FiniteDist.mix_weight, _Pb, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.uniform_weight]
  rw [_root_.AFT.FiniteDist.map_weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : side a = c <;> simp [h, mul_comm]
open _root_.P2Mf6bd8d28 renaming h14 → _Pe
theorem _root_.P2Mf6bd8d28.h12 (p : _root_.AFT.FiniteDist α) (q : _root_.AFT.FiniteDist β)
    (e : α ≃ γ) (f : β ≃ δ) :
    (p.prod q).map (e.prodCongr f) = (p.map e).prod (q.map f) := by
  ext cd
  rw [_root_.AFT.FiniteDist.map_equiv_weight (p.prod q) (e.prodCongr f)]
  simp only [_root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.map_equiv_weight]
  rfl
open _root_.P2Mf6bd8d28 renaming h12 → _Pc
theorem _root_.P2Mf6bd8d28.h15 [Nonempty β] [Nonempty γ]
    (p : _root_.AFT.FiniteDist α) (e : α → β ≃ β) (f : α → γ ≃ γ) :
    p.mix (fun a => ((_root_.AFT.FiniteDist.uniform β).prod (_root_.AFT.FiniteDist.uniform γ)).map ((e a).prodCongr (f a))) =
      (_root_.AFT.FiniteDist.uniform β).prod (_root_.AFT.FiniteDist.uniform γ) := by
  simp only [_Pc, _root_.AFT.FiniteDist.uniform_map_equiv, _root_.AFT.FiniteDist.mix_const]
open _root_.P2Mf6bd8d28 renaming h15 → _Pf
end FiniteDist
open _root_.P2Mf6bd8d28 renaming h11 → _Pb
open _root_.P2Mf6bd8d28 renaming h12 → _Pc
open _root_.P2Mf6bd8d28 renaming h14 → _Pe
open _root_.P2Mf6bd8d28 renaming h15 → _Pf
end AFT
open _root_.P2Mf6bd8d28 renaming h11 → _Pb
open _root_.P2Mf6bd8d28 renaming h12 → _Pc
open _root_.P2Mf6bd8d28 renaming h14 → _Pe
open _root_.P2Mf6bd8d28 renaming h15 → _Pf
end
open _root_.P2Mf6bd8d28 renaming h11 → _Pb
open _root_.P2Mf6bd8d28 renaming h12 → _Pc
open _root_.P2Mf6bd8d28 renaming h14 → _Pe
open _root_.P2Mf6bd8d28 renaming h15 → _Pf
namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.minimumMass
end AFT.FiniteDist.minimumMass
namespace AFT.FiniteDist.permutationMixture
end AFT.FiniteDist.permutationMixture
section
namespace AFT
namespace GaussianSource
open scoped BigOperators Classical ENNReal
theorem _root_.P2Mf6bd8d28.h16 (p : PMF ℤ) (dimension : ℕ)
    (vector : Fin dimension → ℤ) :
    _root_.AFT.GaussianSource.independentCoordinates p dimension vector = ∏ i, p (vector i) := by
  induction dimension with
  | zero =>
      simp [_root_.AFT.GaussianSource.independentCoordinates, Subsingleton.elim vector (fun i => Fin.elim0 i)]
  | succ dimension ih =>
      have hpair (head : ℤ) (tail : Fin dimension → ℤ) :
          vector = Fin.cons head tail ↔ head = vector 0 ∧ tail = Fin.tail vector := by
        constructor
        · intro h
          constructor
          · simpa using (congrFun h 0).symm
          · simpa using (congrArg Fin.tail h).symm
        · rintro ⟨rfl, rfl⟩
          exact (Fin.cons_self_tail vector).symm
      have hmap (head : ℤ) :
          ((_root_.AFT.GaussianSource.independentCoordinates p dimension).map (Fin.cons head)) vector =
            if head = vector 0 then _root_.AFT.GaussianSource.independentCoordinates p dimension (Fin.tail vector) else 0 := by
        rw [PMF.map_apply]
        by_cases h : head = vector 0 <;> simp [hpair, h]
      simp only [_root_.AFT.GaussianSource.independentCoordinates, PMF.bind_apply, hmap, mul_ite, mul_zero]
      rw [tsum_ite_eq, Fin.prod_univ_succ]
      rw [ih]
      rfl
open _root_.P2Mf6bd8d28 renaming h16 → _Pg
theorem _root_.P2Mf6bd8d28.h18 (dimension : ℕ) (width : ℝ) (hwidth : 0 < width)
    (vector : Fin dimension → ℤ) :
    _root_.AFT.GaussianSource.latticeGaussian dimension width hwidth vector =
      ENNReal.ofReal (Real.exp (-(Real.pi / width ^ 2) *
        ∑ coordinate, (vector coordinate : ℝ) ^ 2)) * (_root_.AFT.GaussianSource.normalizer width)⁻¹ ^ dimension := by
  rw [_root_.AFT.GaussianSource.latticeGaussian, _Pg]
  simp only [_root_.AFT.GaussianSource.integerGaussian, PMF.normalize_apply]
  change (∏ i, ENNReal.ofReal (_root_.AFT.GaussianSource.weight width (vector i)) * (_root_.AFT.GaussianSource.normalizer width)⁻¹) = _
  rw [Finset.prod_mul_distrib]
  have hweight : (∏ i, ENNReal.ofReal (_root_.AFT.GaussianSource.weight width (vector i))) =
      ENNReal.ofReal (Real.exp (-(Real.pi / width ^ 2) *
        ∑ coordinate, (vector coordinate : ℝ) ^ 2)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => le_of_lt (_root_.AFT.GaussianSource.weight_pos width (vector i)))]
    congr 1
    simp only [_root_.AFT.GaussianSource.weight, ← Real.exp_sum, ← Finset.mul_sum]
  rw [hweight]
  simp
open _root_.P2Mf6bd8d28 renaming h18 → _Pi
theorem _root_.P2Mf6bd8d28.h19 (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    (∑' vector : Fin dimension → ℤ, ENNReal.ofReal (_root_.AFT.GaussianSource.latticeWeight dimension width vector)) =
      (_root_.AFT.GaussianSource.normalizer width) ^ dimension := by
  have hpoint (vector : Fin dimension → ℤ) :
      ENNReal.ofReal (_root_.AFT.GaussianSource.latticeWeight dimension width vector) =
        _root_.AFT.GaussianSource.latticeGaussian dimension width hwidth vector * (_root_.AFT.GaussianSource.normalizer width) ^ dimension := by
    rw [_Pi, mul_assoc, ← mul_pow,
      ENNReal.inv_mul_cancel (_root_.AFT.GaussianSource.normalizer_ne_zero width) (_root_.AFT.GaussianSource.normalizer_ne_top width hwidth)]
    simp [_root_.AFT.GaussianSource.latticeWeight]
  simp_rw [hpoint]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
open _root_.P2Mf6bd8d28 renaming h19 → _Pj
end GaussianSource
open _root_.P2Mf6bd8d28 renaming h16 → _Pg
open _root_.P2Mf6bd8d28 renaming h18 → _Pi
open _root_.P2Mf6bd8d28 renaming h19 → _Pj
end AFT
open _root_.P2Mf6bd8d28 renaming h16 → _Pg
open _root_.P2Mf6bd8d28 renaming h18 → _Pi
open _root_.P2Mf6bd8d28 renaming h19 → _Pj
end
open _root_.P2Mf6bd8d28 renaming h16 → _Pg
open _root_.P2Mf6bd8d28 renaming h18 → _Pi
open _root_.P2Mf6bd8d28 renaming h19 → _Pj
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.independentCoordinates
end AFT.GaussianSource.independentCoordinates
namespace AFT.GaussianSource.independentCoordinates.match_1
end AFT.GaussianSource.independentCoordinates.match_1
namespace AFT.GaussianSource.integerGaussian
end AFT.GaussianSource.integerGaussian
namespace AFT.GaussianSource.latticeGaussian
end AFT.GaussianSource.latticeGaussian
namespace AFT.GaussianSource.latticeWeight
end AFT.GaussianSource.latticeWeight
namespace AFT.GaussianSource.residueGaussian
end AFT.GaussianSource.residueGaussian
namespace AFT.GaussianSource.weight
end AFT.GaussianSource.weight
section
namespace AFT.GaussianSource
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h20 (width : ℝ) :
    _root_.AFT.GaussianSource.realNormalizer width = (_root_.AFT.GaussianSource.normalizer width).toReal := by
  rw [_root_.AFT.GaussianSource.normalizer, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp [_root_.AFT.GaussianSource.realNormalizer, ENNReal.toReal_ofReal, (_root_.AFT.GaussianSource.weight_pos width _).le]
open _root_.P2Mf6bd8d28 renaming h20 → _Pk
set_option backward.isDefEq.respectTransparency false in
theorem _root_.P2Mf6bd8d28.h17 (width : ℝ) (hw : 0 < width) (z : ℤ) :
    (_root_.AFT.GaussianSource.integerGaussian width hw z).toReal = _root_.AFT.GaussianSource.weight width z / _root_.AFT.GaussianSource.realNormalizer width := by
  rw [_root_.AFT.GaussianSource.integerGaussian, PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (_root_.AFT.GaussianSource.weight_pos width z).le]
  change _root_.AFT.GaussianSource.weight width z * (_root_.AFT.GaussianSource.normalizer width).toReal⁻¹ = _
  rw [← _Pk]
  rfl
open _root_.P2Mf6bd8d28 renaming h17 → _Ph
end AFT.GaussianSource
open _root_.P2Mf6bd8d28 renaming h17 → _Ph
open _root_.P2Mf6bd8d28 renaming h20 → _Pk
end
open _root_.P2Mf6bd8d28 renaming h17 → _Ph
open _root_.P2Mf6bd8d28 renaming h20 → _Pk
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
theorem _root_.P2Mf6bd8d28.h13 (first : _root_.AFT.FiniteDist A) (second : _root_.AFT.FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1, g pair.2)) = (first.map f).prod (second.map g) := by
  apply _root_.AFT.FiniteDist.ext
  rintro ⟨c, d⟩
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.prod_weight, Fintype.sum_prod_type, Prod.mk.injEq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all
open _root_.P2Mf6bd8d28 renaming h13 → _Pd
end
open _root_.P2Mf6bd8d28 renaming h13 → _Pd
end AFT.FiniteDist
open _root_.P2Mf6bd8d28 renaming h13 → _Pd
namespace AFT.SafeConvolution
open scoped BigOperators Classical
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]
end
end AFT.SafeConvolution
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]
attribute [local instance] _root_.AFT.RepresentedPolynomial.jointPairFinDecEq
end
end AFT.RepresentedPolynomial
namespace AFT.GaussianSource
noncomputable section
end
end AFT.GaussianSource
namespace AFT.V7Calibration
open GaussianSource SafeConvolution RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
end
end AFT.V7Calibration
end
open _root_.P2Mf6bd8d28 renaming h13 → _Pd
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.SignedResult
end AFT.BinaryArithmetic.SignedResult
namespace AFT.BinaryArithmetic.SignedResult.mk
end AFT.BinaryArithmetic.SignedResult.mk
namespace AFT.BinaryArithmetic.signedAdd
end AFT.BinaryArithmetic.signedAdd
namespace AFT.BinaryArithmetic.storeData
end AFT.BinaryArithmetic.storeData
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
namespace IntegerBits
theorem _root_.P2Mf6bd8d28.h1 (count : ℕ) (term : Fin count → _root_.AFT.RationalRejectionProgram.CountedValue _root_.AFT.BinaryArithmetic.IntegerBits) :
    (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin count term).value.decode=∑ index,(term index).value.decode := by
  induction count with
  | zero => simp [_root_.AFT.BinaryArithmetic.IntegerBits.sumFin]
  | succ count ih => simp only [_root_.AFT.BinaryArithmetic.IntegerBits.sumFin,_root_.AFT.BinaryArithmetic.IntegerBits.add_value,ih,Fin.sum_univ_castSucc]
open _root_.P2Mf6bd8d28 renaming h1 → _P1
end IntegerBits
open _root_.P2Mf6bd8d28 renaming h1 → _P1
end AFT.BinaryArithmetic
open _root_.P2Mf6bd8d28 renaming h1 → _P1
end
open _root_.P2Mf6bd8d28 renaming h1 → _P1
namespace AFT.BinaryArithmetic.IntegerBits
end AFT.BinaryArithmetic.IntegerBits
namespace AFT.BinaryArithmetic.IntegerBits.decode
end AFT.BinaryArithmetic.IntegerBits.decode
namespace AFT.BinaryArithmetic.IntegerBits.mk
end AFT.BinaryArithmetic.IntegerBits.mk
namespace AFT.BinaryArithmetic.IntegerBits.multiply
end AFT.BinaryArithmetic.IntegerBits.multiply
namespace AFT.BinaryArithmetic.IntegerBits.subtract
end AFT.BinaryArithmetic.IntegerBits.subtract
namespace AFT.BinaryArithmetic.IntegerBits.sumFin
end AFT.BinaryArithmetic.IntegerBits.sumFin
namespace AFT.BinaryArithmetic.IntegerBits.sumFin.match_1
end AFT.BinaryArithmetic.IntegerBits.sumFin.match_1
namespace AFT.BinaryArithmetic.IntegerBits.zero
end AFT.BinaryArithmetic.IntegerBits.zero
section
namespace AFT.BinaryArithmetic.IntegerBits
open AFT.RationalRejectionProgram
theorem _root_.P2Mf6bd8d28.h0 (input : _root_.AFT.BinaryArithmetic.IntegerBits) (modulus : List Bool) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus)
    (hdiv : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ input.decode) :
    (_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient input modulus).value.decode=input.decode/(_root_.AFT.BinaryArithmetic.value modulus : ℤ) := by
  have hv := (_root_.AFT.BinaryArithmetic.divide_value input.digits modulus hq).1
  cases hs : input.negative with
  | false => simp only [_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,Bool.false_eq_true,ite_false,hv,Int.natCast_ediv]
  | true =>
      have hd : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ (_root_.AFT.BinaryArithmetic.value input.digits : ℤ) := by
        simpa only [_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,ite_true,dvd_neg] using hdiv
      simp only [_root_.AFT.BinaryArithmetic.IntegerBits.exactQuotient,_root_.AFT.BinaryArithmetic.IntegerBits.decode,_root_.AFT.BinaryArithmetic.signedValue,hs,ite_true,hv,Int.natCast_ediv,Int.neg_ediv_of_dvd hd]
open _root_.P2Mf6bd8d28 renaming h0 → _P0
end AFT.BinaryArithmetic.IntegerBits
open _root_.P2Mf6bd8d28 renaming h0 → _P0
end
open _root_.P2Mf6bd8d28 renaming h0 → _P0
namespace AFT.blockTransport
end AFT.blockTransport
namespace AFT.injectionColumn
end AFT.injectionColumn
namespace AFT.pathLoad
end AFT.pathLoad
namespace AFT.pathLoad.match_1
end AFT.pathLoad.match_1
namespace AFT.roundingLoad
end AFT.roundingLoad
namespace AFT.totalCharge
end AFT.totalCharge
namespace AFT.transportBlockMatrix
end AFT.transportBlockMatrix
section
namespace AFT
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h26 {α : Type*} {count : ℕ} (f : Fin count → α) :
    (Vector.ofFn f).get=f := by
  funext index
  exact Vector.get_ofFn f index
open _root_.P2Mf6bd8d28 renaming h26 → _Pq
theorem _root_.P2Mf6bd8d28.h22 (count : ℕ) (load : Vector ℤ (count+1))
    (hload : _root_.AFT.totalCharge load.get=0) : _root_.AFT.pathLoad count (_root_.AFT.pathInverseProgram count load).value.get=load.get := by
  induction count with
  | zero =>
    funext index
    have hi : index=0 := Fin.ext (by omega)
    subst index
    simpa [_root_.AFT.totalCharge,_root_.AFT.pathLoad] using hload.symm
  | succ count ih =>
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then load.get 0 else 0)
    have ht : _root_.AFT.totalCharge tail.get=0 := by
      have hsum : load.get 0+(∑ index : Fin (count+1),load.get index.succ)=0 := by
        simpa only [_root_.AFT.totalCharge,Fin.sum_univ_succ] using hload
      simpa [tail,_root_.AFT.totalCharge,Finset.sum_add_distrib,add_comm] using hsum
    have hh := ih tail ht
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp only [_root_.AFT.pathInverseProgram,Vector.get_ofFn,_root_.AFT.pathLoad,Fin.cons_zero]
    · simp only [_root_.AFT.pathInverseProgram,_Pq,_root_.AFT.pathLoad,Fin.cons_succ,Fin.tail_cons]
      change _root_.AFT.pathLoad count (_root_.AFT.pathInverseProgram count tail).value.get rest -
        (if rest=0 then load.get 0 else 0)=load.get rest.succ
      rw [hh]
      simp [tail]
open _root_.P2Mf6bd8d28 renaming h22 → _Pm
noncomputable section
end
theorem _root_.P2Mf6bd8d28.h24 (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1))
    (hinjection : _root_.AFT.totalCharge injection.get=modulus) (hload : modulus ∣ _root_.AFT.totalCharge load.get) :
    _root_.AFT.roundingLoad count injection.get
      ((_root_.AFT.roundingInverseProgram count modulus injection load).value.1.get,
        (_root_.AFT.roundingInverseProgram count modulus injection load).value.2)=load.get := by
  let charge := _root_.AFT.totalCharge load.get/modulus
  have hcharge : charge*modulus=_root_.AFT.totalCharge load.get := Int.ediv_mul_cancel hload
  let shifted := Vector.ofFn (fun index => load.get index-charge*injection.get index)
  have hshift : _root_.AFT.totalCharge shifted.get=0 := by
    rw [_Pq]
    change _root_.AFT.totalCharge (load.get-charge • injection.get)=0
    rw [_root_.AFT.totalCharge_sub,_root_.AFT.totalCharge_smul,hinjection,hcharge,sub_self]
  have hh := _Pm count shifted hshift
  change _root_.AFT.pathLoad count (_root_.AFT.pathInverseProgram count shifted).value.get+charge • injection.get=load.get
  rw [hh]
  funext index
  simp only [shifted,Vector.get_ofFn,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring
open _root_.P2Mf6bd8d28 renaming h24 → _Po
noncomputable section
end
end AFT
open _root_.P2Mf6bd8d28 renaming h22 → _Pm
open _root_.P2Mf6bd8d28 renaming h24 → _Po
open _root_.P2Mf6bd8d28 renaming h26 → _Pq
end
open _root_.P2Mf6bd8d28 renaming h22 → _Pm
open _root_.P2Mf6bd8d28 renaming h24 → _Po
open _root_.P2Mf6bd8d28 renaming h26 → _Pq
namespace AFT.BinaryArithmetic.IntegerBits.exactQuotient
end AFT.BinaryArithmetic.IntegerBits.exactQuotient
namespace AFT.BinaryArithmetic.IntegerBits.residue
end AFT.BinaryArithmetic.IntegerBits.residue
namespace AFT.IntegerCoordinateRun
end AFT.IntegerCoordinateRun
namespace AFT.IntegerCoordinateRun.mk
end AFT.IntegerCoordinateRun.mk
namespace AFT.IntegerLoadRun
end AFT.IntegerLoadRun
namespace AFT.IntegerLoadRun.mk
end AFT.IntegerLoadRun.mk
namespace AFT.IntegerVectorRun
end AFT.IntegerVectorRun
namespace AFT.IntegerVectorRun.mk
end AFT.IntegerVectorRun.mk
namespace AFT.pathForwardProgram
end AFT.pathForwardProgram
namespace AFT.pathForwardProgram.match_1
end AFT.pathForwardProgram.match_1
namespace AFT.pathInverseProgram
end AFT.pathInverseProgram
namespace AFT.pathInverseProgram.match_1
end AFT.pathInverseProgram.match_1
namespace AFT.roundingInverseProgram
end AFT.roundingInverseProgram
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
theorem _root_.P2Mf6bd8d28.h3 {count : ℕ} (load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+2)) (first : _root_.AFT.BinaryArithmetic.IntegerBits)
    (index : Fin (count+1)) :
    ((_root_.AFT.BinaryArithmetic.binaryPathTail load first).value.get index).decode=(load.get index.succ).decode+
      if index=0 then first.decode else 0 := by
  simp only [_root_.AFT.BinaryArithmetic.binaryPathTail,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.pathTailEntry,_root_.AFT.BinaryArithmetic.readVector_value]
  by_cases hi : index=0
  · subst index;simp [_root_.AFT.BinaryArithmetic.IntegerBits.add_value]
  · have hi' : index.val ≠ 0 := fun hh => hi (Fin.ext hh)
    simp [hi,hi']
open _root_.P2Mf6bd8d28 renaming h3 → _P3
theorem _root_.P2Mf6bd8d28.h2 (count : ℕ) (load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (index : Fin count) :
    ((_root_.AFT.BinaryArithmetic.binaryPathInverse count load).value.get index).decode=
      (_root_.AFT.pathInverseProgram count (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode)).value.get index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      have ht : (_root_.AFT.BinaryArithmetic.binaryPathTail load (load.get 0)).value.map _root_.AFT.BinaryArithmetic.IntegerBits.decode=
          Vector.ofFn (fun slot : Fin (count+1) => (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get 0 else 0) := by
        apply Vector.ext
        intro slot hs
        change ((_root_.AFT.BinaryArithmetic.binaryPathTail load (load.get 0)).value.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get ⟨slot,hs⟩=
          (Vector.ofFn (fun slot : Fin (count+1) => (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get 0 else 0)).get ⟨slot,hs⟩
        simp only [Vector.get_map,Vector.get_ofFn,_P3]
      refine Fin.cases ?_ (fun rest => ?_) index
      · simp only [_root_.AFT.BinaryArithmetic.binaryPathInverse,_root_.AFT.BinaryArithmetic.storeData_get,Fin.cases_zero,_root_.AFT.BinaryArithmetic.readVector_value,
          _root_.AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_zero,Vector.get_map]
      · simp only [_root_.AFT.BinaryArithmetic.binaryPathInverse,_root_.AFT.BinaryArithmetic.storeData_get,Fin.cases_succ,_root_.AFT.BinaryArithmetic.readVector_value,
          _root_.AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_succ]
        rw [ih,ht]
open _root_.P2Mf6bd8d28 renaming h2 → _P2
end AFT.BinaryArithmetic
open _root_.P2Mf6bd8d28 renaming h2 → _P2
open _root_.P2Mf6bd8d28 renaming h3 → _P3
end
open _root_.P2Mf6bd8d28 renaming h2 → _P2
open _root_.P2Mf6bd8d28 renaming h3 → _P3
namespace AFT.BinaryArithmetic.binaryPathInverse
end AFT.BinaryArithmetic.binaryPathInverse
namespace AFT.BinaryArithmetic.binaryPathInverse.match_1
end AFT.BinaryArithmetic.binaryPathInverse.match_1
namespace AFT.BinaryArithmetic.binaryPathInverseWork
end AFT.BinaryArithmetic.binaryPathInverseWork
namespace AFT.BinaryArithmetic.binaryPathTail
end AFT.BinaryArithmetic.binaryPathTail
namespace AFT.BinaryArithmetic.pathTailEntry
end AFT.BinaryArithmetic.pathTailEntry
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
theorem _root_.P2Mf6bd8d28.h8 {size : ℕ} (charge : _root_.AFT.BinaryArithmetic.IntegerBits) (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits size)
    (index : Fin size) :
    ((_root_.AFT.BinaryArithmetic.binaryShiftedLoad charge injection load).value.get index).decode=
      (load.get index).decode-charge.decode*(injection.get index).decode := by
  simp only [_root_.AFT.BinaryArithmetic.binaryShiftedLoad,_root_.AFT.BinaryArithmetic.storeData_get,_root_.AFT.BinaryArithmetic.shiftedLoadEntry,_root_.AFT.BinaryArithmetic.IntegerBits.subtract_value,
    _root_.AFT.BinaryArithmetic.IntegerBits.multiply_value,_root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mf6bd8d28 renaming h8 → _P8
theorem _root_.P2Mf6bd8d28.h7 (count : ℕ) (modulus : List Bool)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (hq : 0 < _root_.AFT.BinaryArithmetic.value modulus)
    (hdiv : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ ∑ index,(load.get index).decode) :
    (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge.decode=
      (_root_.AFT.roundingInverseProgram count (_root_.AFT.BinaryArithmetic.value modulus) (injection.map _root_.AFT.BinaryArithmetic.IntegerBits.decode) (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode)).value.2 ∧
    ∀ index,((_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).edges.get index).decode=
      ((_root_.AFT.roundingInverseProgram count (_root_.AFT.BinaryArithmetic.value modulus) (injection.map _root_.AFT.BinaryArithmetic.IntegerBits.decode) (load.map _root_.AFT.BinaryArithmetic.IntegerBits.decode)).value.1.get index) := by
  have htotal : (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin (count+1) (_root_.AFT.BinaryArithmetic.readVector _root_.AFT.BinaryArithmetic.IntegerBits.zero load)).value.decode=
      ∑ index,(load.get index).decode := by rw [_P1];simp only [_root_.AFT.BinaryArithmetic.readVector_value]
  have hc := _P0 (_root_.AFT.BinaryArithmetic.IntegerBits.sumFin (count+1) (_root_.AFT.BinaryArithmetic.readVector _root_.AFT.BinaryArithmetic.IntegerBits.zero load)).value
    modulus hq (by rw [htotal];exact hdiv)
  rw [htotal] at hc
  refine ⟨?_,?_⟩
  · simpa only [_root_.AFT.BinaryArithmetic.binaryRoundingInverse,_root_.AFT.roundingInverseProgram,Vector.get_map] using hc
  · intro index
    simp only [_root_.AFT.BinaryArithmetic.binaryRoundingInverse,_P2,_root_.AFT.roundingInverseProgram,Vector.get_map]
    congr 3
    apply Vector.ext
    intro slot hs
    change ((_root_.AFT.BinaryArithmetic.binaryShiftedLoad _ injection load).value.map _root_.AFT.BinaryArithmetic.IntegerBits.decode).get ⟨slot,hs⟩=
      (Vector.ofFn (fun index : Fin (count+1) => (load.get index).decode-
        ((∑ point : Fin (count+1),(load.get point).decode)/(_root_.AFT.BinaryArithmetic.value modulus : ℤ))*(injection.get index).decode)).get ⟨slot,hs⟩
    simp only [Vector.get_map,Vector.get_ofFn,_P8,hc]
open _root_.P2Mf6bd8d28 renaming h7 → _P7
end AFT.BinaryArithmetic
open _root_.P2Mf6bd8d28 renaming h7 → _P7
open _root_.P2Mf6bd8d28 renaming h8 → _P8
end
open _root_.P2Mf6bd8d28 renaming h7 → _P7
open _root_.P2Mf6bd8d28 renaming h8 → _P8
namespace AFT.BinaryArithmetic.BinaryCoordinateResult
end AFT.BinaryArithmetic.BinaryCoordinateResult
namespace AFT.BinaryArithmetic.BinaryCoordinateResult.mk
end AFT.BinaryArithmetic.BinaryCoordinateResult.mk
namespace AFT.BinaryArithmetic.binaryRoundingInverse
end AFT.BinaryArithmetic.binaryRoundingInverse
namespace AFT.BinaryArithmetic.binaryShiftedLoad
end AFT.BinaryArithmetic.binaryShiftedLoad
namespace AFT.BinaryArithmetic.shiftedLoadEntry
end AFT.BinaryArithmetic.shiftedLoadEntry
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
theorem _root_.P2Mf6bd8d28.h10 {size : ℕ} (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.IntegerBits size) size)
     (column row : Fin size) : (_root_.AFT.BinaryArithmetic.readIntegerMatrix matrix column row).value=(matrix.get column).get row := by
   simp only [_root_.AFT.BinaryArithmetic.readIntegerMatrix,_root_.AFT.BinaryArithmetic.readList_value]
   rw [List.getElem?_eq_getElem (by simp only [Vector.length_toList];exact column.isLt)]
   simp only [Vector.getElem_toList,_root_.AFT.BinaryArithmetic.readVector_value]
   rfl
open _root_.P2Mf6bd8d28 renaming h10 → _Pa
theorem _root_.P2Mf6bd8d28.h4 (count : ℕ) (matrix : Vector (Vector _root_.AFT.BinaryArithmetic.IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column vertex : Fin (count+1)) :
     (_root_.AFT.BinaryArithmetic.binaryPermutedColumn count matrix permutation column).value.get vertex=
       (matrix.get column).get (permutation.get vertex) := by
   simp only [_root_.AFT.BinaryArithmetic.binaryPermutedColumn,_root_.AFT.BinaryArithmetic.storeData_get,_Pa,_root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mf6bd8d28 renaming h4 → _P4
end AFT.BinaryArithmetic
open _root_.P2Mf6bd8d28 renaming h4 → _P4
open _root_.P2Mf6bd8d28 renaming h10 → _Pa
end
open _root_.P2Mf6bd8d28 renaming h4 → _P4
open _root_.P2Mf6bd8d28 renaming h10 → _Pa
namespace AFT.BinaryArithmetic.CounterDivisionResult
end AFT.BinaryArithmetic.CounterDivisionResult
namespace AFT.BinaryArithmetic.CounterDivisionResult.mk
end AFT.BinaryArithmetic.CounterDivisionResult.mk
namespace AFT.BinaryArithmetic.binaryPoolScan
end AFT.BinaryArithmetic.binaryPoolScan
namespace AFT.BinaryArithmetic.binaryPoolScan.match_1
end AFT.BinaryArithmetic.binaryPoolScan.match_1
namespace AFT.BinaryArithmetic.binaryRunPoolScan
end AFT.BinaryArithmetic.binaryRunPoolScan
namespace AFT.BinaryArithmetic.differenceCounter
end AFT.BinaryArithmetic.differenceCounter
namespace AFT.BinaryArithmetic.differenceCounter.match_1
end AFT.BinaryArithmetic.differenceCounter.match_1
namespace AFT.BinaryArithmetic.divideCounter
end AFT.BinaryArithmetic.divideCounter
namespace AFT.blockVertexSplit
end AFT.blockVertexSplit
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
theorem _root_.P2Mf6bd8d28.h9 (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     (_root_.AFT.BinaryArithmetic.binaryVertexCode legs rest index).value=(_root_.AFT.blockVertexNumbering legs rest).symm index := by
   apply (_root_.AFT.blockVertexNumbering legs rest).injective
   rw [Equiv.apply_symm_apply]
   unfold _root_.AFT.BinaryArithmetic.binaryVertexCode
   try dsimp only
   split
   · rename_i h
     apply Fin.ext
     change (_root_.AFT.BinaryArithmetic.divideCounter index.val 3).remainder+3*(_root_.AFT.BinaryArithmetic.divideCounter index.val 3).quotient=index.val
     rw [(_root_.AFT.BinaryArithmetic.divideCounter_value index.val 3 (by omega)).1,(_root_.AFT.BinaryArithmetic.divideCounter_value index.val 3 (by omega)).2]
     exact Nat.mod_add_div _ _
   · rename_i h
     apply Fin.ext
     change legs*3+(0+1*(_root_.AFT.BinaryArithmetic.differenceCounter index.val (_root_.AFT.BinaryArithmetic.multiplyCounter legs 3).count).count)=index.val
     simp only [Nat.zero_add,Nat.one_mul]
     rw [_root_.AFT.BinaryArithmetic.differenceCounter_value,_root_.AFT.BinaryArithmetic.multiplyCounter_value]
     have hi : legs*3 ≤ index.val := by
       have hh : ¬ index.val<(_root_.AFT.BinaryArithmetic.multiplyCounter legs 3).count := fun hi => h ((_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr hi)
       rw [_root_.AFT.BinaryArithmetic.multiplyCounter_value] at hh
       omega
     omega
open _root_.P2Mf6bd8d28 renaming h9 → _P9
theorem _root_.P2Mf6bd8d28.h6 (legs rest : ℕ) (index : Fin legs⊕Fin rest) :
     (_root_.AFT.BinaryArithmetic.binaryRootAddress legs rest index).value=_root_.AFT.blockNumbering legs rest index := by
   cases index <;> apply Fin.ext <;> simp [_root_.AFT.BinaryArithmetic.binaryRootAddress,_root_.AFT.blockNumbering,_root_.AFT.BinaryArithmetic.addCounter_value]
open _root_.P2Mf6bd8d28 renaming h6 → _P6
end AFT.BinaryArithmetic
open _root_.P2Mf6bd8d28 renaming h6 → _P6
open _root_.P2Mf6bd8d28 renaming h9 → _P9
end
open _root_.P2Mf6bd8d28 renaming h6 → _P6
open _root_.P2Mf6bd8d28 renaming h9 → _P9
namespace AFT.BinaryArithmetic.binaryEdgeAddress
end AFT.BinaryArithmetic.binaryEdgeAddress
namespace AFT.BinaryArithmetic.binaryEdgeAddress.match_1
end AFT.BinaryArithmetic.binaryEdgeAddress.match_1
namespace AFT.BinaryArithmetic.binaryRootAddress
end AFT.BinaryArithmetic.binaryRootAddress
namespace AFT.BinaryArithmetic.binaryRootAddress.match_1
end AFT.BinaryArithmetic.binaryRootAddress.match_1
namespace AFT.V7Calibration.actualBodyRootBasis
end AFT.V7Calibration.actualBodyRootBasis
namespace AFT.V7Calibration.actualRootIndex
end AFT.V7Calibration.actualRootIndex
namespace AFT.V7Calibration.blockIndexNumbering
end AFT.V7Calibration.blockIndexNumbering
namespace AFT.V7Calibration.coordinateZeroSumCongr
end AFT.V7Calibration.coordinateZeroSumCongr
namespace AFT.V7Calibration.physicalEdgeIndexEquiv
end AFT.V7Calibration.physicalEdgeIndexEquiv
namespace AFT.blockEdgeNumbering
end AFT.blockEdgeNumbering
namespace AFT.blockNumbering
end AFT.blockNumbering
namespace AFT.physicalEdgeLoadProgram
end AFT.physicalEdgeLoadProgram
namespace AFT.physicalEdgeLoadProgram.match_1
end AFT.physicalEdgeLoadProgram.match_1
namespace AFT.physicalEdgeNumberingProgram
end AFT.physicalEdgeNumberingProgram
namespace AFT.physicalInitialLoadProgram
end AFT.physicalInitialLoadProgram
namespace AFT.physicalQueueLoadProgram
end AFT.physicalQueueLoadProgram
namespace AFT.physicalVertexNumberingProgram
end AFT.physicalVertexNumberingProgram
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
theorem _root_.P2Mf6bd8d28.h5 (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (vertex : Fin (count+1)) :
     (_root_.AFT.BinaryArithmetic.binaryPhysicalVertex legs rest count hvertex vertex).value=
       (_root_.AFT.physicalVertexNumberingProgram legs rest count hvertex).symm vertex :=
   _P9 legs rest _
open _root_.P2Mf6bd8d28 renaming h5 → _P5
end AFT.BinaryArithmetic
open _root_.P2Mf6bd8d28 renaming h5 → _P5
end
open _root_.P2Mf6bd8d28 renaming h5 → _P5
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
namespace AFT.BinaryArithmetic.RationalBits.add
end AFT.BinaryArithmetic.RationalBits.add
namespace AFT.BinaryArithmetic.RationalBits.copy
end AFT.BinaryArithmetic.RationalBits.copy
namespace AFT.BinaryArithmetic.RationalBits.inverse
end AFT.BinaryArithmetic.RationalBits.inverse
namespace AFT.BinaryArithmetic.RationalBits.multiply
end AFT.BinaryArithmetic.RationalBits.multiply
namespace AFT.BinaryArithmetic.RationalBits.negate
end AFT.BinaryArithmetic.RationalBits.negate
namespace AFT.BinaryArithmetic.RationalBits.primitiveWorkBound
end AFT.BinaryArithmetic.RationalBits.primitiveWorkBound
namespace AFT.BinaryArithmetic.copy
end AFT.BinaryArithmetic.copy
namespace AFT.BinaryArithmetic.copy.match_1
end AFT.BinaryArithmetic.copy.match_1
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.RationalOperations
end AFT.RationalNumerics.RationalOperations
namespace AFT.RationalNumerics.RationalOperations.Correct
end AFT.RationalNumerics.RationalOperations.Correct
namespace AFT.RationalNumerics.RationalOperations.mk
end AFT.RationalNumerics.RationalOperations.mk
namespace AFT.RationalNumerics.StoredScalarProgram
end AFT.RationalNumerics.StoredScalarProgram
namespace AFT.RationalNumerics.StoredScalarProgram.add
end AFT.RationalNumerics.StoredScalarProgram.add
namespace AFT.RationalNumerics.StoredScalarProgram.atom
end AFT.RationalNumerics.StoredScalarProgram.atom
namespace AFT.RationalNumerics.StoredScalarProgram.brecOn
end AFT.RationalNumerics.StoredScalarProgram.brecOn
namespace AFT.RationalNumerics.StoredScalarProgram.compile
end AFT.RationalNumerics.StoredScalarProgram.compile
namespace AFT.RationalNumerics.StoredScalarProgram.compile.match_1
end AFT.RationalNumerics.StoredScalarProgram.compile.match_1
namespace AFT.RationalNumerics.StoredScalarProgram.inverse
end AFT.RationalNumerics.StoredScalarProgram.inverse
namespace AFT.RationalNumerics.StoredScalarProgram.literal
end AFT.RationalNumerics.StoredScalarProgram.literal
namespace AFT.RationalNumerics.StoredScalarProgram.meaning
end AFT.RationalNumerics.StoredScalarProgram.meaning
namespace AFT.RationalNumerics.StoredScalarProgram.multiply
end AFT.RationalNumerics.StoredScalarProgram.multiply
namespace AFT.RationalNumerics.StoredScalarProgram.negate
end AFT.RationalNumerics.StoredScalarProgram.negate
namespace AFT.RationalNumerics.StoredScalarProgram.run
end AFT.RationalNumerics.StoredScalarProgram.run
namespace AFT.RationalNumerics.StoredScalarProgram.run.match_1
end AFT.RationalNumerics.StoredScalarProgram.run.match_1
section
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic
namespace StoredScalarProgram
variable {Scalar : Type*}
end StoredScalarProgram
theorem _root_.P2Mf6bd8d28.h21 {Scalar : Type*} (program : _root_.AFT.RationalNumerics.ScalarProgram Scalar) :
    ∃ stored : _root_.AFT.RationalNumerics.StoredScalarProgram Scalar _root_.AFT.BinaryArithmetic.RationalBits,stored.meaning _root_.AFT.BinaryArithmetic.RationalBits.decode=program := by
  induction program with
  | rational q =>
    obtain ⟨code,hcode⟩ := _root_.InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic.RationalBits.exists_code q
    exact ⟨.literal code,congrArg ScalarProgram.rational hcode⟩
  | atom code => exact ⟨.atom code,rfl⟩
  | add first second hf hs =>
    obtain ⟨f,hf⟩ := hf
    obtain ⟨s,hs⟩ := hs
    exact ⟨.add f s,by simp only [_root_.AFT.RationalNumerics.StoredScalarProgram.meaning,hf,hs]⟩
  | multiply first second hf hs =>
    obtain ⟨f,hf⟩ := hf
    obtain ⟨s,hs⟩ := hs
    exact ⟨.multiply f s,by simp only [_root_.AFT.RationalNumerics.StoredScalarProgram.meaning,hf,hs]⟩
  | negate term ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨.negate t,by simp only [_root_.AFT.RationalNumerics.StoredScalarProgram.meaning,ht]⟩
  | inverse term ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨.inverse t,by simp only [_root_.AFT.RationalNumerics.StoredScalarProgram.meaning,ht]⟩
open _root_.P2Mf6bd8d28 renaming h21 → _Pl
end AFT.RationalNumerics
open _root_.P2Mf6bd8d28 renaming h21 → _Pl
end
open _root_.P2Mf6bd8d28 renaming h21 → _Pl
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualBlockFock
end CurrentAFT.ActualBlockFock
namespace CurrentAFT.ActualBlockFock.Slots
end CurrentAFT.ActualBlockFock.Slots
namespace CurrentAFT.ActualBlockFock.Slots.match_1
end CurrentAFT.ActualBlockFock.Slots.match_1
namespace CurrentAFT.ActualBlockFock.blockLawAt
end CurrentAFT.ActualBlockFock.blockLawAt
namespace CurrentAFT.ActualBlockFock.productFockEnergy
end CurrentAFT.ActualBlockFock.productFockEnergy
namespace CurrentAFT.ActualBlockFock.singletonLaw
end CurrentAFT.ActualBlockFock.singletonLaw
section
namespace CurrentAFT.CurrentPhysicalNumbering
open AFT ActualBlockFock
set_option maxHeartbeats 700000
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension
theorem _root_.P2Mf6bd8d28.h104 (security : ℕ) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) (slot : Fin 3) :
    (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inl leg, slot⟩).val = slot.val + 3 * leg.val := by
  rfl
open _root_.P2Mf6bd8d28 renaming h104 → _P2w
theorem _root_.P2Mf6bd8d28.h103 (security : ℕ) (center : Fin (_root_.CurrentAFT.ActualBlockFock.centerCount security)) :
    (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inr (.inl center), (0 : Fin 1)⟩).val = _root_.CurrentAFT.Parameters.legCount security * 3 + center.val := by
  rfl
open _root_.P2Mf6bd8d28 renaming h103 → _P2v
theorem _root_.P2Mf6bd8d28.h105 (security : ℕ) (queue : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inr (.inr queue), (0 : Fin 1)⟩).val =
      _root_.CurrentAFT.Parameters.legCount security * 3 + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) := by
  rfl
open _root_.P2Mf6bd8d28 renaming h105 → _P2x
end CurrentAFT.CurrentPhysicalNumbering
open _root_.P2Mf6bd8d28 renaming h103 → _P2v
open _root_.P2Mf6bd8d28 renaming h104 → _P2w
open _root_.P2Mf6bd8d28 renaming h105 → _P2x
end
open _root_.P2Mf6bd8d28 renaming h103 → _P2v
open _root_.P2Mf6bd8d28 renaming h104 → _P2w
open _root_.P2Mf6bd8d28 renaming h105 → _P2x
namespace CurrentAFT.CurrentFlagChartDraw
end CurrentAFT.CurrentFlagChartDraw
namespace CurrentAFT.CurrentFlagChartDraw.draw
end CurrentAFT.CurrentFlagChartDraw.draw
namespace CurrentAFT.PublicParameterProgram
end CurrentAFT.PublicParameterProgram
namespace CurrentAFT.PublicParameterProgram.checkedPower
end CurrentAFT.PublicParameterProgram.checkedPower
namespace CurrentAFT.PublicParameterProgram.checkedProduct
end CurrentAFT.PublicParameterProgram.checkedProduct
namespace CurrentAFT.PublicParameterProgram.checkedScan
end CurrentAFT.PublicParameterProgram.checkedScan
namespace CurrentAFT.PublicParameterProgram.primeTest
end CurrentAFT.PublicParameterProgram.primeTest
namespace CurrentAFT.PublicParameterProgram.testWork
end CurrentAFT.PublicParameterProgram.testWork
namespace CurrentAFT.PublicParameterProgram.workBound
end CurrentAFT.PublicParameterProgram.workBound
namespace CurrentAFT.PublicParameterProgram.workPolynomial
end CurrentAFT.PublicParameterProgram.workPolynomial
section
namespace CurrentAFT.CurrentPublicShiftProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000
theorem _root_.P2Mf6bd8d28.h107 (modulus primary : ℕ) (coin : Bool) :
    (_root_.CurrentAFT.CurrentPublicShiftProgram.direction modulus primary coin).value =
      if 2 * primary < modulus - 1 then false else if modulus - 1 < 2 * primary then true else coin := by
  simp only [_root_.CurrentAFT.CurrentPublicShiftProgram.direction, _root_.AFT.BinaryArithmetic.doubleCounter_value, _root_.AFT.BinaryArithmetic.differenceCounter_value, _root_.AFT.BinaryArithmetic.lessCounter_value]
open _root_.P2Mf6bd8d28 renaming h107 → _P2z
theorem _root_.P2Mf6bd8d28.h108 (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) :
    (_root_.CurrentAFT.CurrentPublicShiftProgram.program modulus width primary index coin blurFirst blurSecond).value.decode =
      (if (_root_.CurrentAFT.CurrentPublicShiftProgram.direction modulus primary coin).value then ((width + index : ℕ) : ℤ) else -((width + index : ℕ) : ℤ)) +
        blurFirst - blurSecond := by
  simp only [_root_.CurrentAFT.CurrentPublicShiftProgram.program]
  rw [_root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value]
  simp only [_root_.AFT.BinaryArithmetic.IntegerBits.decode, _root_.AFT.BinaryArithmetic.signedValue, _root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  cases (_root_.CurrentAFT.CurrentPublicShiftProgram.direction modulus primary coin).value <;> simp <;> ring
open _root_.P2Mf6bd8d28 renaming h108 → _P30
theorem _root_.P2Mf6bd8d28.h106 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) :
    (_root_.CurrentAFT.CurrentPublicShiftProgram.current security primary seed).value.decode = _root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed := by
  simp only [_root_.CurrentAFT.CurrentPublicShiftProgram.current, _P30, _root_.CurrentAFT.PublicParameterProgram.modulus_value, _root_.AFT.BinaryArithmetic.addCounter_value,
    _root_.AFT.BinaryArithmetic.powerCounter_value, _P2z, _root_.CurrentAFT.ActualPublicLegCharge.publicShift, _root_.CurrentAFT.ActualPublicLegCharge.signedOffset,
    _root_.CurrentAFT.InwardAnchor.positiveDirection, _root_.CurrentAFT.InwardAnchor.offset, _root_.CurrentAFT.Parameters.anchorWidth, _root_.CurrentAFT.Parameters.scale, _root_.CurrentAFT.Parameters.base,
    ← pow_mul, Nat.cast_add]
open _root_.P2Mf6bd8d28 renaming h106 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2Mf6bd8d28 renaming h106 → _P2y
end CurrentAFT.CurrentPublicShiftProgram
open _root_.P2Mf6bd8d28 renaming h106 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2Mf6bd8d28 renaming h106 → _P2y
open _root_.P2Mf6bd8d28 renaming h107 → _P2z
open _root_.P2Mf6bd8d28 renaming h108 → _P30
end
open _root_.P2Mf6bd8d28 renaming h106 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2Mf6bd8d28 renaming h106 → _P2y
open _root_.P2Mf6bd8d28 renaming h107 → _P2z
open _root_.P2Mf6bd8d28 renaming h108 → _P30
namespace CurrentAFT.BinaryFixedScalarProgram
end CurrentAFT.BinaryFixedScalarProgram
namespace CurrentAFT.BinaryFixedScalarProgram.height
end CurrentAFT.BinaryFixedScalarProgram.height
namespace CurrentAFT.BinaryFixedScalarProgram.heightPolynomial
end CurrentAFT.BinaryFixedScalarProgram.heightPolynomial
namespace CurrentAFT.BinaryFixedScalarProgram.literalBound
end CurrentAFT.BinaryFixedScalarProgram.literalBound
namespace CurrentAFT.BinaryFixedScalarProgram.work
end CurrentAFT.BinaryFixedScalarProgram.work
namespace CurrentAFT.BinaryFixedScalarProgram.workPolynomial
end CurrentAFT.BinaryFixedScalarProgram.workPolynomial
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram
namespace CurrentAFT.RationalFamilyProductProgram.average
end CurrentAFT.RationalFamilyProductProgram.average
namespace CurrentAFT.RationalFamilyProductProgram.homogeneous
end CurrentAFT.RationalFamilyProductProgram.homogeneous
namespace CurrentAFT.RationalFamilyProductProgram.product
end CurrentAFT.RationalFamilyProductProgram.product
namespace CurrentAFT.RationalFamilyProductProgram.realTable
end CurrentAFT.RationalFamilyProductProgram.realTable
namespace CurrentAFT.RationalFamilyProductProgram.tensor
end CurrentAFT.RationalFamilyProductProgram.tensor
section
namespace CurrentAFT.FamilyProductSyntax
open AFT RationalNumerics GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h110 (order : ℕ) (output : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) :
    ∃ stored : _root_.AFT.RationalNumerics.StoredScalarProgram (_root_.CurrentAFT.FamilyProductSyntax.Leaf order output) _root_.AFT.BinaryArithmetic.RationalBits,
      stored.meaning _root_.AFT.BinaryArithmetic.RationalBits.decode = _root_.CurrentAFT.FamilyProductSyntax.product order output :=
  _Pl (_root_.CurrentAFT.FamilyProductSyntax.product order output)
open _root_.P2Mf6bd8d28 renaming h110 → _P32
end
open _root_.P2Mf6bd8d28 renaming h110 → _P32
end CurrentAFT.FamilyProductSyntax
open _root_.P2Mf6bd8d28 renaming h110 → _P32
end
open _root_.P2Mf6bd8d28 renaming h110 → _P32
namespace AFT.BinaryArithmetic.countFin
end AFT.BinaryArithmetic.countFin
namespace AFT.BinaryArithmetic.countFin.match_1
end AFT.BinaryArithmetic.countFin.match_1
namespace AFT.BinaryArithmetic.equalCounter
end AFT.BinaryArithmetic.equalCounter
namespace AFT.BinaryArithmetic.equalCounter.match_1
end AFT.BinaryArithmetic.equalCounter.match_1
namespace AFT.BinaryArithmetic.maskCount
end AFT.BinaryArithmetic.maskCount
namespace AFT.BinaryArithmetic.maskSet
end AFT.BinaryArithmetic.maskSet
namespace CurrentAFT.BinaryFamilyProduct
end CurrentAFT.BinaryFamilyProduct
namespace CurrentAFT.BinaryFamilyProduct.gather
end CurrentAFT.BinaryFamilyProduct.gather
namespace CurrentAFT.BinaryFamilyProduct.gatherEntry
end CurrentAFT.BinaryFamilyProduct.gatherEntry
section
namespace CurrentAFT.FixedFamilyPrograms
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h111 (order : ℕ) : ∃ list : List (_root_.CurrentAFT.FixedFamilyPrograms.Entry order), _root_.CurrentAFT.FixedFamilyPrograms.Correct order list ∧ _root_.CurrentAFT.FixedFamilyPrograms.Complete order list := by
  let programs := fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => Classical.choose (_P32 order arity)
  let list : List (_root_.CurrentAFT.FixedFamilyPrograms.Entry order) := (Finset.univ : Finset (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)).toList.map
    (fun arity => ⟨arity, programs arity⟩)
  refine ⟨list, ?_, ?_⟩
  · intro entry hentry
    obtain ⟨arity, _, he⟩ := List.mem_map.mp hentry
    subst entry
    exact Classical.choose_spec (_P32 order arity)
  · intro arity
    refine ⟨programs arity, List.mem_map.mpr ?_⟩
    exact ⟨arity, Finset.mem_toList.mpr (Finset.mem_univ arity), rfl⟩
open _root_.P2Mf6bd8d28 renaming h111 → _P33
end
open _root_.P2Mf6bd8d28 renaming h111 → _P33
end CurrentAFT.FixedFamilyPrograms
open _root_.P2Mf6bd8d28 renaming h111 → _P33
end
open _root_.P2Mf6bd8d28 renaming h111 → _P33
namespace CurrentAFT.BinaryDensityInverseTensor
end CurrentAFT.BinaryDensityInverseTensor
namespace CurrentAFT.BinaryDensityInverseTensor.colors
end CurrentAFT.BinaryDensityInverseTensor.colors
namespace CurrentAFT.BinaryDensityInverseTensor.column
end CurrentAFT.BinaryDensityInverseTensor.column
namespace CurrentAFT.BinaryDensityInverseTensor.columnWorkPolynomial
end CurrentAFT.BinaryDensityInverseTensor.columnWorkPolynomial
namespace CurrentAFT.BinaryDensityInverseTensor.heightPolynomial
end CurrentAFT.BinaryDensityInverseTensor.heightPolynomial
namespace CurrentAFT.BinaryDensityInverseTensor.term
end CurrentAFT.BinaryDensityInverseTensor.term
namespace CurrentAFT.BinaryDensityInverseTensor.termHeightPolynomial
end CurrentAFT.BinaryDensityInverseTensor.termHeightPolynomial
namespace CurrentAFT.BinaryDensityInverseTensor.termWorkPolynomial
end CurrentAFT.BinaryDensityInverseTensor.termWorkPolynomial
namespace CurrentAFT.BinaryDensityInverseTensor.workPolynomial
end CurrentAFT.BinaryDensityInverseTensor.workPolynomial
namespace CurrentAFT.FamilyProductSyntax
end CurrentAFT.FamilyProductSyntax
namespace CurrentAFT.FamilyProductSyntax.Leaf
end CurrentAFT.FamilyProductSyntax.Leaf
namespace CurrentAFT.FamilyProductSyntax.Leaf.mk
end CurrentAFT.FamilyProductSyntax.Leaf.mk
namespace CurrentAFT.FamilyProductSyntax.homogeneous
end CurrentAFT.FamilyProductSyntax.homogeneous
namespace CurrentAFT.FamilyProductSyntax.product
end CurrentAFT.FamilyProductSyntax.product
namespace CurrentAFT.FamilyProductSyntax.splitLeaf
end CurrentAFT.FamilyProductSyntax.splitLeaf
namespace CurrentAFT.FamilyProductSyntax.sum
end CurrentAFT.FamilyProductSyntax.sum
namespace CurrentAFT.FamilyProductSyntax.sumList
end CurrentAFT.FamilyProductSyntax.sumList
namespace CurrentAFT.FamilyProductSyntax.sumList.match_1
end CurrentAFT.FamilyProductSyntax.sumList.match_1
namespace CurrentAFT.FamilyProductSyntax.value
end CurrentAFT.FamilyProductSyntax.value
section
namespace CurrentAFT.BinaryStoredSymmetrization
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h51 (degree : ℕ) : ∃ program : _root_.CurrentAFT.BinaryStoredSymmetrization.Program degree,
    program.meaning _root_.AFT.BinaryArithmetic.RationalBits.decode = _root_.CurrentAFT.BinaryStoredSymmetrization.meanSyntax degree := _Pl (_root_.CurrentAFT.BinaryStoredSymmetrization.meanSyntax degree)
open _root_.P2Mf6bd8d28 renaming h51 → _P1f
end
open _root_.P2Mf6bd8d28 renaming h51 → _P1f
end CurrentAFT.BinaryStoredSymmetrization
open _root_.P2Mf6bd8d28 renaming h51 → _P1f
end
open _root_.P2Mf6bd8d28 renaming h51 → _P1f
namespace CurrentAFT.BinaryCoefficientExtraction
end CurrentAFT.BinaryCoefficientExtraction
namespace CurrentAFT.BinaryFiniteCoefficient
end CurrentAFT.BinaryFiniteCoefficient
namespace CurrentAFT.BinaryFiniteCoefficient.lift
end CurrentAFT.BinaryFiniteCoefficient.lift
namespace CurrentAFT.BinaryFiniteCoefficient.workPolynomial
end CurrentAFT.BinaryFiniteCoefficient.workPolynomial
namespace CurrentAFT.RationalLocalFamilyProgram
end CurrentAFT.RationalLocalFamilyProgram
section
namespace CurrentAFT.BinaryPrimarySelectedCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h46 (selected : Finset (Fin 4)) : ∃ entry : _root_.CurrentAFT.BinaryPrimarySelectedCoefficient.Entry, entry.selected=selected ∧ _root_.CurrentAFT.BinaryPrimarySelectedCoefficient.Valid entry := by
  obtain ⟨program,hprogram⟩ := _P1f selected.card
  refine ⟨⟨selected,Vector.ofFn (fun index => ((Finset.orderIsoOfFin selected rfl) index).val),program⟩,rfl,?_,hprogram⟩
  intro index
  exact Vector.get_ofFn _ _
open _root_.P2Mf6bd8d28 renaming h46 → _P1a
theorem _root_.P2Mf6bd8d28.h45 : ∃ entries : Vector _root_.CurrentAFT.BinaryPrimarySelectedCoefficient.Entry 16, ∃ ordering : Fin 16 ≃ Finset (Fin 4),
    (∀ index, (entries.get index).selected=ordering index) ∧ ∀ index, _root_.CurrentAFT.BinaryPrimarySelectedCoefficient.Valid (entries.get index) := by
  have hcard : Fintype.card (Finset (Fin 4))=16 := by simp
  let ordering : Fin 16 ≃ Finset (Fin 4) := (Fintype.equivFinOfCardEq hcard).symm
  choose entry hselected hvalid using _P1a
  refine ⟨Vector.ofFn (fun index => entry (ordering index)),ordering,?_,?_⟩
  · intro index
    rw [Vector.get_ofFn]
    exact hselected _
  · intro index
    rw [Vector.get_ofFn]
    exact hvalid _
open _root_.P2Mf6bd8d28 renaming h45 → _P19
end
open _root_.P2Mf6bd8d28 renaming h45 → _P19
open _root_.P2Mf6bd8d28 renaming h46 → _P1a
end CurrentAFT.BinaryPrimarySelectedCoefficient
open _root_.P2Mf6bd8d28 renaming h45 → _P19
open _root_.P2Mf6bd8d28 renaming h46 → _P1a
end
open _root_.P2Mf6bd8d28 renaming h45 → _P19
open _root_.P2Mf6bd8d28 renaming h46 → _P1a
namespace CurrentAFT.LobsterIncidence
end CurrentAFT.LobsterIncidence
namespace CurrentAFT.LobsterIncidence.bodyResidual
end CurrentAFT.LobsterIncidence.bodyResidual
namespace CurrentAFT.LobsterIncidence.firstEdge
end CurrentAFT.LobsterIncidence.firstEdge
namespace CurrentAFT.LobsterIncidence.load
end CurrentAFT.LobsterIncidence.load
namespace CurrentAFT.LobsterIncidence.load.match_1
end CurrentAFT.LobsterIncidence.load.match_1
namespace CurrentAFT.LobsterIncidence.secondEdge
end CurrentAFT.LobsterIncidence.secondEdge
namespace CurrentAFT.Parameters
end CurrentAFT.Parameters
namespace CurrentAFT.Parameters.base
end CurrentAFT.Parameters.base
namespace CurrentAFT.Parameters.bodySize
end CurrentAFT.Parameters.bodySize
namespace CurrentAFT.Parameters.calibrationOrder
end CurrentAFT.Parameters.calibrationOrder
namespace CurrentAFT.Parameters.dimension
end CurrentAFT.Parameters.dimension
namespace CurrentAFT.Parameters.leastPrimeWitness
end CurrentAFT.Parameters.leastPrimeWitness
namespace CurrentAFT.Parameters.legCount
end CurrentAFT.Parameters.legCount
namespace CurrentAFT.Parameters.primeThreshold
end CurrentAFT.Parameters.primeThreshold
namespace CurrentAFT.Parameters.scale
end CurrentAFT.Parameters.scale
namespace CurrentAFT.PublicCharge
end CurrentAFT.PublicCharge
namespace CurrentAFT.PublicCharge.attachmentIncrement
end CurrentAFT.PublicCharge.attachmentIncrement
section
namespace CurrentAFT.LobsterCoordinates
open AFT PublicCharge LobsterIncidence
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
theorem _root_.P2Mf6bd8d28.h116 (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) (index : Fin (bodyEdges + (legs + legs) + 1)) :
    (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling input).val index =
      _root_.CurrentAFT.LobsterIncidence.load placement attachment (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input)
        ((_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).symm (relabeling.symm index)) := rfl
open _root_.P2Mf6bd8d28 renaming h116 → _P38
end
open _root_.P2Mf6bd8d28 renaming h116 → _P38
end CurrentAFT.LobsterCoordinates
open _root_.P2Mf6bd8d28 renaming h116 → _P38
end
open _root_.P2Mf6bd8d28 renaming h116 → _P38
namespace CurrentAFT.LegMixer
end CurrentAFT.LegMixer
namespace CurrentAFT.LegMixer.blockCoordinateMixer
end CurrentAFT.LegMixer.blockCoordinateMixer
namespace CurrentAFT.LegMixer.coordinateMixer
end CurrentAFT.LegMixer.coordinateMixer
namespace CurrentAFT.LegMixer.inverseMixer
end CurrentAFT.LegMixer.inverseMixer
namespace CurrentAFT.LegMixer.legIncidence
end CurrentAFT.LegMixer.legIncidence
namespace CurrentAFT.LobsterCoordinates
end CurrentAFT.LobsterCoordinates
section
namespace CurrentAFT.LobsterMixerMatrix
open AFT LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Scalar : Type*} [CommRing Scalar]
theorem _root_.P2Mf6bd8d28.h118 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : Fin (bodyEdges + (legs + legs)) → Scalar)
    (index : Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) :
    (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs index) =
      (_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix bodyEdges legs scale shear).mulVec (input ∘ _root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs) index := by
  simp only [_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs)]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]
open _root_.P2Mf6bd8d28 renaming h118 → _P3a
theorem _root_.P2Mf6bd8d28.h117 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) → Scalar) :
    (_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix bodyEdges legs scale shear).mulVec input =
      Sum.elim (fun vertex => input (.inl vertex))
        (Sum.elim (fun leg => scale leg * input (.inr (.inl leg)) + shear leg * input (.inr (.inr leg)))
          (fun leg => input (.inr (.inr leg)))) := by
  ext index
  rcases index with vertex | (leg | leg) <;>
    simp [_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.diagonal_apply]
open _root_.P2Mf6bd8d28 renaming h117 → _P39
end
open _root_.P2Mf6bd8d28 renaming h117 → _P39
open _root_.P2Mf6bd8d28 renaming h118 → _P3a
end CurrentAFT.LobsterMixerMatrix
open _root_.P2Mf6bd8d28 renaming h117 → _P39
open _root_.P2Mf6bd8d28 renaming h118 → _P3a
end
open _root_.P2Mf6bd8d28 renaming h117 → _P39
open _root_.P2Mf6bd8d28 renaming h118 → _P3a
namespace CurrentAFT.AffineBaseline
end CurrentAFT.AffineBaseline
namespace CurrentAFT.AffineBaseline.baseline
end CurrentAFT.AffineBaseline.baseline
namespace CurrentAFT.AffineBaseline.baseline.match_1
end CurrentAFT.AffineBaseline.baseline.match_1
namespace CurrentAFT.AffineBaseline.closure
end CurrentAFT.AffineBaseline.closure
namespace CurrentAFT.AffineBaseline.offset
end CurrentAFT.AffineBaseline.offset
section
namespace CurrentAFT.AffineRealization
open AFT LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
theorem _root_.P2Mf6bd8d28.h32 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    _root_.AFT.pathLoad _ (_root_.CurrentAFT.AffineRealization.extensionCorrection bodyEdges legs modulus queues relabeling) =
      _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling - _root_.AFT.injectionColumn _ modulus :=
  (Classical.choose_spec (_root_.AFT.exists_extension_correction _
    (_root_.AFT.injectionColumn _ modulus) (_root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling)
    ((_root_.CurrentAFT.AffineRealization.queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (_root_.AFT.totalCharge_injectionColumn _ modulus (_root_.CurrentAFT.AffineRealization.queue_modulus_le bodyEdges legs modulus queues)).symm))).1
open _root_.P2Mf6bd8d28 renaming h32 → _Pw
theorem _root_.P2Mf6bd8d28.h33 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input) =
      (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling
        ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
          input.2 • _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling :=
  _Pp _ _ _ _ _ _
    (_Pw bodyEdges legs modulus queues relabeling) input
open _root_.P2Mf6bd8d28 renaming h33 → _Px
theorem _root_.P2Mf6bd8d28.h31 (count : ℕ) (basis : (Fin count → ℤ) ≃ₗ[ℤ] _root_.AFT.zeroSumLattice count)
    (input : Fin count → ℤ) :
    (_root_.AFT.edgeBasisChangeMatrix count basis).mulVec input = _root_.AFT.edgeBasisChange count basis input := by
  have hrepr (v : Fin count → ℤ) : ⇑((Pi.basisFun ℤ (Fin count)).repr v) = v := by
    funext i
    exact Pi.basisFun_repr ℤ (Fin count) v i
  simpa only [_root_.AFT.edgeBasisChangeMatrix, hrepr, LinearEquiv.coe_coe] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℤ (Fin count)) (Pi.basisFun ℤ (Fin count))
      (_root_.AFT.edgeBasisChange count basis).toLinearMap input
open _root_.P2Mf6bd8d28 renaming h31 → _Pv
theorem _root_.P2Mf6bd8d28.h34 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    (_root_.CurrentAFT.AffineRealization.matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).mulVec
      (Sum.elim input.1 (fun _ : Unit => input.2)) =
      Sum.elim (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).1
        (fun _ : Unit => (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).2) := by
  rw [_root_.CurrentAFT.AffineRealization.matrix, _root_.AFT.transportBlockMatrix, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, ← Matrix.mulVec_mulVec, _Pv,
    _root_.CurrentAFT.AffineRealization.linearPart, _root_.AFT.blockTransport, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
  congr 1
  ext index
  simp [Matrix.mulVec, dotProduct, mul_comm]
open _root_.P2Mf6bd8d28 renaming h34 → _Py
end
open _root_.P2Mf6bd8d28 renaming h31 → _Pv
open _root_.P2Mf6bd8d28 renaming h32 → _Pw
open _root_.P2Mf6bd8d28 renaming h33 → _Px
open _root_.P2Mf6bd8d28 renaming h34 → _Py
end CurrentAFT.AffineRealization
open _root_.P2Mf6bd8d28 renaming h31 → _Pv
open _root_.P2Mf6bd8d28 renaming h32 → _Pw
open _root_.P2Mf6bd8d28 renaming h33 → _Px
open _root_.P2Mf6bd8d28 renaming h34 → _Py
end
open _root_.P2Mf6bd8d28 renaming h31 → _Pv
open _root_.P2Mf6bd8d28 renaming h32 → _Pw
open _root_.P2Mf6bd8d28 renaming h33 → _Px
open _root_.P2Mf6bd8d28 renaming h34 → _Py
namespace CurrentAFT.ActualBlockFock.blockLawAt.match_1
end CurrentAFT.ActualBlockFock.blockLawAt.match_1
namespace CurrentAFT.ActualBlockFock.primaryLawAt
end CurrentAFT.ActualBlockFock.primaryLawAt
namespace CurrentAFT.ActualBlockMean
end CurrentAFT.ActualBlockMean
namespace CurrentAFT.ActualBlockMean.attachmentRoots
end CurrentAFT.ActualBlockMean.attachmentRoots
namespace CurrentAFT.ActualBlockMean.blockVector
end CurrentAFT.ActualBlockMean.blockVector
namespace CurrentAFT.ActualBlockMean.bodyVector
end CurrentAFT.ActualBlockMean.bodyVector
namespace CurrentAFT.ActualBlockMean.centerRoots
end CurrentAFT.ActualBlockMean.centerRoots
namespace CurrentAFT.ActualBlockMean.queueRoots
end CurrentAFT.ActualBlockMean.queueRoots
namespace CurrentAFT.ActualBlockMean.rootAt
end CurrentAFT.ActualBlockMean.rootAt
namespace CurrentAFT.ActualBlockMean.rootedLaw
end CurrentAFT.ActualBlockMean.rootedLaw
namespace CurrentAFT.ActualCycleMeanMGF
end CurrentAFT.ActualCycleMeanMGF
namespace CurrentAFT.ActualCycleMeanMGF.realizedResponse
end CurrentAFT.ActualCycleMeanMGF.realizedResponse
section
namespace CurrentAFT.CyclePathClosure
open AFT PublicCharge AffineBaseline
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem _root_.P2Mf6bd8d28.h109 (count : ℕ) (edges : Fin count → ℤ) :
    _root_.AFT.pathLoad count edges = Fin.snoc edges 0 - Fin.cons 0 edges := by
  induction count with
  | zero =>
    funext index
    have hi : index = (0 : Fin 1) := Fin.eq_zero index
    subst index
    simp [_root_.AFT.pathLoad, Fin.snoc_zero]
  | succ count ih =>
    have he : edges = Fin.cons (edges 0) (Fin.tail edges) := (Fin.cons_self_tail edges).symm
    conv_rhs => rw [he, ← Fin.cons_snoc_eq_snoc_cons]
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp [_root_.AFT.pathLoad]
    · simp only [_root_.AFT.pathLoad, Fin.cons_succ, Pi.sub_apply, ih]
      refine Fin.cases ?_ (fun next => ?_) rest <;> simp
open _root_.P2Mf6bd8d28 renaming h109 → _P31
end
open _root_.P2Mf6bd8d28 renaming h109 → _P31
end CurrentAFT.CyclePathClosure
open _root_.P2Mf6bd8d28 renaming h109 → _P31
end
open _root_.P2Mf6bd8d28 renaming h109 → _P31
namespace AFT.edgeBasisChangeMatrix
end AFT.edgeBasisChangeMatrix
namespace CurrentAFT.ActualPublicCharge
end CurrentAFT.ActualPublicCharge
namespace CurrentAFT.ActualPublicCharge.Core
end CurrentAFT.ActualPublicCharge.Core
namespace CurrentAFT.ActualPublicCharge.Core.mk
end CurrentAFT.ActualPublicCharge.Core.mk
namespace CurrentAFT.ActualPublicCharge.centerAt
end CurrentAFT.ActualPublicCharge.centerAt
namespace CurrentAFT.ActualPublicCharge.centerAt.match_1
end CurrentAFT.ActualPublicCharge.centerAt.match_1
namespace CurrentAFT.ActualPublicCharge.queueSet
end CurrentAFT.ActualPublicCharge.queueSet
namespace CurrentAFT.AffineRealization
end CurrentAFT.AffineRealization
namespace CurrentAFT.AffineRealization.linearPart
end CurrentAFT.AffineRealization.linearPart
namespace CurrentAFT.AffineRealization.matrix
end CurrentAFT.AffineRealization.matrix
namespace CurrentAFT.AffineRealization.queueColumn
end CurrentAFT.AffineRealization.queueColumn
namespace CurrentAFT.CyclePathClosure
end CurrentAFT.CyclePathClosure
namespace CurrentAFT.PublicEndpointPlacement
end CurrentAFT.PublicEndpointPlacement
namespace CurrentAFT.PublicEndpointPlacement.toAssembly
end CurrentAFT.PublicEndpointPlacement.toAssembly
namespace CurrentAFT.PublicEndpointPlacement.toAssembly.match_1
end CurrentAFT.PublicEndpointPlacement.toAssembly.match_1
namespace CurrentAFT.PublicEndpointPlacement.toPhysical
end CurrentAFT.PublicEndpointPlacement.toPhysical
namespace CurrentAFT.PublicEndpointPlacement.toPhysical.match_3
end CurrentAFT.PublicEndpointPlacement.toPhysical.match_3
section
namespace CurrentAFT.CurrentAffineGeometry
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  LobsterCoordinates AffineRealization PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
theorem _root_.P2Mf6bd8d28.h57 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex)) =
      core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex) := by
  simp [_root_.CurrentAFT.CurrentAffineGeometry.relabeling]
open _root_.P2Mf6bd8d28 renaming h57 → _P1l
end
open _root_.P2Mf6bd8d28 renaming h57 → _P1l
end CurrentAFT.CurrentAffineGeometry
open _root_.P2Mf6bd8d28 renaming h57 → _P1l
end
open _root_.P2Mf6bd8d28 renaming h57 → _P1l
section
namespace CurrentAFT.GaussianWindowProtection
open AFT GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
theorem _root_.P2Mf6bd8d28.h112 (width : ℝ) (hwidth : 0 < width) (point : ℤ) :
    _root_.AFT.GaussianSource.integerMass width point = (_root_.AFT.GaussianSource.integerGaussian width hwidth point).toReal :=
  (_Ph width hwidth point).symm
open _root_.P2Mf6bd8d28 renaming h112 → _P34
end
open _root_.P2Mf6bd8d28 renaming h112 → _P34
end CurrentAFT.GaussianWindowProtection
open _root_.P2Mf6bd8d28 renaming h112 → _P34
end
open _root_.P2Mf6bd8d28 renaming h112 → _P34
namespace CurrentAFT.BinaryLegCoefficientExtraction
end CurrentAFT.BinaryLegCoefficientExtraction
namespace CurrentAFT.RationalLegCoefficientExtraction
end CurrentAFT.RationalLegCoefficientExtraction
namespace CurrentAFT.RationalLegCoefficientExtraction.slotNumber
end CurrentAFT.RationalLegCoefficientExtraction.slotNumber
namespace CurrentAFT.RationalLegFamilyTable
end CurrentAFT.RationalLegFamilyTable
namespace CurrentAFT.RationalLegFamilyTable.positive
end CurrentAFT.RationalLegFamilyTable.positive
section
namespace CurrentAFT.BinaryLegSelectedCoefficient
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  GradedControlAlgebra RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h44 (selected : Finset (Fin 3)) : ∃ entry : _root_.CurrentAFT.BinaryLegSelectedCoefficient.Entry, entry.selected=selected ∧ _root_.CurrentAFT.BinaryLegSelectedCoefficient.Valid entry := by
  obtain ⟨program,hprogram⟩ := _P1f selected.card
  refine ⟨⟨selected,Vector.ofFn (fun index => ((Finset.orderIsoOfFin selected rfl) index).val),program⟩,rfl,?_,hprogram⟩
  intro index
  exact Vector.get_ofFn _ _
open _root_.P2Mf6bd8d28 renaming h44 → _P18
theorem _root_.P2Mf6bd8d28.h43 : ∃ entries : Vector _root_.CurrentAFT.BinaryLegSelectedCoefficient.Entry 8, ∃ ordering : Fin 8 ≃ Finset (Fin 3),
    (∀ index, (entries.get index).selected=ordering index) ∧ ∀ index, _root_.CurrentAFT.BinaryLegSelectedCoefficient.Valid (entries.get index) := by
  have hcard : Fintype.card (Finset (Fin 3))=8 := by simp
  let ordering : Fin 8 ≃ Finset (Fin 3) := (Fintype.equivFinOfCardEq hcard).symm
  choose entry hselected hvalid using _P18
  refine ⟨Vector.ofFn (fun index => entry (ordering index)),ordering,?_,?_⟩
  · intro index
    rw [Vector.get_ofFn]
    exact hselected _
  · intro index
    rw [Vector.get_ofFn]
    exact hvalid _
open _root_.P2Mf6bd8d28 renaming h43 → _P17
end
open _root_.P2Mf6bd8d28 renaming h43 → _P17
open _root_.P2Mf6bd8d28 renaming h44 → _P18
end CurrentAFT.BinaryLegSelectedCoefficient
open _root_.P2Mf6bd8d28 renaming h43 → _P17
open _root_.P2Mf6bd8d28 renaming h44 → _P18
end
open _root_.P2Mf6bd8d28 renaming h43 → _P17
open _root_.P2Mf6bd8d28 renaming h44 → _P18
namespace CurrentAFT.BinaryLegGroup
end CurrentAFT.BinaryLegGroup
namespace CurrentAFT.BinaryLegGroup.current
end CurrentAFT.BinaryLegGroup.current
namespace CurrentAFT.BinaryLegGroup.workPolynomial
end CurrentAFT.BinaryLegGroup.workPolynomial
namespace CurrentAFT.BinaryNormalizedPrimary
end CurrentAFT.BinaryNormalizedPrimary
namespace CurrentAFT.BinaryNormalizedPrimary.jointHeight
end CurrentAFT.BinaryNormalizedPrimary.jointHeight
namespace CurrentAFT.BinaryNormalizedPrimary.jointWork
end CurrentAFT.BinaryNormalizedPrimary.jointWork
namespace CurrentAFT.BinaryNormalizedPrimary.numerator
end CurrentAFT.BinaryNormalizedPrimary.numerator
namespace CurrentAFT.BinaryNormalizedPrimary.rootBits
end CurrentAFT.BinaryNormalizedPrimary.rootBits
namespace CurrentAFT.BinaryNormalizedPrimary.workPolynomial
end CurrentAFT.BinaryNormalizedPrimary.workPolynomial
namespace CurrentAFT.BinaryOrdinaryGroup
end CurrentAFT.BinaryOrdinaryGroup
namespace CurrentAFT.BinaryOrdinaryGroup.current
end CurrentAFT.BinaryOrdinaryGroup.current
namespace CurrentAFT.BinaryOrdinaryGroup.workPolynomial
end CurrentAFT.BinaryOrdinaryGroup.workPolynomial
namespace CurrentAFT.BinarySingletonGroup
end CurrentAFT.BinarySingletonGroup
namespace CurrentAFT.BinarySingletonGroup.current
end CurrentAFT.BinarySingletonGroup.current
namespace CurrentAFT.BinarySingletonGroup.workPolynomial
end CurrentAFT.BinarySingletonGroup.workPolynomial
namespace CurrentAFT.RationalRootGroupProgram
end CurrentAFT.RationalRootGroupProgram
namespace CurrentAFT.RationalRootGroupProgram.LocalRole
end CurrentAFT.RationalRootGroupProgram.LocalRole
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.center
end CurrentAFT.RationalRootGroupProgram.LocalRole.center
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.leg
end CurrentAFT.RationalRootGroupProgram.LocalRole.leg
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.ordinary
end CurrentAFT.RationalRootGroupProgram.LocalRole.ordinary
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.primary
end CurrentAFT.RationalRootGroupProgram.LocalRole.primary
namespace CurrentAFT.RationalRootGroupProgram.LocalRole.queue
end CurrentAFT.RationalRootGroupProgram.LocalRole.queue
namespace CurrentAFT.RationalRootGroupProgram.localTable
end CurrentAFT.RationalRootGroupProgram.localTable
namespace CurrentAFT.RationalRootGroupProgram.localTable.match_1
end CurrentAFT.RationalRootGroupProgram.localTable.match_1
namespace CurrentAFT.RationalRootGroupProgram.role
end CurrentAFT.RationalRootGroupProgram.role
namespace CurrentAFT.RationalRootGroupProgram.role.match_3
end CurrentAFT.RationalRootGroupProgram.role.match_3
namespace CurrentAFT.RationalRootGroupProgram.sourceNatural
end CurrentAFT.RationalRootGroupProgram.sourceNatural
namespace CurrentAFT.RationalRootGroupProgram.sourceNatural.match_1
end CurrentAFT.RationalRootGroupProgram.sourceNatural.match_1
namespace CurrentAFT.RationalRootGroupProgram.table
end CurrentAFT.RationalRootGroupProgram.table
namespace CurrentAFT.RootReferenceColumns
end CurrentAFT.RootReferenceColumns
namespace CurrentAFT.RootReferenceColumns.legAt
end CurrentAFT.RootReferenceColumns.legAt
namespace CurrentAFT.RootReferenceColumns.reducedColumn
end CurrentAFT.RootReferenceColumns.reducedColumn
namespace CurrentAFT.RootReferenceColumns.reducedColumn.match_1
end CurrentAFT.RootReferenceColumns.reducedColumn.match_1
namespace CurrentAFT.RootReferenceColumns.singletonAt
end CurrentAFT.RootReferenceColumns.singletonAt
namespace CurrentAFT.RootReferenceColumns.unselectedAt
end CurrentAFT.RootReferenceColumns.unselectedAt
namespace CurrentAFT.RootReferenceColumns.unselectedAt.match_1
end CurrentAFT.RootReferenceColumns.unselectedAt.match_1
section
namespace CurrentAFT.BinaryRootGroupProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open RationalRootGroupProgram (LocalRole)
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h50 (order : ℕ) : ∃ data : _root_.CurrentAFT.BinaryRootGroupProgram.Data order, _root_.CurrentAFT.BinaryRootGroupProgram.Correct data := by
  obtain ⟨programs,hcorrect,hcomplete⟩ := _P33 order
  obtain ⟨primaryEntries,primaryOrder,hprimary,hprimaryValid⟩ := _P19
  obtain ⟨legEntries,legOrder,hleg,hlegValid⟩ := _P17
  refine ⟨⟨programs,primaryEntries.get 0,primaryEntries,legEntries.get 0,legEntries⟩,
    hcorrect,hcomplete,⟨primaryOrder,hprimary,hprimaryValid⟩,⟨legOrder,hleg,hlegValid⟩⟩
open _root_.P2Mf6bd8d28 renaming h50 → _P1e
end
open _root_.P2Mf6bd8d28 renaming h50 → _P1e
end CurrentAFT.BinaryRootGroupProgram
open _root_.P2Mf6bd8d28 renaming h50 → _P1e
end
open _root_.P2Mf6bd8d28 renaming h50 → _P1e
namespace CurrentAFT.BinaryReferenceTables
end CurrentAFT.BinaryReferenceTables
namespace CurrentAFT.BinaryReferenceTables.Result
end CurrentAFT.BinaryReferenceTables.Result
namespace CurrentAFT.BinaryReferenceTables.Result.mk
end CurrentAFT.BinaryReferenceTables.Result.mk
namespace CurrentAFT.BinaryReferenceTables.centerHeightPolynomial
end CurrentAFT.BinaryReferenceTables.centerHeightPolynomial
namespace CurrentAFT.BinaryReferenceTables.current
end CurrentAFT.BinaryReferenceTables.current
namespace CurrentAFT.BinaryReferenceTables.currentWorkPolynomial
end CurrentAFT.BinaryReferenceTables.currentWorkPolynomial
namespace CurrentAFT.BinaryReferenceTables.heightPolynomial
end CurrentAFT.BinaryReferenceTables.heightPolynomial
namespace CurrentAFT.BinaryReferenceTables.marginPolynomial
end CurrentAFT.BinaryReferenceTables.marginPolynomial
namespace CurrentAFT.BinaryReferenceTables.referenceHeightPolynomial
end CurrentAFT.BinaryReferenceTables.referenceHeightPolynomial
namespace CurrentAFT.WeightedPointKernelProgram
end CurrentAFT.WeightedPointKernelProgram
namespace CurrentAFT.WeightedPointKernelProgram.current
end CurrentAFT.WeightedPointKernelProgram.current
namespace CurrentAFT.WeightedPointKernelProgram.weightedTensor
end CurrentAFT.WeightedPointKernelProgram.weightedTensor
section
namespace CurrentAFT.BinaryWeightedPointKernel
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h52 (r s : ℕ) : ∃ program : _root_.CurrentAFT.BinaryWeightedPointKernel.Program r s, program.meaning _root_.AFT.BinaryArithmetic.RationalBits.decode = _root_.CurrentAFT.BinaryWeightedPointKernel.pointSyntax r s :=
  _Pl (_root_.CurrentAFT.BinaryWeightedPointKernel.pointSyntax r s)
open _root_.P2Mf6bd8d28 renaming h52 → _P1g
end
open _root_.P2Mf6bd8d28 renaming h52 → _P1g
end CurrentAFT.BinaryWeightedPointKernel
open _root_.P2Mf6bd8d28 renaming h52 → _P1g
end
open _root_.P2Mf6bd8d28 renaming h52 → _P1g
namespace CurrentAFT.BinaryWeightedPointKernel
end CurrentAFT.BinaryWeightedPointKernel
namespace CurrentAFT.BinaryWeightedPointKernel.atom
end CurrentAFT.BinaryWeightedPointKernel.atom
namespace CurrentAFT.BinaryWeightedPointKernel.atom.match_1
end CurrentAFT.BinaryWeightedPointKernel.atom.match_1
namespace CurrentAFT.BinaryWeightedPointKernel.atomWorkPolynomial
end CurrentAFT.BinaryWeightedPointKernel.atomWorkPolynomial
namespace CurrentAFT.BinaryWeightedPointKernel.current
end CurrentAFT.BinaryWeightedPointKernel.current
namespace CurrentAFT.BinaryWeightedPointKernel.factor
end CurrentAFT.BinaryWeightedPointKernel.factor
namespace CurrentAFT.BinaryWeightedPointKernel.heightPolynomial
end CurrentAFT.BinaryWeightedPointKernel.heightPolynomial
namespace CurrentAFT.BinaryWeightedPointKernel.pointSyntax
end CurrentAFT.BinaryWeightedPointKernel.pointSyntax
namespace CurrentAFT.BinaryWeightedPointKernel.product
end CurrentAFT.BinaryWeightedPointKernel.product
namespace CurrentAFT.BinaryWeightedPointKernel.productList
end CurrentAFT.BinaryWeightedPointKernel.productList
namespace CurrentAFT.BinaryWeightedPointKernel.productList.match_1
end CurrentAFT.BinaryWeightedPointKernel.productList.match_1
namespace CurrentAFT.BinaryWeightedPointKernel.withTables
end CurrentAFT.BinaryWeightedPointKernel.withTables
namespace CurrentAFT.BinaryWeightedPointKernel.workPolynomial
end CurrentAFT.BinaryWeightedPointKernel.workPolynomial
namespace CurrentAFT.FixedFamilyPrograms
end CurrentAFT.FixedFamilyPrograms
namespace CurrentAFT.FixedFamilyPrograms.literals
end CurrentAFT.FixedFamilyPrograms.literals
namespace CurrentAFT.FixedFamilyPrograms.lookup
end CurrentAFT.FixedFamilyPrograms.lookup
namespace CurrentAFT.FixedFamilyPrograms.lookup.match_1
end CurrentAFT.FixedFamilyPrograms.lookup.match_1
namespace CurrentAFT.FixedFamilyPrograms.matchArity
end CurrentAFT.FixedFamilyPrograms.matchArity
namespace CurrentAFT.FixedFamilyPrograms.nodes
end CurrentAFT.FixedFamilyPrograms.nodes
section
namespace CurrentAFT.BinaryFixedPointPrograms
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open FixedFamilyPrograms (matchArity matchArity_value matchArity_work)
noncomputable section
open scoped Classical BigOperators
theorem _root_.P2Mf6bd8d28.h41 (order : ℕ) : ∃ list : List (_root_.CurrentAFT.BinaryFixedPointPrograms.Entry order), _root_.CurrentAFT.BinaryFixedPointPrograms.Correct order list ∧ _root_.CurrentAFT.BinaryFixedPointPrograms.Complete order list := by
  let programs := fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => Classical.choose (_P1g arity.val.1.val arity.val.2.val)
  let list : List (_root_.CurrentAFT.BinaryFixedPointPrograms.Entry order) := (Finset.univ : Finset (_root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)).toList.map
    (fun arity => ⟨arity, programs arity⟩)
  refine ⟨list, ?_, ?_⟩
  · intro entry hentry
    obtain ⟨arity, _, he⟩ := List.mem_map.mp hentry
    subst entry
    exact Classical.choose_spec (_P1g arity.val.1.val arity.val.2.val)
  · intro arity
    refine ⟨programs arity, List.mem_map.mpr ?_⟩
    exact ⟨arity, Finset.mem_toList.mpr (Finset.mem_univ arity), rfl⟩
open _root_.P2Mf6bd8d28 renaming h41 → _P15
end
open _root_.P2Mf6bd8d28 renaming h41 → _P15
end CurrentAFT.BinaryFixedPointPrograms
open _root_.P2Mf6bd8d28 renaming h41 → _P15
end
open _root_.P2Mf6bd8d28 renaming h41 → _P15
namespace CurrentAFT.BinaryFixedPointPrograms
end CurrentAFT.BinaryFixedPointPrograms
namespace CurrentAFT.BinaryFixedPointPrograms.heightPolynomial
end CurrentAFT.BinaryFixedPointPrograms.heightPolynomial
namespace CurrentAFT.BinaryFixedPointPrograms.lookup
end CurrentAFT.BinaryFixedPointPrograms.lookup
namespace CurrentAFT.BinaryFixedPointPrograms.lookup.match_1
end CurrentAFT.BinaryFixedPointPrograms.lookup.match_1
namespace CurrentAFT.BinaryFixedPointPrograms.workPolynomial
end CurrentAFT.BinaryFixedPointPrograms.workPolynomial
namespace CurrentAFT.BinaryRootGroupProgram
end CurrentAFT.BinaryRootGroupProgram
namespace CurrentAFT.BinaryRootGroupProgram.Data
end CurrentAFT.BinaryRootGroupProgram.Data
namespace CurrentAFT.BinaryRootGroupProgram.Data.mk
end CurrentAFT.BinaryRootGroupProgram.Data.mk
namespace CurrentAFT.BinaryRootGroupProgram.heightPolynomial
end CurrentAFT.BinaryRootGroupProgram.heightPolynomial
namespace CurrentAFT.BinaryRootGroupProgram.localTable
end CurrentAFT.BinaryRootGroupProgram.localTable
namespace CurrentAFT.BinaryRootGroupProgram.primary
end CurrentAFT.BinaryRootGroupProgram.primary
namespace CurrentAFT.BinaryRootGroupProgram.workPolynomial
end CurrentAFT.BinaryRootGroupProgram.workPolynomial
namespace CurrentAFT.RationalFullResponseProgram
end CurrentAFT.RationalFullResponseProgram
section
namespace CurrentAFT.BinaryFullResponseData
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem _root_.P2Mf6bd8d28.h42 (order : ℕ) : ∃ data : _root_.CurrentAFT.BinaryFullResponseData.Data order, _root_.CurrentAFT.BinaryFullResponseData.Correct data := by
  obtain ⟨groups,hgroups⟩ := _P1e order
  obtain ⟨points,hpoints,hcomplete⟩ := _P15 order
  exact ⟨⟨groups,points⟩,hgroups,hpoints,hcomplete⟩
open _root_.P2Mf6bd8d28 renaming h42 → _P16
end
open _root_.P2Mf6bd8d28 renaming h42 → _P16
end CurrentAFT.BinaryFullResponseData
open _root_.P2Mf6bd8d28 renaming h42 → _P16
end
open _root_.P2Mf6bd8d28 renaming h42 → _P16
namespace CurrentAFT.CurrentCoreProposal
end CurrentAFT.CurrentCoreProposal
namespace CurrentAFT.CurrentCoreProposal.materializedLaw
end CurrentAFT.CurrentCoreProposal.materializedLaw
namespace CurrentAFT.CurrentLayoutDraw
end CurrentAFT.CurrentLayoutDraw
namespace CurrentAFT.CurrentLayoutDraw.Cache
end CurrentAFT.CurrentLayoutDraw.Cache
namespace CurrentAFT.CurrentLayoutDraw.workPolynomial
end CurrentAFT.CurrentLayoutDraw.workPolynomial
section
namespace CurrentAFT.CurrentEmissionRootOrder
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources CurrentCoreProposal
open ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount
  CurrentCoreProposal.draw addCounter subtractCounter lessCounter
theorem _root_.P2Mf6bd8d28.h98 (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) :
    (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate count front hprefix index).value.val = if index.val < front then count - front + index.val else index.val - front := by
  by_cases hi : index.val < front
  · have hs : (_root_.AFT.BinaryArithmetic.lessCounter index.val front).value = true := (_root_.AFT.BinaryArithmetic.lessCounter_value _ _).mpr hi
    simp only [_root_.CurrentAFT.CurrentEmissionRootOrder.rotate, dif_pos hs, Fin.val_mk, _root_.AFT.BinaryArithmetic.addCounter_value, _root_.AFT.BinaryArithmetic.subtractCounter_value, if_pos hi]
  · have hs : ¬(_root_.AFT.BinaryArithmetic.lessCounter index.val front).value = true := by simpa only [_root_.AFT.BinaryArithmetic.lessCounter_value] using hi
    simp only [_root_.CurrentAFT.CurrentEmissionRootOrder.rotate, dif_neg hs, Fin.val_mk, _root_.AFT.BinaryArithmetic.subtractCounter_value, if_neg hi]
open _root_.P2Mf6bd8d28 renaming h98 → _P2q
theorem _root_.P2Mf6bd8d28.h97 (security : ℕ) (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).body) :
    _root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security
      (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate (_root_.CurrentAFT.CurrentProposalDimensions.current security).body (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionRootOrder.legs_le_body security) index).value =
    _root_.CurrentAFT.CurrentLayoutDraw.canonicalLayout security (_root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security ((_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).symm index)) := by
  obtain ⟨leg | (center | queue), rfl⟩ := (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).surjective index
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals apply Fin.ext
  · have hi : leg.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by simpa only [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1] using leg.isLt
    have hcount := _root_.CurrentAFT.CurrentEmissionRootOrder.root_count security
    change (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inl leg))).value.val = _
    rw [_P2q]
    have hv : (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inl leg)).val = leg.val := rfl
    rw [hv, if_pos hi]
    change (_root_.CurrentAFT.CurrentProposalDimensions.current security).body - (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs + leg.val =
      _root_.CurrentAFT.BackgroundPopulationBounds.freeCount security + (_root_.CurrentAFT.Parameters.modulus security + leg.val)
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
    unfold _root_.CurrentAFT.BackgroundPopulationBounds.freeCount _root_.CurrentAFT.ActualBlockFock.centerCount at *
    omega
  · change (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inl center)))).value.val = _
    rw [_P2q]
    have hv : (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inl center))).val = _root_.CurrentAFT.Parameters.legCount security + center.val := rfl
    rw [hv]
    have hn : ¬_root_.CurrentAFT.Parameters.legCount security + center.val < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]; omega
    rw [if_neg hn]
    change _root_.CurrentAFT.Parameters.legCount security + center.val - (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs = center.val
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
    omega
  · change (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inr queue)))).value.val = _
    rw [_P2q]
    have hv : (_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (.inr (.inr queue))).val = _root_.CurrentAFT.Parameters.legCount security + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) := rfl
    rw [hv]
    have hn : ¬_root_.CurrentAFT.Parameters.legCount security + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) < (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs := by
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]; omega
    rw [if_neg hn]
    change _root_.CurrentAFT.Parameters.legCount security + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val) - (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs =
      _root_.CurrentAFT.BackgroundPopulationBounds.freeCount security + queue.val
    rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
    unfold _root_.CurrentAFT.BackgroundPopulationBounds.freeCount _root_.CurrentAFT.ActualBlockFock.centerCount
    omega
open _root_.P2Mf6bd8d28 renaming h97 → _P2p
theorem _root_.P2Mf6bd8d28.h96 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).body) :
    (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout data).value.get index =
      data.body.inverse.get (layout.forward.get (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate (_root_.CurrentAFT.CurrentProposalDimensions.current security).body (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionRootOrder.legs_le_body security) index).value) := by
  simp only [_root_.CurrentAFT.CurrentEmissionRootOrder.positions, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mf6bd8d28 renaming h96 → CurrentAFT.CurrentEmissionRootOrder.positions_value
open _root_.P2Mf6bd8d28 renaming h96 → _P2o
private theorem _root_.P2Mf6bd8d28.h834 {State Target : Type*} (equiv : State ≃ Target) (permutation : Equiv.Perm State) (state : State) :
    (equiv.permCongr permutation).symm (equiv state) = equiv (permutation.symm state) := by
  apply (equiv.permCongr permutation).injective
  simp only [Equiv.apply_symm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
open _root_.P2Mf6bd8d28 renaming h834 → _Pn6
theorem _root_.P2Mf6bd8d28.h95 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).body) :
    _root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security ((_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout data).value.get index) =
      data.core.bodyPermutation.symm (layout.layout (_root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security ((_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).symm index))) := by
  rw [_P2o]
  change _root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security
      (data.body.toEquiv.symm (layout.toEquiv (_root_.CurrentAFT.CurrentEmissionRootOrder.rotate _ _ _ index).value)) =
    ((_root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security).permCongr data.body.toEquiv).symm
      (((_root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv security).permCongr layout.toEquiv)
        (_root_.CurrentAFT.CurrentLayoutDraw.canonicalLayout security (_root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security ((_root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security).symm index))))
  rw [← _P2p security index, Equiv.permCongr_apply, Equiv.symm_apply_apply, _Pn6]
open _root_.P2Mf6bd8d28 renaming h95 → _P2n
end CurrentAFT.CurrentEmissionRootOrder
open _root_.P2Mf6bd8d28 renaming h95 → _P2n
open _root_.P2Mf6bd8d28 renaming h96 → CurrentAFT.CurrentEmissionRootOrder.positions_value
open _root_.P2Mf6bd8d28 renaming h96 → _P2o
open _root_.P2Mf6bd8d28 renaming h97 → _P2p
open _root_.P2Mf6bd8d28 renaming h98 → _P2q
open _root_.P2Mf6bd8d28 renaming h834 → _Pn6
end
open _root_.P2Mf6bd8d28 renaming h95 → _P2n
open _root_.P2Mf6bd8d28 renaming h96 → CurrentAFT.CurrentEmissionRootOrder.positions_value
open _root_.P2Mf6bd8d28 renaming h96 → _P2o
open _root_.P2Mf6bd8d28 renaming h97 → _P2p
open _root_.P2Mf6bd8d28 renaming h98 → _P2q
namespace AFT.BinaryArithmetic.binaryPhysicalInitialLoad
end AFT.BinaryArithmetic.binaryPhysicalInitialLoad
namespace AFT.BinaryArithmetic.binaryPhysicalQueueLoad
end AFT.BinaryArithmetic.binaryPhysicalQueueLoad
namespace AFT.BinaryArithmetic.binaryPhysicalVertex
end AFT.BinaryArithmetic.binaryPhysicalVertex
namespace AFT.BinaryArithmetic.binaryRootRead
end AFT.BinaryArithmetic.binaryRootRead
namespace AFT.BinaryArithmetic.initialBlockEntry
end AFT.BinaryArithmetic.initialBlockEntry
namespace AFT.BinaryArithmetic.initialBlockEntry.match_1
end AFT.BinaryArithmetic.initialBlockEntry.match_1
namespace AFT.BinaryArithmetic.initialBlockEntry_length
end AFT.BinaryArithmetic.initialBlockEntry_length
namespace AFT.BinaryArithmetic.initialBlockEntry_work
end AFT.BinaryArithmetic.initialBlockEntry_work
namespace AFT.BinaryArithmetic.queueBlockEntry
end AFT.BinaryArithmetic.queueBlockEntry
namespace AFT.BinaryArithmetic.queueBlockEntry_length
end AFT.BinaryArithmetic.queueBlockEntry_length
namespace AFT.BinaryArithmetic.queueBlockEntry_work
end AFT.BinaryArithmetic.queueBlockEntry_work
namespace AFT.blockVertexNumbering
end AFT.blockVertexNumbering
namespace AFT.blockVertexSplit.match_1
end AFT.blockVertexSplit.match_1
namespace AFT.blockVertexSplit.match_3
end AFT.blockVertexSplit.match_3
namespace CurrentAFT.CurrentEmissionRootOrder
end CurrentAFT.CurrentEmissionRootOrder
namespace CurrentAFT.CurrentEmissionRootOrder.positions
end CurrentAFT.CurrentEmissionRootOrder.positions
namespace CurrentAFT.CurrentEmissionRootOrder.rootToRole
end CurrentAFT.CurrentEmissionRootOrder.rootToRole
namespace CurrentAFT.CurrentEmissionRootOrder.rotate
end CurrentAFT.CurrentEmissionRootOrder.rotate
namespace CurrentAFT.CurrentPhysicalNumbering
end CurrentAFT.CurrentPhysicalNumbering
namespace CurrentAFT.CurrentPhysicalNumbering.blocks
end CurrentAFT.CurrentPhysicalNumbering.blocks
namespace CurrentAFT.CurrentPhysicalNumbering.blocks.match_1
end CurrentAFT.CurrentPhysicalNumbering.blocks.match_1
namespace CurrentAFT.CurrentPhysicalNumbering.blocks.match_3
end CurrentAFT.CurrentPhysicalNumbering.blocks.match_3
namespace CurrentAFT.CurrentPhysicalNumbering.split
end CurrentAFT.CurrentPhysicalNumbering.split
namespace CurrentAFT.CurrentPhysicalNumbering.split.match_1
end CurrentAFT.CurrentPhysicalNumbering.split.match_1
section
namespace CurrentAFT.CurrentEmissionMetadata
open AFT AFT.BinaryArithmetic CurrentProposalDimensions CurrentProposalResources
open ActualBlockFock
set_option maxHeartbeats 1000000
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount Parameters.dimension
  subtractCounter
attribute [local irreducible] CurrentEmissionMetadata.current
theorem _root_.P2Mf6bd8d28.h94 (security : ℕ)
    (point : Sigma (_root_.AFT.blockSlotsProgram (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest)) :
    _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security (_root_.AFT.physicalVertexNumberingProgram _ _ _ (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1 point) =
      _root_.CurrentAFT.CurrentPhysicalNumbering.numbering security (_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv security point) := by
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    apply Fin.ext
    change _ = (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security ⟨.inl (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg), slot⟩).val
    rw [_P2w]
    change slot.val + 3 * leg.val = slot.val + 3 * leg.val
    rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    · apply Fin.ext
      change _ = (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, _P2v]
      have hv := congrArg Fin.val he
      change center.val = body.val at hv
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) = _root_.CurrentAFT.Parameters.legCount security * 3 + center.val
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
      omega
    · apply Fin.ext
      change _ = (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, _P2x]
      have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val = body.val at hv
      change (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) =
        _root_.CurrentAFT.Parameters.legCount security * 3 + (_root_.CurrentAFT.ActualBlockFock.centerCount security + queue.val)
      rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
      omega
open _root_.P2Mf6bd8d28 renaming h94 → _P2m
end CurrentAFT.CurrentEmissionMetadata
open _root_.P2Mf6bd8d28 renaming h94 → _P2m
end
open _root_.P2Mf6bd8d28 renaming h94 → _P2m
namespace AFT.BinaryArithmetic.lessCounter
end AFT.BinaryArithmetic.lessCounter
namespace AFT.BinaryArithmetic.lessCounter.match_1
end AFT.BinaryArithmetic.lessCounter.match_1
namespace AFT.BinaryArithmetic.powerCounter
end AFT.BinaryArithmetic.powerCounter
namespace AFT.BinaryArithmetic.powerCounter.match_1
end AFT.BinaryArithmetic.powerCounter.match_1
namespace AFT.BinaryArithmetic.powerCounterWork
end AFT.BinaryArithmetic.powerCounterWork
namespace AFT.BinaryArithmetic.subtractCounter
end AFT.BinaryArithmetic.subtractCounter
section
namespace CurrentAFT.CurrentBinaryIncidence
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 700000
private theorem _root_.P2Mf6bd8d28.h833 (condition : Prop) [Decidable condition] (first second : _root_.AFT.BinaryArithmetic.IntegerBits) :
    (if condition then first else second).decode = if condition then first.decode else second.decode := by
  split_ifs <;> rfl
open _root_.P2Mf6bd8d28 renaming h833 → _Pn5
theorem _root_.P2Mf6bd8d28.h73 (bodyEdges column root : ℕ) :
    (_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry bodyEdges column root).value.decode = if column < bodyEdges then
      (if root = column then 1 else 0) - (if root = column + 1 then 1 else 0) else 0 := by
  have hi : (_root_.AFT.BinaryArithmetic.lessCounter column bodyEdges).value = true ↔ column < bodyEdges := _root_.AFT.BinaryArithmetic.lessCounter_value _ _
  have hp : (_root_.AFT.BinaryArithmetic.equalCounter root column).value = true ↔ root = column := _root_.AFT.BinaryArithmetic.equalCounter_value _ _
  have hn : (_root_.AFT.BinaryArithmetic.equalCounter root (_root_.AFT.BinaryArithmetic.addCounter column 1).count).value = true ↔ root = column + 1 := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  simp only [_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry, _Pn5, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.one_value, _root_.AFT.BinaryArithmetic.IntegerBits.zero_value, hi, hp, hn]
open _root_.P2Mf6bd8d28 renaming h73 → _P21
theorem _root_.P2Mf6bd8d28.h72 {legs : ℕ} (bodyEdges column : ℕ) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits legs) (leg : Fin legs) :
    let first := (if column = bodyEdges + leg.val then (scale.get leg).decode else 0) +
      (if column = bodyEdges + leg.val + legs then (shear.get leg).decode else 0)
    let second := if column = bodyEdges + leg.val + legs then (1 : ℤ) else 0
    ((_root_.CurrentAFT.CurrentBinaryIncidence.legEntries bodyEdges column scale shear leg).value.1.decode,
      ((_root_.CurrentAFT.CurrentBinaryIncidence.legEntries bodyEdges column scale shear leg).value.2.1.decode,
        (_root_.CurrentAFT.CurrentBinaryIncidence.legEntries bodyEdges column scale shear leg).value.2.2.decode)) = (first, (-first - second, second)) := by
  have hf : (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.AFT.BinaryArithmetic.addCounter bodyEdges leg.val).count).value = true ↔ column = bodyEdges + leg.val := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  have hs : (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.AFT.BinaryArithmetic.addCounter (_root_.AFT.BinaryArithmetic.addCounter bodyEdges leg.val).count legs).count).value = true ↔
      column = bodyEdges + leg.val + legs := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value, _root_.AFT.BinaryArithmetic.addCounter_value]
  simp only [_root_.CurrentAFT.CurrentBinaryIncidence.legEntries, _Pn5, _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.negate_value, _root_.AFT.BinaryArithmetic.readVector_value, hf, hs, _root_.AFT.BinaryArithmetic.IntegerBits.zero_value, _root_.AFT.BinaryArithmetic.IntegerBits.one_value]
open _root_.P2Mf6bd8d28 renaming h72 → _P20
end CurrentAFT.CurrentBinaryIncidence
open _root_.P2Mf6bd8d28 renaming h72 → _P20
open _root_.P2Mf6bd8d28 renaming h73 → _P21
open _root_.P2Mf6bd8d28 renaming h833 → _Pn5
end
open _root_.P2Mf6bd8d28 renaming h72 → _P20
open _root_.P2Mf6bd8d28 renaming h73 → _P21
namespace CurrentAFT.CurrentBinaryIncidence
end CurrentAFT.CurrentBinaryIncidence
namespace CurrentAFT.CurrentBinaryIncidence.legEntries
end CurrentAFT.CurrentBinaryIncidence.legEntries
namespace CurrentAFT.CurrentBinaryIncidence.pathEntry
end CurrentAFT.CurrentBinaryIncidence.pathEntry
namespace CurrentAFT.CurrentBinaryIncidence.pathEntryWork
end CurrentAFT.CurrentBinaryIncidence.pathEntryWork
section
namespace CurrentAFT.CurrentPathImpulse
open AFT
set_option maxHeartbeats 700000
theorem _root_.P2Mf6bd8d28.h102 (count column : ℕ) (vertex : Fin (count + 1)) :
    _root_.AFT.pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex =
      if column < count then (if vertex.val = column then 1 else 0) -
        (if vertex.val = column + 1 then 1 else 0) else 0 := by
  induction count generalizing column with
  | zero => simp only [_root_.AFT.pathLoad, Pi.zero_apply, Nat.not_lt_zero, if_false]
  | succ count ih =>
    cases column with
    | zero =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [_root_.AFT.pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = 0 then (1 : ℤ) else 0) = 0 := by
          funext edge
          simp [Fin.tail]
        rw [_root_.AFT.pathLoad, Fin.cons_succ, ht, _root_.AFT.pathLoad_zero]
        have he : rest.val + 1 = 1 ↔ rest = 0 := by
          constructor
          · intro h; apply Fin.ext; change rest.val = 0; omega
          · rintro rfl; rfl
        change (0 - if rest = 0 then (1 : ℤ) else 0) =
          if 0 < count + 1 then (if rest.val + 1 = 0 then 1 else 0) -
            (if rest.val + 1 = 1 then 1 else 0) else 0
        simp only [Nat.zero_lt_succ, if_true, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, he]
    | succ column =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [_root_.AFT.pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = column + 1 then (1 : ℤ) else 0) =
            (fun edge : Fin count => if edge.val = column then 1 else 0) := by
          funext edge
          simp [Fin.tail]
        rw [_root_.AFT.pathLoad, Fin.cons_succ, ht, ih]
        have hf : ((0 : Fin (count + 1)).val = column + 1) = False := by simp
        have hp : rest.succ.val = column + 1 ↔ rest.val = column := by simp
        have hn : rest.succ.val = column + 1 + 1 ↔ rest.val = column + 1 := by simp
        simp only [hf, if_false, ite_self, Nat.add_lt_add_iff_right, hp, hn]
        exact sub_zero _
open _root_.P2Mf6bd8d28 renaming h102 → _P2u
theorem _root_.P2Mf6bd8d28.h101 (count column : ℕ) (vertex : Fin (count + 1)) :
    (_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry count column vertex.val).value.decode =
      _root_.AFT.pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex := by
  rw [_P21, _P2u]
open _root_.P2Mf6bd8d28 renaming h101 → _P2t
end CurrentAFT.CurrentPathImpulse
open _root_.P2Mf6bd8d28 renaming h101 → _P2t
open _root_.P2Mf6bd8d28 renaming h102 → _P2u
end
open _root_.P2Mf6bd8d28 renaming h101 → _P2t
open _root_.P2Mf6bd8d28 renaming h102 → _P2u
namespace CurrentAFT.CurrentEmissionMetadata
end CurrentAFT.CurrentEmissionMetadata
namespace CurrentAFT.CurrentEmissionMetadata.Result
end CurrentAFT.CurrentEmissionMetadata.Result
namespace CurrentAFT.CurrentEmissionMetadata.Result.mk
end CurrentAFT.CurrentEmissionMetadata.Result.mk
namespace CurrentAFT.CurrentEmissionMetadata.current
end CurrentAFT.CurrentEmissionMetadata.current
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv
end CurrentAFT.CurrentEmissionMetadata.pointEquiv
namespace CurrentAFT.CurrentPathImpulse
end CurrentAFT.CurrentPathImpulse
section
namespace CurrentAFT.CurrentBinaryLoadColumns
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentEmissionMetadata
set_option maxHeartbeats 1200000
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
theorem _root_.P2Mf6bd8d28.h76 (security : ℕ) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    (_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots point).value = roots.get
      ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1) := by
  simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead, _root_.AFT.BinaryArithmetic.readVector_value, _P6]
open _root_.P2Mf6bd8d28 renaming h76 → _P24
theorem _root_.P2Mf6bd8d28.h74 (security column : ℕ) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security)
    (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    (_root_.CurrentAFT.CurrentBinaryLoadColumns.entry security column scale shear roots point).value.decode =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry security column (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots point := by
  rcases point with ⟨leg | body, slot⟩
  · have hv := _P20 (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column scale shear leg
    have hfirst := congrArg Prod.fst hv
    have hcompanion := congrArg (fun value => value.2.1) hv
    have hsecond := congrArg (fun value => value.2.2) hv
    try dsimp only at hfirst hcompanion hsecond
    have hp := _P2t (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column
      ((_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inl leg)).value.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    change Fin 3 at slot
    fin_cases slot <;> simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.entry, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ', _root_.AFT.BinaryArithmetic.IntegerBits.add_value,
      hfirst, hcompanion, hsecond, _root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry, _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry]
    change (_root_.CurrentAFT.CurrentBinaryIncidence.pathEntry (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column (_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inl leg)).value.val).value.decode + _ = _
    rw [hp]
    simp only [_P24, _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue]
  · have hp := _P2t (_root_.CurrentAFT.CurrentEmissionMetadata.current security).bodyEdges column
      ((_root_.CurrentAFT.CurrentBinaryLoadColumns.rootRead security roots (.inr body)).value.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    have hf : (_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value = false ↔ (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val := by
      rw [Bool.eq_false_iff]
      exact (not_congr (_root_.AFT.BinaryArithmetic.lessCounter_value _ _)).trans not_lt
    have hc : ((! (_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value) &&
        (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges).value) = true ↔
        (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val ∧ column = (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', hf, _root_.AFT.BinaryArithmetic.equalCounter_value]
    simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.entry, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, _root_.AFT.BinaryArithmetic.IntegerBits.add_value]
    rw [hp]
    simp only [_P24, _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue]
    congr 1
    by_cases h : ((! (_root_.AFT.BinaryArithmetic.lessCounter body.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers).value) &&
      (_root_.AFT.BinaryArithmetic.equalCounter column (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges).value) = true
    · rw [if_pos h, if_pos (hc.mp h), _root_.AFT.BinaryArithmetic.IntegerBits.one_value]
    · rw [if_neg h, if_neg (fun hh => h (hc.mpr hh)), _root_.AFT.BinaryArithmetic.IntegerBits.zero_value]
open _root_.P2Mf6bd8d28 renaming h74 → _P22
theorem _root_.P2Mf6bd8d28.h75 (security : ℕ) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) (roots : _root_.CurrentAFT.CurrentBinaryLoadColumns.Roots security)
    (column row : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges + 1)) :
    (((_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear roots).value.get column).get row).decode =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry security column.val (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots
        ((_root_.AFT.physicalVertexNumberingProgram (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
          (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm row) := by
  simp only [_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix, _root_.AFT.BinaryArithmetic.storeData_get, _P22, _P5]
open _root_.P2Mf6bd8d28 renaming h75 → _P23
end CurrentAFT.CurrentBinaryLoadColumns
open _root_.P2Mf6bd8d28 renaming h74 → _P22
open _root_.P2Mf6bd8d28 renaming h75 → _P23
open _root_.P2Mf6bd8d28 renaming h76 → _P24
end
open _root_.P2Mf6bd8d28 renaming h74 → _P22
open _root_.P2Mf6bd8d28 renaming h75 → _P23
open _root_.P2Mf6bd8d28 renaming h76 → _P24
namespace CurrentAFT.CurrentAffineData
end CurrentAFT.CurrentAffineData
namespace CurrentAFT.CurrentAffineData.Data
end CurrentAFT.CurrentAffineData.Data
namespace CurrentAFT.CurrentAffineData.Data.eval
end CurrentAFT.CurrentAffineData.Data.eval
namespace CurrentAFT.CurrentAffineData.Data.mk
end CurrentAFT.CurrentAffineData.Data.mk
namespace CurrentAFT.CurrentAffineData.assemble
end CurrentAFT.CurrentAffineData.assemble
namespace CurrentAFT.CurrentAffineData.assembled
end CurrentAFT.CurrentAffineData.assembled
namespace CurrentAFT.CurrentAffineData.fallback
end CurrentAFT.CurrentAffineData.fallback
namespace CurrentAFT.CurrentAffineData.scales
end CurrentAFT.CurrentAffineData.scales
namespace CurrentAFT.CurrentCoreProposal.MaterializedCore
end CurrentAFT.CurrentCoreProposal.MaterializedCore
namespace CurrentAFT.CurrentCoreProposal.MaterializedCore.core
end CurrentAFT.CurrentCoreProposal.MaterializedCore.core
namespace CurrentAFT.CurrentCoreProposal.MaterializedCore.mk
end CurrentAFT.CurrentCoreProposal.MaterializedCore.mk
namespace CurrentAFT.CurrentCoreProposal.decode
end CurrentAFT.CurrentCoreProposal.decode
namespace CurrentAFT.CurrentCoreProposal.draw
end CurrentAFT.CurrentCoreProposal.draw
namespace CurrentAFT.CurrentCoreProposal.gatherInputs
end CurrentAFT.CurrentCoreProposal.gatherInputs
namespace CurrentAFT.CurrentPublicShiftProgram
end CurrentAFT.CurrentPublicShiftProgram
section
namespace CurrentAFT.CurrentBinaryChartData
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
theorem _root_.P2Mf6bd8d28.h68 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security)
    (field : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security → ZMod (_root_.CurrentAFT.Parameters.modulus security))
    (leg : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs) :
    ((_root_.CurrentAFT.CurrentBinaryChartData.fieldArray security charts field).value.get leg).decode = (field (charts.get (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg))).val := by
  simp only [_root_.CurrentAFT.CurrentBinaryChartData.fieldArray, _root_.AFT.BinaryArithmetic.storeData_get, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value]
open _root_.P2Mf6bd8d28 renaming h68 → _P1w
end CurrentAFT.CurrentBinaryChartData
open _root_.P2Mf6bd8d28 renaming h68 → _P1w
end
open _root_.P2Mf6bd8d28 renaming h68 → _P1w
section
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h38 (security : ℕ) (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    (_root_.CurrentAFT.BinaryCoreCharge.numerator security core : ZMod (_root_.CurrentAFT.Parameters.modulus security)) = _root_.CurrentAFT.ActualPublicCharge.chargeValue security core := by
  unfold _root_.CurrentAFT.BinaryCoreCharge.numerator _root_.CurrentAFT.ActualPublicCharge.chargeValue
  simp only [Fintype.sum_sum_type, Int.cast_sum, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Finset.sum_add_distrib]
  push_cast
  ring
open _root_.P2Mf6bd8d28 renaming h38 → _P12
theorem _root_.P2Mf6bd8d28.h35 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).controls) :
    (_root_.CurrentAFT.BinaryCoreCharge.controlTerm security data index).value.decode =
      ((data.core.controls (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security index)).2.val.val : ℤ) := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.controlTerm, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value,
    _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, Equiv.symm_apply_apply]
open _root_.P2Mf6bd8d28 renaming h35 → _Pz
theorem _root_.P2Mf6bd8d28.h37 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).legs) :
    (_root_.CurrentAFT.BinaryCoreCharge.legTerm security data index).value.decode =
      ((data.core.legs (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv security index)).2.val : ℤ) + _root_.CurrentAFT.ActualPublicCharge.legShift security data.core (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv security index) := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.legTerm, _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value,
    _P2y, _root_.AFT.BinaryArithmetic.readVector_value, data.inputs_correct,
    _root_.CurrentAFT.ActualPublicCharge.legShift, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, Equiv.symm_apply_apply]
open _root_.P2Mf6bd8d28 renaming h37 → _P11
theorem _root_.P2Mf6bd8d28.h39 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (index : Fin (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors) :
    (_root_.CurrentAFT.BinaryCoreCharge.queueTerm security data index).value.decode =
      ((data.core.queueBaselines (_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv security index)).val : ℤ) := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.queueTerm, _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _root_.AFT.BinaryArithmetic.readVector_value,
    _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode, Equiv.symm_apply_apply]
open _root_.P2Mf6bd8d28 renaming h39 → _P13
theorem _root_.P2Mf6bd8d28.h40 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    (_root_.CurrentAFT.BinaryCoreCharge.total security data).value.decode = _root_.CurrentAFT.BinaryCoreCharge.numerator security data.core := by
  simp only [_root_.CurrentAFT.BinaryCoreCharge.total, _root_.AFT.BinaryArithmetic.IntegerBits.subtract_value, _root_.AFT.BinaryArithmetic.IntegerBits.add_value, _P1,
    _root_.InfoLossLARNativeSupplements.ha029c925a85a9044.CurrentAFT.CurrentPublicShiftProgram.encode_value, _Pz, _P11, _P13]
  rw [Equiv.sum_comp (_root_.CurrentAFT.CurrentProposalDimensions.controlsEquiv security) (fun index => ((data.core.controls index).2.val.val : ℤ)),
    Equiv.sum_comp (_root_.CurrentAFT.CurrentProposalDimensions.legEquiv security) (fun leg => ((data.core.legs leg).2.val : ℤ) + _root_.CurrentAFT.ActualPublicCharge.legShift security data.core leg),
    Equiv.sum_comp (_root_.CurrentAFT.CurrentProposalDimensions.queueEquiv security) (fun index => ((data.core.queueBaselines index).val : ℤ)),
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
  unfold _root_.CurrentAFT.BinaryCoreCharge.numerator
  norm_cast
open _root_.P2Mf6bd8d28 renaming h40 → _P14
theorem _root_.P2Mf6bd8d28.h36 (security : ℕ) (data : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) :
    (_root_.CurrentAFT.BinaryCoreCharge.current security data).value = true ↔ _root_.CurrentAFT.ActualPublicCharge.publicCharge security data.core := by
  have hq : 0 < _root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits := by
    rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value]
    exact (_root_.CurrentAFT.Parameters.modulus_spec security).2.pos
  have hr := _root_.AFT.BinaryArithmetic.IntegerBits.residue_value (_root_.CurrentAFT.BinaryCoreCharge.total security data).value
    (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits hq
  rw [_P14, _root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value] at hr
  change (_root_.AFT.BinaryArithmetic.normalize (_root_.AFT.BinaryArithmetic.IntegerBits.residue (_root_.CurrentAFT.BinaryCoreCharge.total security data).value
    (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits).digits).digits.isEmpty = true ↔ _
  rw [List.isEmpty_iff, _root_.AFT.BinaryArithmetic.normalize_nil_iff]
  have he : _root_.AFT.BinaryArithmetic.value (_root_.AFT.BinaryArithmetic.IntegerBits.residue (_root_.CurrentAFT.BinaryCoreCharge.total security data).value
      (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits).digits = 0 ↔
      _root_.CurrentAFT.BinaryCoreCharge.numerator security data.core % (_root_.CurrentAFT.Parameters.modulus security : ℤ) = 0 := by
    rw [_root_.CurrentAFT.PublicParameterProgram.modulus_value]
    omega
  rw [he, ← Int.dvd_iff_emod_eq_zero]
  unfold _root_.CurrentAFT.ActualPublicCharge.publicCharge
  rw [← _P12]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
open _root_.P2Mf6bd8d28 renaming h36 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mf6bd8d28 renaming h36 → _P10
end
open _root_.P2Mf6bd8d28 renaming h35 → _Pz
open _root_.P2Mf6bd8d28 renaming h36 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mf6bd8d28 renaming h36 → _P10
open _root_.P2Mf6bd8d28 renaming h37 → _P11
open _root_.P2Mf6bd8d28 renaming h38 → _P12
open _root_.P2Mf6bd8d28 renaming h39 → _P13
open _root_.P2Mf6bd8d28 renaming h40 → _P14
end CurrentAFT.BinaryCoreCharge
open _root_.P2Mf6bd8d28 renaming h35 → _Pz
open _root_.P2Mf6bd8d28 renaming h36 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mf6bd8d28 renaming h36 → _P10
open _root_.P2Mf6bd8d28 renaming h37 → _P11
open _root_.P2Mf6bd8d28 renaming h38 → _P12
open _root_.P2Mf6bd8d28 renaming h39 → _P13
open _root_.P2Mf6bd8d28 renaming h40 → _P14
end
open _root_.P2Mf6bd8d28 renaming h35 → _Pz
open _root_.P2Mf6bd8d28 renaming h36 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2Mf6bd8d28 renaming h36 → _P10
open _root_.P2Mf6bd8d28 renaming h37 → _P11
open _root_.P2Mf6bd8d28 renaming h38 → _P12
open _root_.P2Mf6bd8d28 renaming h39 → _P13
open _root_.P2Mf6bd8d28 renaming h40 → _P14
namespace AFT.BinaryArithmetic.BinaryAffineData
end AFT.BinaryArithmetic.BinaryAffineData
namespace AFT.BinaryArithmetic.BinaryAffineData.mk
end AFT.BinaryArithmetic.BinaryAffineData.mk
namespace AFT.BinaryArithmetic.BinaryCoordinateResult.decode
end AFT.BinaryArithmetic.BinaryCoordinateResult.decode
namespace AFT.BinaryArithmetic.binaryAffineAssembly
end AFT.BinaryArithmetic.binaryAffineAssembly
namespace AFT.BinaryArithmetic.binaryAffineAssemblyWork
end AFT.BinaryArithmetic.binaryAffineAssemblyWork
namespace CurrentAFT.ActualPublicCharge.legShift
end CurrentAFT.ActualPublicCharge.legShift
namespace CurrentAFT.BinaryCoreCharge
end CurrentAFT.BinaryCoreCharge
namespace CurrentAFT.BinaryCoreCharge.controlTerm
end CurrentAFT.BinaryCoreCharge.controlTerm
namespace CurrentAFT.BinaryCoreCharge.legTerm
end CurrentAFT.BinaryCoreCharge.legTerm
namespace CurrentAFT.BinaryCoreCharge.queueTerm
end CurrentAFT.BinaryCoreCharge.queueTerm
namespace CurrentAFT.BinaryCoreCharge.total
end CurrentAFT.BinaryCoreCharge.total
namespace CurrentAFT.CurrentBinaryOffsetLoad
end CurrentAFT.CurrentBinaryOffsetLoad
namespace CurrentAFT.CurrentBinaryOffsetLoad.entry
end CurrentAFT.CurrentBinaryOffsetLoad.entry
namespace CurrentAFT.CurrentBinaryOffsetLoad.entry.match_1
end CurrentAFT.CurrentBinaryOffsetLoad.entry.match_1
namespace CurrentAFT.CurrentBinaryOffsetLoad.load
end CurrentAFT.CurrentBinaryOffsetLoad.load
namespace CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad
end CurrentAFT.CurrentBinaryOffsetLoad.physicalLoad
section
namespace CurrentAFT.CurrentBinaryAffinePrimitives
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
theorem _root_.P2Mf6bd8d28.h67 (security : ℕ) (row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection security).value.get row).decode = _root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.Parameters.modulus security) row := by
  have h : (_root_.AFT.BinaryArithmetic.lessCounter row.val (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors).value = true ↔ row.val < _root_.CurrentAFT.Parameters.modulus security := by
    rw [_root_.AFT.BinaryArithmetic.lessCounter_value, (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).1]
  simp only [_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.injectionColumn]
  by_cases ht : (_root_.AFT.BinaryArithmetic.lessCounter row.val (_root_.CurrentAFT.CurrentProposalDimensions.current security).colors).value = true
  · rw [if_pos ht, if_pos (h.mp ht), _root_.AFT.BinaryArithmetic.IntegerBits.one_value]
  · rw [if_neg ht, if_neg (fun hh => ht (h.mpr hh)), _root_.AFT.BinaryArithmetic.IntegerBits.zero_value]
open _root_.P2Mf6bd8d28 renaming h67 → _P1v
theorem _root_.P2Mf6bd8d28.h66 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value.get row) =
      core.core.endpointPermutation (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
  simp only [_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation, _root_.AFT.BinaryArithmetic.storeData_get, _root_.AFT.BinaryArithmetic.readVector_value, _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore.core, _root_.CurrentAFT.CurrentCoreProposal.decode,
    Equiv.permCongr_apply]
  apply Fin.ext
  change (core.endpoints.forward.get (row.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.1)).val =
    (core.endpoints.forward.get ((_root_.CurrentAFT.CurrentProposalDimensions.endpointEquiv security).symm (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row))).val
  have hi : row.cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.1 =
      (_root_.CurrentAFT.CurrentProposalDimensions.endpointEquiv security).symm (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
    apply Fin.ext
    rfl
  rw [hi]
open _root_.P2Mf6bd8d28 renaming h66 → _P1u
end CurrentAFT.CurrentBinaryAffinePrimitives
open _root_.P2Mf6bd8d28 renaming h66 → _P1u
open _root_.P2Mf6bd8d28 renaming h67 → _P1v
end
open _root_.P2Mf6bd8d28 renaming h66 → _P1u
open _root_.P2Mf6bd8d28 renaming h67 → _P1v
namespace CurrentAFT.BinaryProposalGuard
end CurrentAFT.BinaryProposalGuard
namespace CurrentAFT.BinaryProposalGuard.allFin
end CurrentAFT.BinaryProposalGuard.allFin
namespace CurrentAFT.BinaryProposalGuard.allFin.match_1
end CurrentAFT.BinaryProposalGuard.allFin.match_1
namespace CurrentAFT.BinaryProposalGuard.lowerCheck
end CurrentAFT.BinaryProposalGuard.lowerCheck
namespace CurrentAFT.BinaryProposalGuard.primary
end CurrentAFT.BinaryProposalGuard.primary
namespace CurrentAFT.BinaryProposalGuard.threshold
end CurrentAFT.BinaryProposalGuard.threshold
namespace CurrentAFT.BinaryProposalGuard.thresholdWork
end CurrentAFT.BinaryProposalGuard.thresholdWork
namespace CurrentAFT.BinaryProposalGuard.uniformTable
end CurrentAFT.BinaryProposalGuard.uniformTable
namespace CurrentAFT.CurrentBinaryAffinePrimitives
end CurrentAFT.CurrentBinaryAffinePrimitives
namespace CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation
end CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation
namespace CurrentAFT.CurrentBinaryAffinePrimitives.injection
end CurrentAFT.CurrentBinaryAffinePrimitives.injection
namespace CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad
end CurrentAFT.CurrentBinaryAffinePrimitives.permuteLoad
section
namespace CurrentAFT.CurrentBinaryAffineGuard
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentBinaryChartData
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
theorem _root_.P2Mf6bd8d28.h65 (security : ℕ) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentBinaryAffineGuard.scale security charts leg).value = true ↔ (charts.get leg).2.2.1 ≠ 0 := by
  have he : (_root_.AFT.BinaryArithmetic.equalCounter (charts.get leg).2.2.1.val 0).value = true ↔ (charts.get leg).2.2.1 = 0 := by
    rw [_root_.AFT.BinaryArithmetic.equalCounter_value, ZMod.val_eq_zero]
  simp only [_root_.CurrentAFT.CurrentBinaryAffineGuard.scale, _root_.AFT.BinaryArithmetic.readVector_value, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr he
open _root_.P2Mf6bd8d28 renaming h65 → _P1t
theorem _root_.P2Mf6bd8d28.h64 (security : ℕ) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (charts : _root_.CurrentAFT.CurrentBinaryChartData.Charts security) :
    (_root_.CurrentAFT.CurrentBinaryAffineGuard.current security core charts).value = true ↔ _root_.CurrentAFT.CurrentAffineData.Valid security core.core charts.get := by
  simp only [_root_.CurrentAFT.CurrentBinaryAffineGuard.current, Bool.and_eq_true, _P10,
    _root_.CurrentAFT.BinaryProposalGuard.allFin_value, _P1t, _root_.CurrentAFT.CurrentAffineData.Valid]
open _root_.P2Mf6bd8d28 renaming h64 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2Mf6bd8d28 renaming h64 → _P1s
end CurrentAFT.CurrentBinaryAffineGuard
open _root_.P2Mf6bd8d28 renaming h64 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2Mf6bd8d28 renaming h64 → _P1s
open _root_.P2Mf6bd8d28 renaming h65 → _P1t
end
open _root_.P2Mf6bd8d28 renaming h64 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2Mf6bd8d28 renaming h64 → _P1s
open _root_.P2Mf6bd8d28 renaming h65 → _P1t
namespace CurrentAFT.CurrentAffineGeometry
end CurrentAFT.CurrentAffineGeometry
namespace CurrentAFT.CurrentAffineGeometry.relabeling
end CurrentAFT.CurrentAffineGeometry.relabeling
section
namespace CurrentAFT.CurrentAffineLoad
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
theorem _root_.P2Mf6bd8d28.h61 (security : ℕ) (input : (Fin (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) → ℤ) × ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentAffineLoad.packSource security input) = input := by
  simp [_root_.CurrentAFT.CurrentAffineLoad.splitSource, _root_.CurrentAFT.CurrentAffineLoad.packSource]
open _root_.P2Mf6bd8d28 renaming h61 → _P1p
theorem _root_.P2Mf6bd8d28.h60 (security : ℕ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.packSource security (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input) = input := by
  funext index
  obtain ⟨edge | point, rfl⟩ := (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).surjective index
  · simp [_root_.CurrentAFT.CurrentAffineLoad.packSource, _root_.CurrentAFT.CurrentAffineLoad.splitSource]
  · cases point
    simp [_root_.CurrentAFT.CurrentAffineLoad.packSource, _root_.CurrentAFT.CurrentAffineLoad.splitSource]
open _root_.P2Mf6bd8d28 renaming h60 → _P1o
theorem _root_.P2Mf6bd8d28.h58 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    (_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input =
      _root_.CurrentAFT.CurrentAffineLoad.packSource security
        (_root_.CurrentAFT.AffineRealization.linearPart (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security)
          (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
          (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input)) := by
  change (Matrix.reindex _ _ _).mulVecLin input = _
  rw [Matrix.mulVecLin_reindex]
  change (fun index => (_root_.CurrentAFT.AffineRealization.matrix (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
    (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
      (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear).mulVec (input ∘ _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security)
        ((_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).symm index)) = _
  have hinput : input ∘ _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security =
      Sum.elim (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).1 (fun _ : Unit => (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).2) := by
    funext index
    rcases index with edge | point
    · rfl
    · cases point; rfl
  rw [hinput, _Py]
  rfl
open _root_.P2Mf6bd8d28 renaming h58 → _P1m
theorem _root_.P2Mf6bd8d28.h59 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      _root_.CurrentAFT.AffineRealization.linearPart (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
        (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input) := by
  rw [_P1m, _P1p]
open _root_.P2Mf6bd8d28 renaming h59 → _P1n
end
open _root_.P2Mf6bd8d28 renaming h58 → _P1m
open _root_.P2Mf6bd8d28 renaming h59 → _P1n
open _root_.P2Mf6bd8d28 renaming h60 → _P1o
open _root_.P2Mf6bd8d28 renaming h61 → _P1p
end CurrentAFT.CurrentAffineLoad
open _root_.P2Mf6bd8d28 renaming h58 → _P1m
open _root_.P2Mf6bd8d28 renaming h59 → _P1n
open _root_.P2Mf6bd8d28 renaming h60 → _P1o
open _root_.P2Mf6bd8d28 renaming h61 → _P1p
end
open _root_.P2Mf6bd8d28 renaming h58 → _P1m
open _root_.P2Mf6bd8d28 renaming h59 → _P1n
open _root_.P2Mf6bd8d28 renaming h60 → _P1o
open _root_.P2Mf6bd8d28 renaming h61 → _P1p
section
namespace CurrentAFT.LobsterAffineLoad
open AFT PublicCharge LobsterCoordinates LobsterMixerMatrix AffineBaseline AffineRealization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
theorem _root_.P2Mf6bd8d28.h113 (bodyEdges legs : ℕ) (scale shear : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) :
    _root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input) =
      ((_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).1,
        (fun leg => scale leg * (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
          shear leg * (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.2 leg,
         (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.2)) := by
  apply Prod.ext
  · funext vertex
    change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inl vertex)) = _
    rw [_P3a, _P39]
    rfl
  · apply Prod.ext
    · funext leg
      change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inr (.inl leg))) = _
      rw [_P3a, _P39]
      rfl
    · funext leg
      change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inr (.inr leg))) = _
      rw [_P3a, _P39]
      rfl
open _root_.P2Mf6bd8d28 renaming h113 → _P35
theorem _root_.P2Mf6bd8d28.h114 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin (bodyEdges + 1)) :
    _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex))) =
      if vertex ∈ Finset.univ.map queues then 1 else 0 := by
  have hequal : relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex)) ∈
      Finset.univ.map (_root_.CurrentAFT.AffineRealization.queueEmbedding bodyEdges legs modulus queues relabeling) ↔
      vertex ∈ Finset.univ.map queues := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨point, heq⟩
      exact ⟨point, Sum.inl.inj ((_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).injective (relabeling.injective heq))⟩
    · rintro ⟨point, heq⟩
      exact ⟨point, congrArg (fun vertex => relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex))) heq⟩
  simp only [_root_.CurrentAFT.AffineRealization.queueColumn, hequal]
open _root_.P2Mf6bd8d28 renaming h114 → _P36
theorem _root_.P2Mf6bd8d28.h115 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin legs ⊕ Fin legs) :
    _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inr vertex))) = 0 := by
  have hnot : relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inr vertex)) ∉
      Finset.univ.map (_root_.CurrentAFT.AffineRealization.queueEmbedding bodyEdges legs modulus queues relabeling) := by
    intro hmem
    obtain ⟨point, _, heq⟩ := Finset.mem_map.mp hmem
    have h := (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).injective (relabeling.injective heq)
    cases h
  exact if_neg hnot
open _root_.P2Mf6bd8d28 renaming h115 → _P37
end
open _root_.P2Mf6bd8d28 renaming h113 → _P35
open _root_.P2Mf6bd8d28 renaming h114 → _P36
open _root_.P2Mf6bd8d28 renaming h115 → _P37
end CurrentAFT.LobsterAffineLoad
open _root_.P2Mf6bd8d28 renaming h113 → _P35
open _root_.P2Mf6bd8d28 renaming h114 → _P36
open _root_.P2Mf6bd8d28 renaming h115 → _P37
end
open _root_.P2Mf6bd8d28 renaming h113 → _P35
open _root_.P2Mf6bd8d28 renaming h114 → _P36
open _root_.P2Mf6bd8d28 renaming h115 → _P37
namespace CurrentAFT.ActualGaussianAccuracy
end CurrentAFT.ActualGaussianAccuracy
namespace CurrentAFT.ActualGaussianAccuracy.five_inversePower
end CurrentAFT.ActualGaussianAccuracy.five_inversePower
section
namespace CurrentAFT.NumericalAffineTransport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport CurrentZeroFiber
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.NumericalAffineTransport.modulusNeZero
theorem _root_.P2Mf6bd8d28.h119 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (result : _root_.CurrentAFT.NumericalAffineTransport.PublicResult security) :
    IsUnit ((_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout result).matrix.map
      (Int.castRingHom (ZMod (_root_.CurrentAFT.Parameters.modulus security)))) :=
  (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout result).invertible
open _root_.P2Mf6bd8d28 renaming h119 → _P3b
end
open _root_.P2Mf6bd8d28 renaming h119 → _P3b
end CurrentAFT.NumericalAffineTransport
open _root_.P2Mf6bd8d28 renaming h119 → _P3b
end
open _root_.P2Mf6bd8d28 renaming h119 → _P3b
namespace CurrentAFT.CurrentAffineLoad
end CurrentAFT.CurrentAffineLoad
namespace CurrentAFT.CurrentAffineLoad.packSource
end CurrentAFT.CurrentAffineLoad.packSource
namespace CurrentAFT.CurrentAffineLoad.splitSource
end CurrentAFT.CurrentAffineLoad.splitSource
section
namespace CurrentAFT.CurrentAffineEmissionBridge
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean CurrentAffineGeometry CurrentAffineLoad
  LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
theorem _root_.P2Mf6bd8d28.h55 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear input := by
  unfold _root_.CurrentAFT.CurrentAffineLoad.rounding
  rw [_P1n, _Px]
  rfl
open _root_.P2Mf6bd8d28 renaming h55 → _P1j
theorem _root_.P2Mf6bd8d28.h56 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (column : Fin (_root_.CurrentAFT.Parameters.dimension security)) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security (fun row => _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear row column) =
      _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear (Pi.single column 1) := by
  have h := _P1j security layout core scale shear (Pi.single column 1)
  have he : (_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec (Pi.single column 1) =
      fun row => _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear row column := by
    funext row
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rwa [he] at h
open _root_.P2Mf6bd8d28 renaming h56 → _P1k
theorem _root_.P2Mf6bd8d28.h54 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    _root_.AFT.totalCharge (_root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)) = (_root_.CurrentAFT.Parameters.modulus security : ℤ) := by
  exact _root_.AFT.totalCharge_injectionColumn _ _ (_root_.CurrentAFT.AffineRealization.queue_modulus_le
    (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout))
open _root_.P2Mf6bd8d28 renaming h54 → _P1i
 theorem _root_.P2Mf6bd8d28.h53 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (modulus : List Bool) (hmodulus : _root_.AFT.BinaryArithmetic.value modulus = _root_.CurrentAFT.Parameters.modulus security)
    (injection bitLoad : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security + 1))
    (hinjection : ∀ vertex, (injection.get vertex).decode = _root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security) vertex)
    (target : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (hload : ∀ vertex, (bitLoad.get vertex).decode = _root_.CurrentAFT.CurrentAffineLoad.rounding security target (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security vertex)) :
    _root_.CurrentAFT.CurrentAffineLoad.packSource security
      ((fun edge => ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).edges.get edge).decode),
        (_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).charge.decode) = target := by
  let decodedInjection := injection.map _root_.AFT.BinaryArithmetic.IntegerBits.decode
  let decodedLoad := bitLoad.map _root_.AFT.BinaryArithmetic.IntegerBits.decode
  have hi : decodedInjection.get = _root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) := by
    funext vertex
    simpa only [decodedInjection, Vector.get_map] using hinjection vertex
  have hm : _root_.AFT.totalCharge decodedInjection.get = (_root_.CurrentAFT.Parameters.modulus security : ℤ) := by
    rw [hi]
    exact _P1i security layout
  have hl : decodedLoad.get = _root_.AFT.roundingLoad (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) decodedInjection.get (_root_.CurrentAFT.CurrentAffineLoad.splitSource security target) := by
    funext vertex
    rw [hi]
    simpa only [decodedLoad, Vector.get_map, _root_.CurrentAFT.CurrentAffineLoad.rounding, Equiv.symm_apply_apply] using hload vertex
  have hd : (_root_.CurrentAFT.Parameters.modulus security : ℤ) ∣ _root_.AFT.totalCharge decodedLoad.get := by
    exact (_root_.AFT.rounding_image_lattice _ _ _ hm _).mp ⟨_root_.CurrentAFT.CurrentAffineLoad.splitSource security target, hl.symm⟩
  have hbitdiv : (_root_.AFT.BinaryArithmetic.value modulus : ℤ) ∣ ∑ vertex, (bitLoad.get vertex).decode := by
    simpa only [hmodulus, decodedLoad, _root_.AFT.totalCharge, Vector.get_map] using hd
  have hb := _P7 (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad
    (by rw [hmodulus]; exact (_root_.CurrentAFT.Parameters.modulus_spec security).2.pos) hbitdiv
  have hq : (_root_.CurrentAFT.Parameters.modulus security : ℤ) ≠ 0 := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.ne_zero
  have he : ((_root_.AFT.roundingInverseProgram (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) decodedInjection decodedLoad).value.1.get,
      (_root_.AFT.roundingInverseProgram (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) decodedInjection decodedLoad).value.2) =
        _root_.CurrentAFT.CurrentAffineLoad.splitSource security target := by
    apply _root_.AFT.roundingLoad_injective (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) hq decodedInjection.get hm
    rw [_Po _ _ _ _ hm hd, hl]
  rw [hmodulus] at hb
  have hresult : ((fun edge => ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).edges.get edge).decode),
      (_root_.AFT.BinaryArithmetic.binaryRoundingInverse (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) modulus injection bitLoad).charge.decode) = _root_.CurrentAFT.CurrentAffineLoad.splitSource security target := by
    apply (Prod.ext (funext hb.2) hb.1).trans he
  rw [hresult, _P1o]
open _root_.P2Mf6bd8d28 renaming h53 → _P1h
end
open _root_.P2Mf6bd8d28 renaming h53 → _P1h
open _root_.P2Mf6bd8d28 renaming h54 → _P1i
open _root_.P2Mf6bd8d28 renaming h55 → _P1j
open _root_.P2Mf6bd8d28 renaming h56 → _P1k
end CurrentAFT.CurrentAffineEmissionBridge
open _root_.P2Mf6bd8d28 renaming h53 → _P1h
open _root_.P2Mf6bd8d28 renaming h54 → _P1i
open _root_.P2Mf6bd8d28 renaming h55 → _P1j
open _root_.P2Mf6bd8d28 renaming h56 → _P1k
end
open _root_.P2Mf6bd8d28 renaming h53 → _P1h
open _root_.P2Mf6bd8d28 renaming h54 → _P1i
open _root_.P2Mf6bd8d28 renaming h55 → _P1j
open _root_.P2Mf6bd8d28 renaming h56 → _P1k
namespace CurrentAFT.CurrentAffineData.Valid
end CurrentAFT.CurrentAffineData.Valid
namespace CurrentAFT.CurrentAffineEmissionBridge
end CurrentAFT.CurrentAffineEmissionBridge
namespace CurrentAFT.CurrentAffineLoad.rounding
end CurrentAFT.CurrentAffineLoad.rounding
namespace CurrentAFT.CurrentBinaryAffineGuard
end CurrentAFT.CurrentBinaryAffineGuard
namespace CurrentAFT.CurrentBinaryAffineGuard.current
end CurrentAFT.CurrentBinaryAffineGuard.current
namespace CurrentAFT.CurrentBinaryAffineGuard.scale
end CurrentAFT.CurrentBinaryAffineGuard.scale
namespace CurrentAFT.CurrentMaterializedCompletion
end CurrentAFT.CurrentMaterializedCompletion
namespace CurrentAFT.CurrentMaterializedCompletion.Result
end CurrentAFT.CurrentMaterializedCompletion.Result
namespace CurrentAFT.CurrentMaterializedCompletion.Result.mk
end CurrentAFT.CurrentMaterializedCompletion.Result.mk
namespace CurrentAFT.CurrentMaterializedCompletion.complete
end CurrentAFT.CurrentMaterializedCompletion.complete
namespace CurrentAFT.CurrentMaterializedCompletion.workPolynomial
end CurrentAFT.CurrentMaterializedCompletion.workPolynomial
section
namespace CurrentAFT.CurrentBinaryAffineEmitter
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryAffinePrimitives CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
theorem _root_.P2Mf6bd8d28.h62 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security)
    (h : ¬_root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security).columns ∧
      (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security).offset := by
  have ht : ¬(_root_.CurrentAFT.CurrentBinaryAffineGuard.current security sample.core sample.charts).value = true :=
    fun ht => h ((_P1s security sample.core sample.charts).mp ht)
  simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit, if_neg ht, and_self]
open _root_.P2Mf6bd8d28 renaming h62 → _P1q
theorem _root_.P2Mf6bd8d28.h63 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security)
    (h : _root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample).columns ∧
      (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample).offset := by
  have ht := (_P1s security sample.core sample.charts).mpr h
  simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit, if_pos ht, and_self]
open _root_.P2Mf6bd8d28 renaming h63 → _P1r
end
open _root_.P2Mf6bd8d28 renaming h62 → _P1q
open _root_.P2Mf6bd8d28 renaming h63 → _P1r
end CurrentAFT.CurrentBinaryAffineEmitter
open _root_.P2Mf6bd8d28 renaming h62 → _P1q
open _root_.P2Mf6bd8d28 renaming h63 → _P1r
end
open _root_.P2Mf6bd8d28 renaming h62 → _P1q
open _root_.P2Mf6bd8d28 renaming h63 → _P1r
namespace CurrentAFT.CurrentBinaryAffineEmitter
end CurrentAFT.CurrentBinaryAffineEmitter
namespace CurrentAFT.CurrentBinaryAffineEmitter.emit
end CurrentAFT.CurrentBinaryAffineEmitter.emit
namespace CurrentAFT.CurrentBinaryAffineEmitter.emit.match_1
end CurrentAFT.CurrentBinaryAffineEmitter.emit.match_1
section
namespace CurrentAFT.CurrentBinaryFallbackSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentBinaryAffineEmitter
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
private theorem _root_.P2Mf6bd8d28.h832 (test : Prop) [Decidable test] : (if test then _root_.AFT.BinaryArithmetic.IntegerBits.one else _root_.AFT.BinaryArithmetic.IntegerBits.zero).decode = if test then 1 else 0 := by
  split_ifs <;> rfl
open _root_.P2Mf6bd8d28 renaming h832 → _Pn4
theorem _root_.P2Mf6bd8d28.h70 (security : ℕ) (column : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn security column).value = Pi.single (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column) 1 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).surjective row
  · have he : (_root_.AFT.BinaryArithmetic.equalCounter edge.val column.val).value = true ↔
        _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl edge) = _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column := by
      rw [_root_.AFT.BinaryArithmetic.equalCounter_value, Fin.ext_iff]
      change edge.val = column.val ↔ edge.val = column.val
      rfl
    simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate, _root_.CurrentAFT.CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inl,
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn, _root_.AFT.BinaryArithmetic.storeData_get, Fin.val_cast, _Pn4, Pi.single_apply, he]
  · cases point
    have he : (_root_.AFT.BinaryArithmetic.equalCounter column.val (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges).value = true ↔
        _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inr ()) = _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column := by
      rw [_root_.AFT.BinaryArithmetic.equalCounter_value, Fin.ext_iff]
      change column.val = (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges ↔ _root_.CurrentAFT.CurrentAffineGeometry.edgeCount security = column.val
      rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1]
      exact eq_comm
    simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate, _root_.CurrentAFT.CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inr,
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn, _Pn4, Pi.single_apply, he]
open _root_.P2Mf6bd8d28 renaming h70 → _P1y
theorem _root_.P2Mf6bd8d28.h71 (security : ℕ) : _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallback security) = 1 := by
  funext row column
  change _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security ((_root_.AFT.BinaryArithmetic.storeData _ (_root_.CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn security)).value.get ((_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security).symm column)) row = _
  rw [_root_.AFT.BinaryArithmetic.storeData_get, _P1y, Equiv.apply_symm_apply]
  simp [Pi.single_apply, Matrix.one_apply]
open _root_.P2Mf6bd8d28 renaming h71 → _P1z
end CurrentAFT.CurrentBinaryFallbackSemantic
open _root_.P2Mf6bd8d28 renaming h70 → _P1y
open _root_.P2Mf6bd8d28 renaming h71 → _P1z
open _root_.P2Mf6bd8d28 renaming h832 → _Pn4
end
open _root_.P2Mf6bd8d28 renaming h70 → _P1y
open _root_.P2Mf6bd8d28 renaming h71 → _P1z
namespace CurrentAFT.AffineBaseline.numberedOffset
end CurrentAFT.AffineBaseline.numberedOffset
namespace CurrentAFT.LobsterAffineLoad
end CurrentAFT.LobsterAffineLoad
namespace CurrentAFT.LobsterAffineLoad.primary
end CurrentAFT.LobsterAffineLoad.primary
section
namespace CurrentAFT.CurrentLinearPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates LobsterMixerMatrix PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
theorem _root_.P2Mf6bd8d28.h99 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear input
        (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.LobsterIncidence.load (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
        ((_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security input).1, (_root_.CurrentAFT.CurrentLinearPhysicalLoad.primary security scale shear input, (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security input).2.2))
        (Sum.map (_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security) id vertex) +
      (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).2 * _root_.CurrentAFT.AffineRealization.queueColumn (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
        (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core)
        (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex)) := by
  have hi : (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm
      (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex) := by
    apply (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, _P1l]
  unfold _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad
  rw [hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, _P38,
    Equiv.symm_apply_apply]
  rw [_P35]
  simp only [_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply]
  rfl
open _root_.P2Mf6bd8d28 renaming h99 → _P2r
theorem _root_.P2Mf6bd8d28.h100 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (point : Sigma (_root_.CurrentAFT.ActualBlockFock.Slots security)) :
    _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout core scale shear input
      (core.endpointPermutation.symm (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security point)) =
      _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical security layout core scale shear input point := by
  have hp : _root_.CurrentAFT.CurrentPhysicalNumbering.numbering security point =
      _root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout (_root_.CurrentAFT.PublicEndpointPlacement.toAssembly security layout point) := by
    change _root_.CurrentAFT.PublicCoefficientOutput.flatten security point =
      _root_.CurrentAFT.PublicCoefficientOutput.flatten security (_root_.CurrentAFT.PublicEndpointPlacement.toPhysical security layout (_root_.CurrentAFT.PublicEndpointPlacement.toAssembly security layout point))
    rw [_root_.CurrentAFT.PublicEndpointPlacement.toPhysical_toAssembly]
  rw [hp, _P2r]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, Fin.cases, Fin.induction, Fin.induction.go, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, _P37,
        _P36, _root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.PublicCharge.attachmentIncrement,
        _root_.CurrentAFT.CurrentAffineGeometry.attachments, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition, _root_.CurrentAFT.CurrentAffineGeometry.queues, _root_.CurrentAFT.ActualPublicCharge.queuePosition, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentLinearPhysicalLoad.path, _root_.CurrentAFT.CurrentAffineGeometry.placement]
  · simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, _P36,
      _root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.CurrentAffineGeometry.attachments, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition,
      _root_.CurrentAFT.CurrentAffineGeometry.queues, _root_.CurrentAFT.ActualPublicCharge.queuePosition, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentLinearPhysicalLoad.path, _root_.CurrentAFT.CurrentAffineGeometry.placement]
  · simp [_root_.CurrentAFT.PublicEndpointPlacement.toAssembly, _root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering, _P36,
      _root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.CurrentAffineGeometry.attachments, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition,
      _root_.CurrentAFT.CurrentAffineGeometry.queues, _root_.CurrentAFT.ActualPublicCharge.queuePosition, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentLinearPhysicalLoad.path, _root_.CurrentAFT.CurrentAffineGeometry.placement]
open _root_.P2Mf6bd8d28 renaming h100 → _P2s
end
open _root_.P2Mf6bd8d28 renaming h99 → _P2r
open _root_.P2Mf6bd8d28 renaming h100 → _P2s
end CurrentAFT.CurrentLinearPhysicalLoad
open _root_.P2Mf6bd8d28 renaming h99 → _P2r
open _root_.P2Mf6bd8d28 renaming h100 → _P2s
end
open _root_.P2Mf6bd8d28 renaming h99 → _P2r
open _root_.P2Mf6bd8d28 renaming h100 → _P2s
namespace CurrentAFT.CurrentAffineGeometry.attachments
end CurrentAFT.CurrentAffineGeometry.attachments
namespace CurrentAFT.CurrentAffineGeometry.naturalNumbering
end CurrentAFT.CurrentAffineGeometry.naturalNumbering
namespace CurrentAFT.CurrentAffineGeometry.placement
end CurrentAFT.CurrentAffineGeometry.placement
namespace CurrentAFT.CurrentAffineGeometry.queues
end CurrentAFT.CurrentAffineGeometry.queues
namespace CurrentAFT.CurrentLinearPhysicalLoad
end CurrentAFT.CurrentLinearPhysicalLoad
namespace CurrentAFT.CurrentLinearPhysicalLoad.path
end CurrentAFT.CurrentLinearPhysicalLoad.path
namespace CurrentAFT.CurrentLinearPhysicalLoad.physical
end CurrentAFT.CurrentLinearPhysicalLoad.physical
namespace CurrentAFT.CurrentLinearPhysicalLoad.physical.match_1
end CurrentAFT.CurrentLinearPhysicalLoad.physical.match_1
section
namespace CurrentAFT.CurrentBinaryLoadSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata
open CurrentCoreProposal (MaterializedCore)
open
  CurrentLinearPhysicalLoad CurrentAffineGeometry CurrentAffineLoad
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current
theorem _root_.P2Mf6bd8d28.h85 (security : ℕ) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    (_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1 =
      _root_.CurrentAFT.CurrentEmissionRootOrder.rootNumbering security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv security point) := by
  rcases point with leg | body
  · apply Fin.ext
    rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    all_goals
      apply Fin.ext
      simp only [_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv, Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply,
        ← he, Equiv.symm_apply_apply]
    · change (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)+body.val=_root_.CurrentAFT.Parameters.legCount security+center.val
      have hv := congrArg Fin.val he
      change center.val=body.val at hv
      rw [show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1, hv]
    · change (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)+body.val=_root_.CurrentAFT.Parameters.legCount security+(_root_.CurrentAFT.ActualBlockFock.centerCount security+queue.val)
      have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security+queue.val=body.val at hv
      rw [show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1, hv]
open _root_.P2Mf6bd8d28 renaming h85 → _P2d
theorem _root_.P2Mf6bd8d28.h78 (security : ℕ) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    _root_.CurrentAFT.CurrentEmissionRootOrder.rootToRole security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv security point) = _root_.CurrentAFT.CurrentBinaryBaselines.role security point := by
  rcases point with leg | body
  · rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    all_goals simp only [_root_.CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv, _root_.CurrentAFT.CurrentBinaryBaselines.role, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.trans_apply, ← he, Equiv.symm_apply_apply]; rfl
open _root_.P2Mf6bd8d28 renaming h78 → _P26
theorem _root_.P2Mf6bd8d28.h86 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    ((_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value.get
      ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)).val =
      (core.core.bodyPermutation.symm (layout.layout (_root_.CurrentAFT.CurrentBinaryBaselines.role security point))).val := by
  have h := _P2n security layout core
    ((_root_.AFT.blockNumbering (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest point).cast (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.1)
  rw [_P2d, Equiv.symm_apply_apply, _P26] at h
  have hv := congrArg (fun vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security => vertex.val) h
  simpa only [_root_.CurrentAFT.CurrentProposalDimensions.bodyEquiv, finCongr_apply, Fin.val_cast, _P2d] using hv
open _root_.P2Mf6bd8d28 renaming h86 → _P2e
theorem _root_.P2Mf6bd8d28.h77 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (index : Fin (_root_.CurrentAFT.Parameters.dimension security)) :
    (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) index = if index.val=column.val then 1 else 0 := by
  simp only [_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput, Pi.single_apply, Fin.ext_iff]
  rfl
open _root_.P2Mf6bd8d28 renaming h77 → _P25
theorem _root_.P2Mf6bd8d28.h79 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).1 =
      fun edge => if edge.val=column.val then 1 else 0 := by
  funext edge
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
    (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inl edge)))) = _
  rw [_P25]
  rfl
open _root_.P2Mf6bd8d28 renaming h79 → _P27
theorem _root_.P2Mf6bd8d28.h80 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2.1 leg =
      if _root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security+leg.val=column.val then 1 else 0 := by
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
    (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inl leg))))) = _
  rw [_P25]
  rfl
open _root_.P2Mf6bd8d28 renaming h80 → _P28
theorem _root_.P2Mf6bd8d28.h87 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2.2 leg =
      if _root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security+(_root_.CurrentAFT.Parameters.legCount security+leg.val)=column.val then 1 else 0 := by
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
    (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inr leg))))) = _
  rw [_P25]
  rfl
open _root_.P2Mf6bd8d28 renaming h87 → _P2f
theorem _root_.P2Mf6bd8d28.h84 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) :
    (_root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2 =
      if column.val=(_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges then 1 else 0 := by
  change (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inr ())) = _
  rw [_P25]
  change (if _root_.CurrentAFT.CurrentAffineGeometry.edgeCount security=column.val then (1 : ℤ) else 0)=_
  simp only [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1, eq_comm]
open _root_.P2Mf6bd8d28 renaming h84 → _P2c
theorem _root_.P2Mf6bd8d28.h83 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1))
    (scale shear : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) → ℤ) (leg : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) :
    _root_.CurrentAFT.CurrentLinearPhysicalLoad.primary security (fun i => scale ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm i))
      (fun i => shear ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm i))
      (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg) =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry security column.val scale shear leg := by
  rw [_root_.CurrentAFT.CurrentLinearPhysicalLoad.primary, _P28, _P2f]
  simp only [Equiv.symm_apply_apply]
  have hleg : (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  unfold _root_.CurrentAFT.CurrentBinaryLoadColumns.primaryEntry
  simp only [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1, show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
  simp only [_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges, add_comm (_root_.CurrentAFT.Parameters.legCount security) leg.val, ← add_assoc,
    eq_comm, mul_ite, mul_one, mul_zero]
open _root_.P2Mf6bd8d28 renaming h83 → _P2b
theorem _root_.P2Mf6bd8d28.h88 (security : ℕ) (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (leg : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security)) :
    (_root_.CurrentAFT.CurrentLinearPhysicalLoad.sourceEdges security (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)).2.2 (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg) =
      _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry security column.val leg := by
  rw [_P2f]
  unfold _root_.CurrentAFT.CurrentBinaryLoadColumns.secondEntry
  simp only [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1, show _root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security=_root_.CurrentAFT.Parameters.legCount security from
    (_root_.CurrentAFT.CurrentProposalDimensions.current_values security).2.1]
  have hleg : (_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  simp only [_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges, add_comm (_root_.CurrentAFT.Parameters.legCount security) leg.val, ← add_assoc, eq_comm]
open _root_.P2Mf6bd8d28 renaming h88 → _P2g
theorem _root_.P2Mf6bd8d28.h82 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (point : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) ⊕ Fin (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest) :
    _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue security column.val (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value point =
      _root_.CurrentAFT.CurrentLinearPhysicalLoad.path security core.core (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
        (layout.layout (_root_.CurrentAFT.CurrentBinaryBaselines.role security point)) := by
  unfold _root_.CurrentAFT.CurrentLinearPhysicalLoad.path _root_.CurrentAFT.CurrentBinaryLoadColumns.pathValue
  rw [_P27, _P2u, _P2u]
  simp only [Fin.val_cast]
  simp only [_P2e, (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).1]
  rfl
open _root_.P2Mf6bd8d28 renaming h82 → _P2a
theorem _root_.P2Mf6bd8d28.h81 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security)
    (column : Fin ((_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges+1)) (scale shear : Fin (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) → ℤ) (point : _root_.CurrentAFT.CurrentBinaryLoadColumns.Point security) :
    _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry security column.val scale shear (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value point =
      _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
        (fun leg => scale ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg))
        (fun leg => shear ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg))
        (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column)
        (core.core.endpointPermutation.symm (_root_.CurrentAFT.CurrentPhysicalNumbering.numbering security (_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv security point))) := by
  rw [_P2s]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ',
      _P2b, _P2g, _P2a, _root_.CurrentAFT.CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (_root_.CurrentAFT.CurrentEmissionMetadata.restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val=body.val at hv
      have hn : ¬(_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val := by
        rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2, ← hv]
        exact Nat.not_le.mpr center.isLt
      simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, ← he, Equiv.symm_apply_apply, _P2a,
        _root_.CurrentAFT.CurrentBinaryBaselines.role, hn, false_and, if_false, add_zero]
    · have hv := congrArg Fin.val he
      change _root_.CurrentAFT.ActualBlockFock.centerCount security+queue.val=body.val at hv
      have hy : (_root_.CurrentAFT.CurrentEmissionMetadata.current security).centers ≤ body.val := by
        rw [(_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.2.2, ← hv]
        omega
      simp only [_root_.CurrentAFT.CurrentEmissionMetadata.pointEquiv, Equiv.coe_fn_mk, _root_.CurrentAFT.CurrentBinaryLoadColumns.loadEntry, _root_.CurrentAFT.CurrentLinearPhysicalLoad.physical, ← he, Equiv.symm_apply_apply, _P2a,
        _root_.CurrentAFT.CurrentBinaryBaselines.role, hy, true_and, _P2c]
open _root_.P2Mf6bd8d28 renaming h81 → _P29
end
open _root_.P2Mf6bd8d28 renaming h77 → _P25
open _root_.P2Mf6bd8d28 renaming h78 → _P26
open _root_.P2Mf6bd8d28 renaming h79 → _P27
open _root_.P2Mf6bd8d28 renaming h80 → _P28
open _root_.P2Mf6bd8d28 renaming h81 → _P29
open _root_.P2Mf6bd8d28 renaming h82 → _P2a
open _root_.P2Mf6bd8d28 renaming h83 → _P2b
open _root_.P2Mf6bd8d28 renaming h84 → _P2c
open _root_.P2Mf6bd8d28 renaming h85 → _P2d
open _root_.P2Mf6bd8d28 renaming h86 → _P2e
open _root_.P2Mf6bd8d28 renaming h87 → _P2f
open _root_.P2Mf6bd8d28 renaming h88 → _P2g
end CurrentAFT.CurrentBinaryLoadSemantic
open _root_.P2Mf6bd8d28 renaming h77 → _P25
open _root_.P2Mf6bd8d28 renaming h78 → _P26
open _root_.P2Mf6bd8d28 renaming h79 → _P27
open _root_.P2Mf6bd8d28 renaming h80 → _P28
open _root_.P2Mf6bd8d28 renaming h81 → _P29
open _root_.P2Mf6bd8d28 renaming h82 → _P2a
open _root_.P2Mf6bd8d28 renaming h83 → _P2b
open _root_.P2Mf6bd8d28 renaming h84 → _P2c
open _root_.P2Mf6bd8d28 renaming h85 → _P2d
open _root_.P2Mf6bd8d28 renaming h86 → _P2e
open _root_.P2Mf6bd8d28 renaming h87 → _P2f
open _root_.P2Mf6bd8d28 renaming h88 → _P2g
end
open _root_.P2Mf6bd8d28 renaming h77 → _P25
open _root_.P2Mf6bd8d28 renaming h78 → _P26
open _root_.P2Mf6bd8d28 renaming h79 → _P27
open _root_.P2Mf6bd8d28 renaming h80 → _P28
open _root_.P2Mf6bd8d28 renaming h81 → _P29
open _root_.P2Mf6bd8d28 renaming h82 → _P2a
open _root_.P2Mf6bd8d28 renaming h83 → _P2b
open _root_.P2Mf6bd8d28 renaming h84 → _P2c
open _root_.P2Mf6bd8d28 renaming h85 → _P2d
open _root_.P2Mf6bd8d28 renaming h86 → _P2e
open _root_.P2Mf6bd8d28 renaming h87 → _P2f
open _root_.P2Mf6bd8d28 renaming h88 → _P2g
namespace CurrentAFT.CurrentBinaryFallbackSemantic
end CurrentAFT.CurrentBinaryFallbackSemantic
namespace CurrentAFT.CurrentBinaryLoadSemantic
end CurrentAFT.CurrentBinaryLoadSemantic
namespace CurrentAFT.CurrentBinaryLoadSemantic.basisInput
end CurrentAFT.CurrentBinaryLoadSemantic.basisInput
namespace CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv
end CurrentAFT.CurrentBinaryLoadSemantic.blockEquiv
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
namespace CurrentAFT.CurrentLinearPhysicalLoad.primary
end CurrentAFT.CurrentLinearPhysicalLoad.primary
namespace CurrentAFT.CurrentProposalDimensions
end CurrentAFT.CurrentProposalDimensions
namespace CurrentAFT.CurrentProposalDimensions.bodyEquiv
end CurrentAFT.CurrentProposalDimensions.bodyEquiv
section
namespace CurrentAFT.CurrentBinaryMatrixSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
theorem _root_.P2Mf6bd8d28.h91 (security : ℕ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (count : ℕ) (hc : count = _root_.CurrentAFT.CurrentAffineGeometry.edgeCount security)
    (modulus : List Bool) (hm : _root_.AFT.BinaryArithmetic.value modulus = _root_.CurrentAFT.Parameters.modulus security)
    (injection load : Vector _root_.AFT.BinaryArithmetic.IntegerBits (count + 1))
    (hi : ∀ vertex, (injection.get vertex).decode = if vertex.val < _root_.CurrentAFT.Parameters.modulus security then 1 else 0)
    (target : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (hl : ∀ vertex, (load.get vertex).decode = _root_.CurrentAFT.CurrentAffineLoad.rounding security target
      (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security (vertex.cast (congrArg (fun n => n + 1) hc)))) :
    _root_.CurrentAFT.CurrentAffineLoad.packSource security
      ((fun edge => ((_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).edges.get (edge.cast hc.symm)).decode),
        (_root_.AFT.BinaryArithmetic.binaryRoundingInverse count modulus injection load).charge.decode) = target := by
  subst count
  apply _P1h security layout modulus hm injection load
    (fun vertex => hi vertex) target
  intro vertex
  simpa only [id_eq,Fin.cast_refl] using hl vertex
open _root_.P2Mf6bd8d28 renaming h91 → _P2j
theorem _root_.P2Mf6bd8d28.h93 (security : ℕ) (vertex : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security
      (vertex.cast (congrArg (fun n => n + 1) (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1)) = _root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security vertex := by
  apply Fin.ext
  rfl
open _root_.P2Mf6bd8d28 renaming h93 → _P2l
theorem _root_.P2Mf6bd8d28.h92 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (column row : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    ((_root_.AFT.BinaryArithmetic.binaryPermutedColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
      (_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value).value
      (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value column).value.get row).decode =
    _root_.CurrentAFT.CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
      (fun leg => (scale.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode)
      (_root_.CurrentAFT.CurrentBinaryLoadSemantic.basisInput security column) (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security row) := by
  rw [_P4, _P23, _P29]
  have hp := _P2m security ((_root_.AFT.physicalVertexNumberingProgram (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security) (_root_.CurrentAFT.CurrentEmissionMetadata.current security).rest
    (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.CurrentEmissionMetadata.current_counts security).2.2.2.1).symm ((_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, _P1u, Equiv.symm_apply_apply]
open _root_.P2Mf6bd8d28 renaming h92 → _P2k
theorem _root_.P2Mf6bd8d28.h90 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (core : _root_.CurrentAFT.CurrentCoreProposal.MaterializedCore security) (scale shear : Vector _root_.AFT.BinaryArithmetic.IntegerBits (_root_.CurrentAFT.CurrentBinaryLoadColumns.Legs security))
    (column : Fin (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.Size security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security
      (_root_.AFT.BinaryArithmetic.binaryAffineColumn (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges
        (_root_.AFT.BinaryArithmetic.canonicalCounter (_root_.CurrentAFT.PublicParameterProgram.modulus security).count).digits
        (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.injection security).value
        (_root_.CurrentAFT.CurrentBinaryLoadColumns.matrix security scale shear (_root_.CurrentAFT.CurrentEmissionRootOrder.positions security layout core).value).value
        (_root_.CurrentAFT.CurrentBinaryAffinePrimitives.endpointPermutation security core).value column).value =
    fun row => _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout.layout core.core
      (fun leg => (scale.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((_root_.CurrentAFT.CurrentEmissionMetadata.legEquiv security).symm leg)).decode) row (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column) := by
  unfold _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate _root_.AFT.BinaryArithmetic.binaryAffineColumn
  apply _P2j security layout.layout (_root_.CurrentAFT.CurrentEmissionMetadata.current security).edges (_root_.CurrentAFT.CurrentEmissionMetadata.current_values security).2.1
  · rw [_root_.AFT.BinaryArithmetic.canonicalCounter_value, _root_.CurrentAFT.PublicParameterProgram.modulus_value]
  · intro vertex
    exact _P1v security vertex
  · intro vertex
    rw [_P2k, _P2l]
    exact congrFun (_P1k security layout.layout core.core _ _
      (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security column)).symm (_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security vertex)
open _root_.P2Mf6bd8d28 renaming h90 → _P2i
theorem _root_.P2Mf6bd8d28.h89 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (sample : _root_.CurrentAFT.CurrentMaterializedCompletion.Result security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled security layout sample) =
      _root_.CurrentAFT.CurrentAffineGeometry.matrix security layout.layout sample.core.core
        (_root_.CurrentAFT.CurrentAffineData.scales security sample.charts.get) (_root_.CurrentAFT.CurrentAffineData.shears security sample.charts.get) := by
  funext row column
  simp only [_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix, _root_.CurrentAFT.CurrentBinaryAffineEmitter.assembled, _root_.AFT.BinaryArithmetic.storeData_get, _P2i,
    Equiv.apply_symm_apply]
  congr 1 <;> funext leg <;>
    simp only [_P1w, Equiv.apply_symm_apply,
      _root_.CurrentAFT.CurrentAffineData.scales, _root_.CurrentAFT.CurrentAffineData.shears]
open _root_.P2Mf6bd8d28 renaming h89 → _P2h
end
open _root_.P2Mf6bd8d28 renaming h89 → _P2h
open _root_.P2Mf6bd8d28 renaming h90 → _P2i
open _root_.P2Mf6bd8d28 renaming h91 → _P2j
open _root_.P2Mf6bd8d28 renaming h92 → _P2k
open _root_.P2Mf6bd8d28 renaming h93 → _P2l
end CurrentAFT.CurrentBinaryMatrixSemantic
open _root_.P2Mf6bd8d28 renaming h89 → _P2h
open _root_.P2Mf6bd8d28 renaming h90 → _P2i
open _root_.P2Mf6bd8d28 renaming h91 → _P2j
open _root_.P2Mf6bd8d28 renaming h92 → _P2k
open _root_.P2Mf6bd8d28 renaming h93 → _P2l
end
open _root_.P2Mf6bd8d28 renaming h89 → _P2h
open _root_.P2Mf6bd8d28 renaming h90 → _P2i
open _root_.P2Mf6bd8d28 renaming h91 → _P2j
open _root_.P2Mf6bd8d28 renaming h92 → _P2k
open _root_.P2Mf6bd8d28 renaming h93 → _P2l
namespace CurrentAFT.CurrentAffineData.shears
end CurrentAFT.CurrentAffineData.shears
namespace CurrentAFT.CurrentBinaryMatrixSemantic
end CurrentAFT.CurrentBinaryMatrixSemantic
namespace CurrentAFT.CurrentBinaryOffsetSemantic
end CurrentAFT.CurrentBinaryOffsetSemantic
section
namespace CurrentAFT.CurrentBinaryEmitterSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
theorem _root_.P2Mf6bd8d28.h69 (security : ℕ) (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security)
    (input : Option (_root_.CurrentAFT.CurrentMaterializedCompletion.Result security)) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout input) =
      (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout.layout (input.map _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample)).matrix := by
  cases input with
  | none => exact _P1z security
  | some sample =>
    by_cases h : _root_.CurrentAFT.CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (_P1r security layout sample h).1
      change (fun row column => _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security
        ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (_P2h security layout sample).trans (by
        simp only [_root_.CurrentAFT.NumericalAffineTransport.realizeResult, Option.map_some, _root_.CurrentAFT.CurrentPublicAffineSample.realize,
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample, _root_.CurrentAFT.CurrentAffineData.assemble, dif_pos h, _root_.CurrentAFT.CurrentAffineData.assembled])
    · have he := (_P1q security layout sample h).1
      change (fun row column => _root_.CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate security
        ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((_root_.CurrentAFT.CurrentEmissionMetadata.vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (_P1z security).trans (by
        simp only [_root_.CurrentAFT.NumericalAffineTransport.realizeResult, Option.map_some, _root_.CurrentAFT.CurrentPublicAffineSample.realize,
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample, _root_.CurrentAFT.CurrentAffineData.assemble, dif_neg h, _root_.CurrentAFT.CurrentAffineData.fallback])
open _root_.P2Mf6bd8d28 renaming h69 → _P1x
end
open _root_.P2Mf6bd8d28 renaming h69 → _P1x
end CurrentAFT.CurrentBinaryEmitterSemantic
open _root_.P2Mf6bd8d28 renaming h69 → _P1x
end
open _root_.P2Mf6bd8d28 renaming h69 → _P1x
namespace CurrentAFT.CurrentProposalResources
end CurrentAFT.CurrentProposalResources
namespace CurrentAFT.CurrentProposalResources.anchorSizePolynomial
end CurrentAFT.CurrentProposalResources.anchorSizePolynomial
namespace CurrentAFT.CurrentProposalResources.countPolynomial
end CurrentAFT.CurrentProposalResources.countPolynomial
namespace CurrentAFT.CurrentProposalResources.cutoffSizePolynomial
end CurrentAFT.CurrentProposalResources.cutoffSizePolynomial
namespace CurrentAFT.CurrentProposalResources.metadataWorkPolynomial
end CurrentAFT.CurrentProposalResources.metadataWorkPolynomial
namespace CurrentAFT.CurrentProposalResources.primeSizePolynomial
end CurrentAFT.CurrentProposalResources.primeSizePolynomial
namespace CurrentAFT.CurrentProposalResources.shiftWorkPolynomial
end CurrentAFT.CurrentProposalResources.shiftWorkPolynomial
namespace CurrentAFT.CurrentPublicShiftProgram.workBound
end CurrentAFT.CurrentPublicShiftProgram.workBound
namespace CurrentAFT.PublicBitTapes
end CurrentAFT.PublicBitTapes
namespace CurrentAFT.PublicBitTapes.Encoding
end CurrentAFT.PublicBitTapes.Encoding
namespace CurrentAFT.PublicBitTapes.Encoding.mk
end CurrentAFT.PublicBitTapes.Encoding.mk
namespace CurrentAFT.UniformPolynomialBound
end CurrentAFT.UniformPolynomialBound
section
namespace CurrentAFT.PublicBitResources
open AFT PublicBitTapes CurrentProposalResources
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current
private theorem _root_.P2Mf6bd8d28.h835 (resource : ℕ → ℕ) (polynomial : Polynomial ℕ)
    (h : ∀ security, resource security ≤ polynomial.eval security) : _root_.CurrentAFT.UniformPolynomialBound resource := ⟨polynomial,h⟩
open _root_.P2Mf6bd8d28 renaming h835 → _Pn7
attribute [local irreducible] UniformPolynomialBound
theorem _root_.P2Mf6bd8d28.h126 : _root_.CurrentAFT.UniformPolynomialBound (fun security => (_root_.CurrentAFT.PublicBitTapes.current security).bits) := by
  have hcontrols : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentProposalDimensions.current n).controls) :=
    _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.countPolynomial (fun n => (_root_.CurrentAFT.CurrentProposalResources.count_bounds n).1)
  have hlegs : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentProposalDimensions.current n).legs) :=
    _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.countPolynomial (fun n => (_root_.CurrentAFT.CurrentProposalResources.count_bounds n).2.1)
  have hcolors : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentProposalDimensions.current n).colors) :=
    _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.countPolynomial (fun n => (_root_.CurrentAFT.CurrentProposalResources.count_bounds n).2.2.1)
  have hbody : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentProposalDimensions.current n).body) :=
    _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.countPolynomial (fun n => (_root_.CurrentAFT.CurrentProposalResources.count_bounds n).2.2.2.1)
  have hdimension : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentProposalDimensions.current n).dimension) :=
    _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.countPolynomial (fun n => (_root_.CurrentAFT.CurrentProposalResources.count_bounds n).2.2.2.2)
  have hq : _root_.CurrentAFT.UniformPolynomialBound _root_.CurrentAFT.Parameters.modulus :=
    hcolors.mono (fun n => by rw [(_root_.CurrentAFT.CurrentProposalDimensions.current_values n).1])
  have hnativeq : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.PublicParameterProgram.modulus n).count) :=
    hq.mono (fun n => by rw [_root_.CurrentAFT.PublicParameterProgram.modulus_value])
  have hsafe : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentReferenceDraw.counts n).safe) :=
    hq.mono (fun n => by rw [(_root_.CurrentAFT.CurrentReferenceDraw.counts_values n).2.2]; exact Nat.sub_le ..)
  have hanchor : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.CurrentAnchorIndexDraw.width n).count) := by
    refine _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.anchorSizePolynomial (fun n => ?_)
    simp only [_root_.CurrentAFT.CurrentAnchorIndexDraw.width_value, _root_.CurrentAFT.DiffuseProfiles.anchorWidth_eq,
      _root_.CurrentAFT.CurrentProposalResources.anchorSizePolynomial, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat, _root_.CurrentAFT.Parameters.base, le_refl]
  have hcutoff : _root_.CurrentAFT.UniformPolynomialBound _root_.CurrentAFT.DiffuseProfiles.edgeCutoff := by
    refine _Pn7 _ _root_.CurrentAFT.CurrentProposalResources.cutoffSizePolynomial (fun n => ?_)
    simp only [_root_.CurrentAFT.CurrentProposalResources.cutoffSizePolynomial, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat, _root_.CurrentAFT.DiffuseProfiles.edgeCutoff, _root_.CurrentAFT.Parameters.sourceCutoff, _root_.CurrentAFT.Parameters.base]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hretry : _root_.CurrentAFT.UniformPolynomialBound (fun n => (_root_.CurrentAFT.BinaryRejectionCap.current n).count) :=
    _Pn7 _ _root_.CurrentAFT.BinaryRejectionCap.countPolynomial _root_.CurrentAFT.BinaryRejectionCap.count_bound
  unfold _root_.CurrentAFT.PublicBitTapes.current _root_.CurrentAFT.PublicBitTapes.materialized _root_.CurrentAFT.PublicBitTapes.rejection _root_.CurrentAFT.PublicBitTapes.completion _root_.CurrentAFT.PublicBitTapes.charts _root_.CurrentAFT.PublicBitTapes.core _root_.CurrentAFT.PublicBitTapes.leg _root_.CurrentAFT.PublicBitTapes.seed _root_.CurrentAFT.PublicBitTapes.control _root_.CurrentAFT.PublicBitTapes.safe _root_.CurrentAFT.PublicBitTapes.edge
    _root_.CurrentAFT.PublicBitTapes.Encoding.prod _root_.CurrentAFT.PublicBitTapes.Encoding.indexed _root_.CurrentAFT.PublicBitTapes.bits _root_.CurrentAFT.PublicBitTapes.flag _root_.AFT.RationalNumerics.windowTicketBits
  try dsimp only
  repeat' first
    | exact hcontrols
    | exact hlegs
    | exact hcolors
    | exact hbody
    | exact hdimension
    | exact hq
    | exact hnativeq
    | exact hsafe
    | exact hanchor
    | exact hcutoff
    | exact hretry
    | exact _root_.CurrentAFT.UniformPolynomialBound.identity
    | exact _root_.CurrentAFT.UniformPolynomialBound.constant _
    | apply _root_.CurrentAFT.UniformPolynomialBound.add
    | apply _root_.CurrentAFT.UniformPolynomialBound.mul
open _root_.P2Mf6bd8d28 renaming h126 → _P3i
end
open _root_.P2Mf6bd8d28 renaming h126 → _P3i
open _root_.P2Mf6bd8d28 renaming h835 → _Pn7
end CurrentAFT.PublicBitResources
open _root_.P2Mf6bd8d28 renaming h126 → _P3i
open _root_.P2Mf6bd8d28 renaming h835 → _Pn7
end
open _root_.P2Mf6bd8d28 renaming h126 → _P3i
namespace CurrentAFT.CurrentAffineData.intercepts
end CurrentAFT.CurrentAffineData.intercepts
namespace CurrentAFT.CurrentBinaryEmitterSemantic
end CurrentAFT.CurrentBinaryEmitterSemantic
namespace CurrentAFT.CurrentMaterializedCompletion.Result.sample
end CurrentAFT.CurrentMaterializedCompletion.Result.sample
namespace CurrentAFT.CurrentPublicAffineSample
end CurrentAFT.CurrentPublicAffineSample
namespace CurrentAFT.CurrentPublicAffineSample.realize
end CurrentAFT.CurrentPublicAffineSample.realize
namespace CurrentAFT.NumericalAffineTransport
end CurrentAFT.NumericalAffineTransport
namespace CurrentAFT.NumericalAffineTransport.realizeResult
end CurrentAFT.NumericalAffineTransport.realizeResult
namespace CurrentAFT.NumericalAffineTransport.realizeResult.match_1
end CurrentAFT.NumericalAffineTransport.realizeResult.match_1
namespace CurrentAFT.PublicBitResources
end CurrentAFT.PublicBitResources
section
namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw
noncomputable section
open scoped Classical
theorem _root_.P2Mf6bd8d28.h121 (security extra : ℕ) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.addWork security extra data) =
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security data := rfl
open _root_.P2Mf6bd8d28 renaming h121 → _P3d
theorem _root_.P2Mf6bd8d28.h122 (security extra : ℕ) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security (_root_.CurrentAFT.PublicAffinePipeline.addWork security extra data) =
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.offset security data := rfl
open _root_.P2Mf6bd8d28 renaming h122 → _P3e
theorem _root_.P2Mf6bd8d28.h124 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (word : _root_.CurrentAFT.CurrentMaterializedCompletion.Tapes security) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.forLayout security order producer layout word) =
      (_root_.CurrentAFT.NumericalAffineTransport.realizeResult security layout.layout
        ((_root_.CurrentAFT.CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          _root_.CurrentAFT.CurrentMaterializedCompletion.Result.sample)).matrix :=
  _P1x security layout _
open _root_.P2Mf6bd8d28 renaming h124 → _P3g
theorem _root_.P2Mf6bd8d28.h123 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (layout : _root_.CurrentAFT.CurrentLayoutDraw.Cache security) (word : _root_.CurrentAFT.CurrentMaterializedCompletion.Tapes security) :
    IsUnit ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.forLayout security order producer layout word)).map
      (Int.castRingHom (ZMod (_root_.CurrentAFT.Parameters.modulus security)))) := by
  rw [_P3g]
  exact _P3b security layout.layout _
open _root_.P2Mf6bd8d28 renaming h123 → _P3f
theorem _root_.P2Mf6bd8d28.h125 (security order : ℕ) (producer : _root_.CurrentAFT.PublicAffinePipeline.Producer security order)
    (word : _root_.CurrentAFT.PublicBitTapes.Tapes security) :
    IsUnit ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.PublicAffinePipeline.run security order producer word)).map
      (Int.castRingHom (ZMod (_root_.CurrentAFT.Parameters.modulus security)))) := by
  rw [_root_.CurrentAFT.PublicAffinePipeline.run, _P3d]
  exact _P3f security order producer _ word.2
open _root_.P2Mf6bd8d28 renaming h125 → _P3h
end
open _root_.P2Mf6bd8d28 renaming h121 → _P3d
open _root_.P2Mf6bd8d28 renaming h122 → _P3e
open _root_.P2Mf6bd8d28 renaming h123 → _P3f
open _root_.P2Mf6bd8d28 renaming h124 → _P3g
open _root_.P2Mf6bd8d28 renaming h125 → _P3h
end CurrentAFT.PublicAffinePipeline
open _root_.P2Mf6bd8d28 renaming h121 → _P3d
open _root_.P2Mf6bd8d28 renaming h122 → _P3e
open _root_.P2Mf6bd8d28 renaming h123 → _P3f
open _root_.P2Mf6bd8d28 renaming h124 → _P3g
open _root_.P2Mf6bd8d28 renaming h125 → _P3h
end
open _root_.P2Mf6bd8d28 renaming h121 → _P3d
open _root_.P2Mf6bd8d28 renaming h122 → _P3e
open _root_.P2Mf6bd8d28 renaming h123 → _P3f
open _root_.P2Mf6bd8d28 renaming h124 → _P3g
open _root_.P2Mf6bd8d28 renaming h125 → _P3h
namespace CurrentAFT.PublicAffinePipeline
end CurrentAFT.PublicAffinePipeline
namespace CurrentAFT.PublicAffinePipeline.run
end CurrentAFT.PublicAffinePipeline.run
section
namespace CurrentAFT.PublicAffinePipeline
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw
theorem _root_.P2Mf6bd8d28.h120 (security extra : ℕ) (data : _root_.CurrentAFT.CurrentBinaryAffineEmitter.Data security) :
    _root_.CurrentAFT.PublicAffinePipeline.gaussianChannel security (_root_.CurrentAFT.PublicAffinePipeline.addWork security extra data) = _root_.CurrentAFT.PublicAffinePipeline.gaussianChannel security data := by
  simp only [_root_.CurrentAFT.PublicAffinePipeline.gaussianChannel, _P3d, _P3e]
open _root_.P2Mf6bd8d28 renaming h120 → _P3c
end
open _root_.P2Mf6bd8d28 renaming h120 → _P3c
end CurrentAFT.PublicAffinePipeline
open _root_.P2Mf6bd8d28 renaming h120 → _P3c
end
open _root_.P2Mf6bd8d28 renaming h120 → _P3c
namespace AFT.BinaryArithmetic.UnaryCounterResult
end AFT.BinaryArithmetic.UnaryCounterResult
namespace AFT.BinaryArithmetic.UnaryCounterResult.mk
end AFT.BinaryArithmetic.UnaryCounterResult.mk
namespace AFT.BinaryArithmetic.addCounter
end AFT.BinaryArithmetic.addCounter
namespace AFT.BinaryArithmetic.addCounter.match_1
end AFT.BinaryArithmetic.addCounter.match_1
namespace AFT.BinaryArithmetic.doubleCounter
end AFT.BinaryArithmetic.doubleCounter
namespace AFT.BinaryArithmetic.doubleCounter.match_1
end AFT.BinaryArithmetic.doubleCounter.match_1
namespace AFT.BinaryArithmetic.multiplyCounter
end AFT.BinaryArithmetic.multiplyCounter
namespace AFT.BinaryArithmetic.readCounter
end AFT.BinaryArithmetic.readCounter
namespace AFT.BinaryArithmetic.readCounter.match_1
end AFT.BinaryArithmetic.readCounter.match_1
section
namespace CurrentAFT.BinaryPublicBitCodec
open AFT BinaryArithmetic RationalRejectionProgram PublicBitTapes
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
theorem _root_.P2Mf6bd8d28.h48 {State : Type*} (codec : _root_.CurrentAFT.BinaryPublicBitCodec.Codec State)
    (word : Fin codec.encoding.bits → Fin 2) :
    (_root_.CurrentAFT.BinaryPublicBitCodec.decode codec word).value = codec.encoding.equiv word := by
  simp only [_root_.CurrentAFT.BinaryPublicBitCodec.decode,codec.read_value,Vector.get_cast,_root_.AFT.BinaryArithmetic.storeData_get,Nat.zero_add]
  apply congrArg
  funext index
  congr 1
open _root_.P2Mf6bd8d28 renaming h48 → _P1c
theorem _root_.P2Mf6bd8d28.h47 {State : Type*} (codec : _root_.CurrentAFT.BinaryPublicBitCodec.Codec State) (target : _root_.CurrentAFT.PublicBitTapes.Encoding State)
    (same : codec.encoding=target) (word : Fin target.bits → Fin 2) :
    (_root_.CurrentAFT.BinaryPublicBitCodec.decodeAs codec target same word).value = target.equiv word := by
  subst target
  exact _P1c codec word
open _root_.P2Mf6bd8d28 renaming h47 → _P1b
end CurrentAFT.BinaryPublicBitCodec
open _root_.P2Mf6bd8d28 renaming h47 → _P1b
open _root_.P2Mf6bd8d28 renaming h48 → _P1c
end
open _root_.P2Mf6bd8d28 renaming h47 → _P1b
open _root_.P2Mf6bd8d28 renaming h48 → _P1c
namespace AFT.RationalNumerics.windowTicketBits
end AFT.RationalNumerics.windowTicketBits
namespace CurrentAFT.BinaryPublicBitCodec
end CurrentAFT.BinaryPublicBitCodec
namespace CurrentAFT.BinaryPublicBitCodec.Codec
end CurrentAFT.BinaryPublicBitCodec.Codec
namespace CurrentAFT.BinaryPublicBitCodec.Codec.mk
end CurrentAFT.BinaryPublicBitCodec.Codec.mk
namespace CurrentAFT.BinaryPublicBitCodec.Codec.read
end CurrentAFT.BinaryPublicBitCodec.Codec.read
namespace CurrentAFT.BinaryPublicBitCodec.copy
end CurrentAFT.BinaryPublicBitCodec.copy
namespace CurrentAFT.BinaryPublicBitCodec.decode
end CurrentAFT.BinaryPublicBitCodec.decode
namespace CurrentAFT.BinaryPublicBitSizes
end CurrentAFT.BinaryPublicBitSizes
namespace CurrentAFT.BinaryPublicBitSizes.Data
end CurrentAFT.BinaryPublicBitSizes.Data
namespace CurrentAFT.BinaryPublicBitSizes.Data.mk
end CurrentAFT.BinaryPublicBitSizes.Data.mk
namespace CurrentAFT.BinaryPublicBitSizes.Lengths
end CurrentAFT.BinaryPublicBitSizes.Lengths
namespace CurrentAFT.BinaryPublicBitSizes.Lengths.mk
end CurrentAFT.BinaryPublicBitSizes.Lengths.mk
namespace CurrentAFT.BinaryPublicBitSizes.assemble
end CurrentAFT.BinaryPublicBitSizes.assemble
namespace CurrentAFT.BinaryPublicBitSizes.current
end CurrentAFT.BinaryPublicBitSizes.current
namespace CurrentAFT.BinaryPublicBitSizes.formula
end CurrentAFT.BinaryPublicBitSizes.formula
namespace CurrentAFT.BinaryPublicBitSizes.workPolynomial
end CurrentAFT.BinaryPublicBitSizes.workPolynomial
namespace CurrentAFT.PublicBitTapes.split
end CurrentAFT.PublicBitTapes.split
section
namespace CurrentAFT.BinaryPublicBitDecode
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
open BinaryPublicBitCodec
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus BinaryPublicBitSizes.current PublicBitTapes.current
variable (security : ℕ) (sizes : BinaryPublicBitSizes.Data) (correct : sizes=BinaryPublicBitSizes.current security)
theorem _root_.P2Mf6bd8d28.h49 (security : ℕ) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    (_root_.CurrentAFT.BinaryPublicBitDecode.current security word).value=(_root_.CurrentAFT.PublicBitTapes.current security).equiv word :=
  _P1b (_root_.CurrentAFT.BinaryPublicBitDecode.codec security (_root_.CurrentAFT.BinaryPublicBitSizes.current security) rfl) (_root_.CurrentAFT.PublicBitTapes.current security)
    (_root_.CurrentAFT.BinaryPublicBitDecode.codec_encoding security (_root_.CurrentAFT.BinaryPublicBitSizes.current security) rfl) word
open _root_.P2Mf6bd8d28 renaming h49 → CurrentAFT.BinaryPublicBitDecode.current_value
open _root_.P2Mf6bd8d28 renaming h49 → _P1d
noncomputable section
attribute [local irreducible] UniformPolynomialBound
end
end CurrentAFT.BinaryPublicBitDecode
open _root_.P2Mf6bd8d28 renaming h49 → CurrentAFT.BinaryPublicBitDecode.current_value
open _root_.P2Mf6bd8d28 renaming h49 → _P1d
end
open _root_.P2Mf6bd8d28 renaming h49 → CurrentAFT.BinaryPublicBitDecode.current_value
open _root_.P2Mf6bd8d28 renaming h49 → _P1d
namespace CurrentAFT.ActualAffineEvaluator
end CurrentAFT.ActualAffineEvaluator
namespace CurrentAFT.ActualAffineEvaluator.budgetPolynomial
end CurrentAFT.ActualAffineEvaluator.budgetPolynomial
namespace CurrentAFT.ActualAffineEvaluator.coordinateEntry
end CurrentAFT.ActualAffineEvaluator.coordinateEntry
namespace CurrentAFT.ActualAffineEvaluator.decodeInput
end CurrentAFT.ActualAffineEvaluator.decodeInput
namespace CurrentAFT.ActualAffineEvaluator.dotWork
end CurrentAFT.ActualAffineEvaluator.dotWork
namespace CurrentAFT.ActualAffineEvaluator.evaluate
end CurrentAFT.ActualAffineEvaluator.evaluate
namespace CurrentAFT.ActualAffineEvaluator.nativeCoordinate
end CurrentAFT.ActualAffineEvaluator.nativeCoordinate
namespace CurrentAFT.ActualAffineEvaluator.productEntry
end CurrentAFT.ActualAffineEvaluator.productEntry
namespace CurrentAFT.ActualAffineEvaluator.productWork
end CurrentAFT.ActualAffineEvaluator.productWork
namespace CurrentAFT.ActualAffineEvaluator.row
end CurrentAFT.ActualAffineEvaluator.row
namespace CurrentAFT.ActualAffineEvaluator.rowWork
end CurrentAFT.ActualAffineEvaluator.rowWork
namespace CurrentAFT.ActualAffineEvaluator.workBound
end CurrentAFT.ActualAffineEvaluator.workBound
namespace CurrentAFT.BinaryFullResponseMatrixEntry
end CurrentAFT.BinaryFullResponseMatrixEntry
namespace CurrentAFT.BinaryFullResponseMatrixEntry.validWorkPolynomial
end CurrentAFT.BinaryFullResponseMatrixEntry.validWorkPolynomial
namespace CurrentAFT.BinaryNaturalCoordinates
end CurrentAFT.BinaryNaturalCoordinates
namespace CurrentAFT.BinaryNaturalCoordinates.current
end CurrentAFT.BinaryNaturalCoordinates.current
namespace CurrentAFT.BinaryPublicBitDecode
end CurrentAFT.BinaryPublicBitDecode
namespace CurrentAFT.PublicAffinePipeline.workPolynomial
end CurrentAFT.PublicAffinePipeline.workPolynomial
section
namespace CurrentAFT.ActualConstructiveSampler
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open ActualCalibrationRates BinaryFullResponseData
open Filter
open scoped Classical Topology
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current PublicParameterProgram.modulus
  BinaryPublicBitDecode.current PublicAffinePipeline.run
  CurrentBinaryAffineEmitter.matrix CurrentBinaryAffineEmitter.offset
theorem _root_.P2Mf6bd8d28.h27 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) :
    _root_.CurrentAFT.ActualConstructiveSampler.law security order data =
      (_root_.AFT.FiniteDist.uniform (Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2)).mix
        (fun word => _root_.CurrentAFT.PublicAffinePipeline.gaussianChannel security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data word)) := by
  simp only [_root_.CurrentAFT.ActualConstructiveSampler.law,_root_.CurrentAFT.PublicAffinePipeline.fairGaussian,_root_.CurrentAFT.ActualConstructiveSampler.run,_P3c,
    _P1d,_root_.CurrentAFT.PublicAffinePipeline.fairBitRun]
open _root_.P2Mf6bd8d28 renaming h27 → _Pr
theorem _root_.P2Mf6bd8d28.h28 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    _root_.CurrentAFT.ActualConstructiveSampler.run security order data word=
      _root_.CurrentAFT.PublicAffinePipeline.addWork security (_root_.CurrentAFT.BinaryPublicBitDecode.current security word).work
        (_root_.CurrentAFT.PublicAffinePipeline.fairBitRun security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) word) := by
  exact congrArg (fun decoded => _root_.CurrentAFT.PublicAffinePipeline.addWork security (_root_.CurrentAFT.BinaryPublicBitDecode.current security word).work
    (_root_.CurrentAFT.PublicAffinePipeline.run security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) decoded))
      (_P1d security word)
open _root_.P2Mf6bd8d28 renaming h28 → _Ps
theorem _root_.P2Mf6bd8d28.h30 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data word)=
      _root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security
        (_root_.CurrentAFT.PublicAffinePipeline.fairBitRun security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) word) := by
  exact (congrArg (_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security) (_Ps security order data word)).trans
    (_P3d security _ _)
open _root_.P2Mf6bd8d28 renaming h30 → _Pu
theorem _root_.P2Mf6bd8d28.h29 (security order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order) (word : Fin (_root_.CurrentAFT.PublicBitTapes.current security).bits → Fin 2) :
    IsUnit ((_root_.CurrentAFT.CurrentBinaryAffineEmitter.matrix security (_root_.CurrentAFT.ActualConstructiveSampler.run security order data word)).map
      (Int.castRingHom (ZMod (_root_.CurrentAFT.Parameters.modulus security)))) := by
  rw [_Pu]
  exact _P3h security order (_root_.CurrentAFT.ActualConstructiveSampler.producer security order data) ((_root_.CurrentAFT.PublicBitTapes.current security).equiv word)
open _root_.P2Mf6bd8d28 renaming h29 → _Pt
attribute [local instance] _root_.CurrentAFT.ActualConstructiveSampler.uniformFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualConstructiveSampler.modulusNeZero
end
open _root_.P2Mf6bd8d28 renaming h27 → _Pr
open _root_.P2Mf6bd8d28 renaming h28 → _Ps
open _root_.P2Mf6bd8d28 renaming h29 → _Pt
open _root_.P2Mf6bd8d28 renaming h30 → _Pu
end CurrentAFT.ActualConstructiveSampler
open _root_.P2Mf6bd8d28 renaming h27 → _Pr
open _root_.P2Mf6bd8d28 renaming h28 → _Ps
open _root_.P2Mf6bd8d28 renaming h29 → _Pt
open _root_.P2Mf6bd8d28 renaming h30 → _Pu
end
open _root_.P2Mf6bd8d28 renaming h27 → _Pr
open _root_.P2Mf6bd8d28 renaming h28 → _Ps
open _root_.P2Mf6bd8d28 renaming h29 → _Pt
open _root_.P2Mf6bd8d28 renaming h30 → _Pu
section
set_option autoImplicit false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.Integration
open AFT GaussianSource
theorem _root_.P2Mf6bd8d28.h180 {d : ℕ} (σ : ℝ) (x : Fin d → ℤ) :
    rhoInt σ x = _root_.AFT.GaussianSource.latticeWeight d σ x := by
  unfold rhoInt RegevLWE.GaussConv.rho _root_.AFT.GaussianSource.latticeWeight
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  ring
open _root_.P2Mf6bd8d28 renaming h180 → _P50
theorem _root_.P2Mf6bd8d28.h172 (d : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    (∑' x : Fin d → ℤ, _root_.AFT.GaussianSource.latticeWeight d σ x) = ((_root_.AFT.GaussianSource.normalizer σ) ^ d).toReal := by
  rw [← _Pj d σ hσ,
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro x
  exact (ENNReal.toReal_ofReal (Real.exp_nonneg _)).symm
open _root_.P2Mf6bd8d28 renaming h172 → _P4s
theorem _root_.P2Mf6bd8d28.h171 {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x : Fin d → ℤ) :
    (_root_.AFT.GaussianSource.latticeGaussian d σ hσ x).toReal =
      rhoInt σ x / (∑' z : Fin d → ℤ, rhoInt σ z) := by
  simp_rw [_P50]
  rw [_P4s d σ hσ]
  rw [_Pi, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_pow]
  simp only [_root_.AFT.GaussianSource.latticeWeight, div_eq_mul_inv, inv_pow]
open _root_.P2Mf6bd8d28 renaming h171 → _P4r
theorem _root_.P2Mf6bd8d28.h169 {α β : Type*} [Fintype β] (p : PMF α) (f : α → β) (b : β) :
    (_root_.AFT.GaussianSource.finiteLaw (p.map f)).weight b = ∑' a, if f a = b then (p a).toReal else 0 := by
  classical
  change ((p.map f) b).toReal = _
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : f a = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top
open _root_.P2Mf6bd8d28 renaming h169 → _P4p
theorem _root_.P2Mf6bd8d28.h179 (q d : ℕ) [NeZero q] (σ : ℝ) (hσ : 0 < σ)
    (e : Fin d → ZMod q) :
    (_root_.AFT.GaussianSource.residueGaussian d q σ hσ).weight e = chiG q d σ e := by
  classical
  unfold _root_.AFT.GaussianSource.residueGaussian
  rw [_P4p]
  unfold chiG
  simp_rw [_P4r σ hσ]
  rw [← tsum_div_const]
  apply tsum_congr
  intro x
  change (if modq q x = e then _ else _) = _
  split_ifs <;> simp
open _root_.P2Mf6bd8d28 renaming h179 → _P4z
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h169 → _P4p
open _root_.P2Mf6bd8d28 renaming h171 → _P4r
open _root_.P2Mf6bd8d28 renaming h172 → _P4s
open _root_.P2Mf6bd8d28 renaming h179 → _P4z
open _root_.P2Mf6bd8d28 renaming h180 → _P50
end
open _root_.P2Mf6bd8d28 renaming h169 → _P4p
open _root_.P2Mf6bd8d28 renaming h171 → _P4r
open _root_.P2Mf6bd8d28 renaming h172 → _P4s
open _root_.P2Mf6bd8d28 renaming h179 → _P4z
open _root_.P2Mf6bd8d28 renaming h180 → _P50
namespace CurrentAFT.CurrentHiddenSourceTransport
end CurrentAFT.CurrentHiddenSourceTransport
namespace CurrentAFT.CurrentSourceLayout
end CurrentAFT.CurrentSourceLayout
namespace CurrentAFT.CurrentSourceLayout.splitWord
end CurrentAFT.CurrentSourceLayout.splitWord
namespace InfoLossLAR
end InfoLossLAR
namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase
namespace InfoLossLAR.WorstCase.Integration
end InfoLossLAR.WorstCase.Integration
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.Integration
open AFT GaussianSource
open CurrentAFT.GaussianProductProtection CurrentAFT.CurrentSourceProtection
theorem _root_.P2Mf6bd8d28.h158 (width : ℝ) (hwidth : 0 < width)
    (count : ℕ) (word : Fin count → ℤ) :
    _root_.CurrentAFT.GaussianProductProtection.fullMass width count word = (_root_.AFT.GaussianSource.latticeGaussian count width hwidth word).toReal := by
  rw [_root_.AFT.GaussianSource.latticeGaussian, _Pg, ENNReal.toReal_prod]
  unfold _root_.CurrentAFT.GaussianProductProtection.fullMass
  exact Finset.prod_congr rfl (fun index _ =>
    _P34 width hwidth (word index))
open _root_.P2Mf6bd8d28 renaming h158 → _P4e
theorem _root_.P2Mf6bd8d28.h168 {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) :
    _root_.AFT.GaussianSource.finiteLaw (p.map f) = (_root_.AFT.GaussianSource.finiteLaw p).map f := by
  apply _root_.AFT.FiniteDist.ext
  intro b
  rw [_P4p, tsum_fintype, _root_.AFT.FiniteDist.map_weight]
  rfl
open _root_.P2Mf6bd8d28 renaming h168 → _P4o
theorem _root_.P2Mf6bd8d28.h160 {Output : Type*} [Fintype Output]
    (security : ℕ) (f : (Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) → Output) :
    _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenGaussianOutput security
      (fun input => (_root_.AFT.FiniteDist.uniform Unit).map (fun _ => f input)) =
      _root_.AFT.GaussianSource.finiteLaw ((_root_.AFT.GaussianSource.latticeGaussian (_root_.CurrentAFT.Parameters.dimension security)
        (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security)).map f) := by
  apply _root_.AFT.FiniteDist.ext
  intro output
  rw [_P4p]
  change (∑' input, _root_.CurrentAFT.GaussianProductProtection.fullMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.Parameters.dimension security) input *
    ((_root_.AFT.FiniteDist.uniform Unit).map (fun _ => f input)).weight output) = _
  apply tsum_congr
  intro input
  rw [_P4e _ (_root_.CurrentAFT.CurrentSourceProtection.width_pos security)]
  by_cases h : f input = output
  · simp [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.uniform_weight, h]
  · simp [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.uniform_weight, h]
open _root_.P2Mf6bd8d28 renaming h160 → _P4g
theorem _root_.P2Mf6bd8d28.h161 {Output : Type*} [Fintype Output]
    (security q : ℕ) [NeZero q]
    (f : (Fin (_root_.CurrentAFT.Parameters.dimension security) → ZMod q) → Output) :
    _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenGaussianOutput security
      (fun input => (_root_.AFT.FiniteDist.uniform Unit).map (fun _ => f (modq q input))) =
      (_root_.AFT.GaussianSource.residueGaussian (_root_.CurrentAFT.Parameters.dimension security) q
        (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security)).map f := by
  rw [_P4g]
  unfold _root_.AFT.GaussianSource.residueGaussian
  rw [← _P4o, PMF.map_comp]
  rfl
open _root_.P2Mf6bd8d28 renaming h161 → _P4h
theorem _root_.P2Mf6bd8d28.h159 (security q : ℕ) [NeZero q]
    (Q : Matrix (Fin (_root_.CurrentAFT.Parameters.dimension security))
      (Fin (_root_.CurrentAFT.Parameters.dimension security)) ℤ)
    (offset : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenGaussianOutput security
      (fun input => (_root_.AFT.FiniteDist.uniform Unit).map (fun _ index =>
        ((Q.mulVec input index + offset index : ℤ) : ZMod q))) =
      (_root_.AFT.GaussianSource.residueGaussian (_root_.CurrentAFT.Parameters.dimension security) q
        (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security)).map (evalAffine Q offset) := by
  convert _P4h security q (evalAffine Q offset) using 1
  congr 1
  funext input
  congr 1
  funext unit index
  simp only [evalAffine, matModq, modq, Matrix.mulVec, dotProduct,
    Pi.add_apply, Matrix.map_apply, Int.cast_add, Int.cast_sum, Int.cast_mul]
open _root_.P2Mf6bd8d28 renaming h159 → _P4f
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h158 → _P4e
open _root_.P2Mf6bd8d28 renaming h159 → _P4f
open _root_.P2Mf6bd8d28 renaming h160 → _P4g
open _root_.P2Mf6bd8d28 renaming h161 → _P4h
open _root_.P2Mf6bd8d28 renaming h168 → _P4o
end
open _root_.P2Mf6bd8d28 renaming h158 → _P4e
open _root_.P2Mf6bd8d28 renaming h159 → _P4f
open _root_.P2Mf6bd8d28 renaming h160 → _P4g
open _root_.P2Mf6bd8d28 renaming h161 → _P4h
open _root_.P2Mf6bd8d28 renaming h168 → _P4o
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.totalVariation
end AFT.FiniteDist.totalVariation
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.Integration
open AFT
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h181 {α : Type*} [Fintype α] (p q : _root_.AFT.FiniteDist α) :
    sdist p.weight q.weight = p.totalVariation q := by
  rw [FiniteDist.totalVariation_eq_half_l1]
  unfold sdist
  ring
open _root_.P2Mf6bd8d28 renaming h181 → _P51
theorem _root_.P2Mf6bd8d28.h182 {q d : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) (x : Fin d → ZMod q) :
    transportLaw S source.weight x =
      ((_root_.AFT.FiniteDist.uniform Ω).mix (fun seed =>
        source.map (evalAffine (S seed).1 (S seed).2))).weight x := by
  simp only [transportLaw, avg, _root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.uniform_weight,
    _root_.AFT.FiniteDist.map_weight, ← Finset.mul_sum]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro seed hseed
  apply Finset.sum_congr rfl
  intro error herror
  by_cases h : evalAffine (S seed).1 (S seed).2 error = x
  · simp only [if_pos h]
  · simp only [if_neg h]
open _root_.P2Mf6bd8d28 renaming h182 → _P52
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h181 → _P51
open _root_.P2Mf6bd8d28 renaming h182 → _P52
end
open _root_.P2Mf6bd8d28 renaming h181 → _P51
open _root_.P2Mf6bd8d28 renaming h182 → _P52
namespace AFT.FiniteDist.mk
end AFT.FiniteDist.mk
namespace AFT.FiniteDist.uniform
end AFT.FiniteDist.uniform
namespace AFT.endpointIntegralPreimage
end AFT.endpointIntegralPreimage
namespace AFT.endpointLift
end AFT.endpointLift
namespace AFT.endpointProjection
end AFT.endpointProjection
namespace AFT.integerLabel
end AFT.integerLabel
namespace AFT.liftCoordinates
end AFT.liftCoordinates
namespace AFT.reduceCoordinates
end AFT.reduceCoordinates
namespace AFT.zeroFiberPullback
end AFT.zeroFiberPullback
section
set_option autoImplicit false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.Integration
open AFT
theorem _root_.P2Mf6bd8d28.h175 (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    LinearMap.toMatrix' (_root_.AFT.pathIncidence n) i j =
      if i = j.castSucc then 1 else if (i : ℕ) = (j : ℕ) + 1 then -1 else 0 := by
  rw [LinearMap.toMatrix'_apply]
  change _root_.AFT.pathLoad n (Pi.single j 1) i = _
  have hsingle : (Pi.single j (1 : ℤ)) = (fun k => if k = j then (1 : ℤ) else 0) := by
    ext k
    by_cases hk : k = j <;> simp [hk]
  rw [hsingle, _Pn]
  by_cases hfirst : i = j.castSucc
  · subst i
    have hne : j.castSucc ≠ j.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hh
      omega
    simp [hne]
  · have hsucc : i = j.succ ↔ (i : ℕ) = (j : ℕ) + 1 := by
      constructor
      · intro h; exact congrArg Fin.val h
      · intro h; exact Fin.ext h
    simp only [hfirst, if_false, hsucc, zero_sub]
    split_ifs <;> rfl
open _root_.P2Mf6bd8d28 renaming h175 → _P4v
theorem _root_.P2Mf6bd8d28.h154 (q n : ℕ) (x : Fin (n + 1) → ℤ) :
    (TDef63 q (n + 1)).mulVec x =
      _root_.AFT.roundingLoad n (_root_.AFT.injectionColumn n q) (fun j => x j.castSucc, x (Fin.last n)) := by
  funext i
  have hedge (j : Fin n) : TDef63 q (n + 1) i j.castSucc =
      LinearMap.toMatrix' (_root_.AFT.pathIncidence n) i j := by
    rw [_P4v]
    simp [TDef63, show (j : ℕ) + 1 < n + 1 by omega]
  have hlast : TDef63 q (n + 1) i (Fin.last n) = _root_.AFT.injectionColumn n q i := by
    simp [TDef63, _root_.AFT.injectionColumn]
  change (∑ j, TDef63 q (n + 1) i j * x j) = _
  rw [Fin.sum_univ_castSucc]
  simp_rw [hedge]
  rw [hlast]
  have hpath := congrFun (LinearMap.toMatrix'_mulVec (_root_.AFT.pathIncidence n)
    (fun j => x j.castSucc)) i
  change (∑ j, LinearMap.toMatrix' (_root_.AFT.pathIncidence n) i j * x j.castSucc) = _ at hpath
  rw [hpath]
  simp only [_root_.AFT.roundingLoad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.AFT.pathIncidence,
    LinearMap.coe_mk, AddHom.coe_mk]
  ring
open _root_.P2Mf6bd8d28 renaming h154 → _P4a
theorem _root_.P2Mf6bd8d28.h176 (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (i : Fin d) :
    carry q w i = w i / (q : ℤ) := by
  unfold carry
  rw [Int.floor_div_natCast, Int.floor_intCast]
open _root_.P2Mf6bd8d28 renaming h176 → _P4w
theorem _root_.P2Mf6bd8d28.h166 (q n : ℕ) (x : Fin (n + 1) → ZMod q) :
    fT63 q (n + 1) x =
      _root_.AFT.fiberLabel n q (_root_.AFT.injectionColumn n q) (fun j => x j.castSucc, x (Fin.last n)) := by
  unfold fT63 AR _root_.AFT.fiberLabel _root_.AFT.integerLabel _root_.AFT.totalCharge _root_.AFT.canonicalCarry
  simp_rw [_P4w]
  congr 1
  rw [_P4a]
  rfl
open _root_.P2Mf6bd8d28 renaming h166 → _P4m
theorem _root_.P2Mf6bd8d28.h167 {q n d : ℕ} (hd : n + 1 = d) (x : Fin d → ZMod q) :
    fT63 q d x = _root_.AFT.fiberLabel n q (_root_.AFT.injectionColumn n q)
      (fun j => x ((finCongr hd) j.castSucc), x ((finCongr hd) (Fin.last n))) := by
  subst d
  exact _P4m q n x
open _root_.P2Mf6bd8d28 renaming h167 → _P4n
theorem _root_.P2Mf6bd8d28.h184 {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] [Nonempty {x // P x}] (x : α) :
    ((_root_.AFT.FiniteDist.uniform {x // P x}).map Subtype.val).weight x =
      unifOn (Finset.univ.filter P) x := by
  classical
  rw [_root_.AFT.FiniteDist.map_weight]
  simp only [_root_.AFT.FiniteDist.uniform_weight]
  by_cases hx : P x
  · have heq (a : {x // P x}) : (a : α) = x ↔ a = ⟨x, hx⟩ := by
      simp only [Subtype.ext_iff]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [unifOn, hx, Fintype.card_subtype]
  · have hne (a : {x // P x}) : (a : α) ≠ x := by
      intro h
      apply hx
      exact h ▸ a.property
    simp [hne, unifOn, hx]
open _root_.P2Mf6bd8d28 renaming h184 → _P54
theorem _root_.P2Mf6bd8d28.h183 {q d : ℕ} [NeZero q]
    (label : (Fin d → ZMod q) → ZMod q)
    [Nonempty {x // label x = 0}] (x : Fin d → ZMod q) :
    ((_root_.AFT.FiniteDist.uniform {x // label x = 0}).map Subtype.val).weight x =
      unifZeroFiber (fun y => (fun _ : Fin 1 => label y)) x := by
  rw [_P54]
  unfold unifZeroFiber
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    funext i
    exact h
  · intro h
    exact congrFun h 0
open _root_.P2Mf6bd8d28 renaming h183 → _P53
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h154 → _P4a
open _root_.P2Mf6bd8d28 renaming h166 → _P4m
open _root_.P2Mf6bd8d28 renaming h167 → _P4n
open _root_.P2Mf6bd8d28 renaming h175 → _P4v
open _root_.P2Mf6bd8d28 renaming h176 → _P4w
open _root_.P2Mf6bd8d28 renaming h183 → _P53
open _root_.P2Mf6bd8d28 renaming h184 → _P54
end
open _root_.P2Mf6bd8d28 renaming h154 → _P4a
open _root_.P2Mf6bd8d28 renaming h166 → _P4m
open _root_.P2Mf6bd8d28 renaming h167 → _P4n
open _root_.P2Mf6bd8d28 renaming h175 → _P4v
open _root_.P2Mf6bd8d28 renaming h176 → _P4w
open _root_.P2Mf6bd8d28 renaming h183 → _P53
open _root_.P2Mf6bd8d28 renaming h184 → _P54
namespace AFT.canonicalEndpointEquiv
end AFT.canonicalEndpointEquiv
namespace AFT.pathIncidence
end AFT.pathIncidence
namespace AFT.uniformZeroFiber
end AFT.uniformZeroFiber
namespace CurrentAFT.CurrentZeroFiber
end CurrentAFT.CurrentZeroFiber
namespace CurrentAFT.CurrentZeroFiber.label
end CurrentAFT.CurrentZeroFiber.label
namespace CurrentAFT.CurrentZeroFiber.pullback
end CurrentAFT.CurrentZeroFiber.pullback
namespace CurrentAFT.CurrentZeroFiber.rawPullback
end CurrentAFT.CurrentZeroFiber.rawPullback
namespace CurrentAFT.CurrentZeroFiber.uniformFiber
end CurrentAFT.CurrentZeroFiber.uniformFiber
namespace InfoLossLAR.WorstCase.TDef63
end InfoLossLAR.WorstCase.TDef63
namespace InfoLossLAR.WorstCase.unifOn
end InfoLossLAR.WorstCase.unifOn
namespace InfoLossLAR.WorstCase.zeroFiber63
end InfoLossLAR.WorstCase.zeroFiber63
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentAFT.Parameters.base CurrentAFT.Parameters.bodySize
  CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.Integration
open AFT CurrentAFT.CurrentAffineGeometry
attribute [local instance] _root_.InfoLossLAR.WorstCase.Integration.instNeZeroNatModulus_integration9_9
theorem _root_.P2Mf6bd8d28.h162 (security : ℕ)
    (x : _root_.CurrentAFT.CurrentZeroFiber.Word security) :
    _root_.CurrentAFT.CurrentZeroFiber.label security x =
      fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) x := by
  unfold _root_.CurrentAFT.CurrentZeroFiber.label
  rw [_P4n (_root_.CurrentAFT.LobsterCoordinates.current_vertex_count security) x]
  apply congrArg (_root_.AFT.fiberLabel (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)
    (_root_.AFT.injectionColumn (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)))
  apply Prod.ext
  · funext j
    apply congrArg x
    apply Fin.ext
    rfl
  · apply congrArg x
    apply Fin.ext
    rfl
open _root_.P2Mf6bd8d28 renaming h162 → _P4i
theorem _root_.P2Mf6bd8d28.h163 (security : ℕ)
    (x : _root_.CurrentAFT.CurrentZeroFiber.Word security) :
    (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security).weight x =
      unifZeroFiber
        (fun y => (fun _ : Fin 1 =>
          fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) y)) x := by
  letI : Nonempty {y : _root_.CurrentAFT.CurrentZeroFiber.Word security //
      _root_.CurrentAFT.CurrentZeroFiber.label security y = 0} :=
    _root_.CurrentAFT.CurrentZeroFiber.fiberNonempty security
  change ((_root_.AFT.FiniteDist.uniform {y : _root_.CurrentAFT.CurrentZeroFiber.Word security //
      _root_.CurrentAFT.CurrentZeroFiber.label security y = 0}).map Subtype.val).weight x = _
  rw [_P53]
  have hlabel :
      (fun y : _root_.CurrentAFT.CurrentZeroFiber.Word security =>
        (fun _ : Fin 1 => _root_.CurrentAFT.CurrentZeroFiber.label security y)) =
      (fun y => (fun _ : Fin 1 =>
        fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) y)) := by
    funext y i
    exact _P4i security y
  rw [hlabel]
open _root_.P2Mf6bd8d28 renaming h163 → _P4j
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h162 → _P4i
open _root_.P2Mf6bd8d28 renaming h163 → _P4j
end
open _root_.P2Mf6bd8d28 renaming h162 → _P4i
open _root_.P2Mf6bd8d28 renaming h163 → _P4j
namespace InfoLossLAR.WorstCase.avg
end InfoLossLAR.WorstCase.avg
namespace InfoLossLAR.WorstCase.transportLaw
end InfoLossLAR.WorstCase.transportLaw
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.Integration
open AFT GaussianSource
open CurrentAFT.CurrentSourceProtection
attribute [local instance] _root_.InfoLossLAR.WorstCase.Integration.currentModulusNeZero
theorem _root_.P2Mf6bd8d28.h157 {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (security : ℕ)
    (S : Ω → Matrix (Fin (_root_.CurrentAFT.Parameters.dimension security))
      (Fin (_root_.CurrentAFT.Parameters.dimension security)) ℤ ×
        (Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ))
    (x : Fin (_root_.CurrentAFT.Parameters.dimension security) → ZMod (_root_.CurrentAFT.Parameters.modulus security)) :
    ((_root_.AFT.FiniteDist.uniform Ω).mix (fun seed =>
      _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenGaussianOutput security
        (fun input => (_root_.AFT.FiniteDist.uniform Unit).map (fun _ index =>
          (((S seed).1.mulVec input index + (S seed).2 index : ℤ) :
            ZMod (_root_.CurrentAFT.Parameters.modulus security)))))).weight x =
      transportLaw S (chiG (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.CurrentAFT.Parameters.dimension security) (_root_.CurrentAFT.CurrentSourceProtection.width security)) x := by
  have hsource : (_root_.AFT.GaussianSource.residueGaussian (_root_.CurrentAFT.Parameters.dimension security)
      (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security)).weight =
      chiG (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) (_root_.CurrentAFT.CurrentSourceProtection.width security) := by
    funext error
    exact _P4z _ _ _ _ error
  rw [← hsource, _P52]
  simp_rw [_P4f]
open _root_.P2Mf6bd8d28 renaming h157 → _P4d
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h157 → _P4d
end
open _root_.P2Mf6bd8d28 renaming h157 → _P4d
section
set_option autoImplicit false
namespace Integration9_9.FairBitPadding
open InfoLossLAR.WorstCase
theorem _root_.P2Mf6bd8d28.h589 {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [e.sum_comp, Fintype.card_congr e]
open _root_.P2Mf6bd8d28 renaming h589 → _Pgd
theorem _root_.P2Mf6bd8d28.h591 {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : avg (fun p : α × β => f p.1) = avg f := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum]
  field_simp
open _root_.P2Mf6bd8d28 renaming h591 → _Pgf
theorem _root_.P2Mf6bd8d28.h593 (n extra : ℕ) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin (n+extra) → Bool => f (fun i => tape (Fin.castAdd extra i))) = avg f := by
  calc
    _ = avg (fun tape => (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1)
          (_root_.Integration9_9.FairBitPadding.splitEquiv n extra tape)) := rfl
    _ = avg (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1) :=
      _Pgd (_root_.Integration9_9.FairBitPadding.splitEquiv n extra) (fun p => f p.1)
    _ = avg f := _Pgf f
open _root_.P2Mf6bd8d28 renaming h593 → _Pgh
theorem _root_.P2Mf6bd8d28.h592 {n m : ℕ} (h : n ≤ m) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin m → Bool => f (fun i => tape (Fin.castLE h i))) = avg f := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa only [Fin.castLE, Fin.castAdd] using _Pgh n extra f
open _root_.P2Mf6bd8d28 renaming h592 → _Pgg
theorem _root_.P2Mf6bd8d28.h590 (n : ℕ) (f : (Fin n → Fin 2) → ℝ) :
    avg (fun tape : Fin n → Bool => f (fun i => finTwoEquiv.symm (tape i))) = avg f := by
  exact _Pgd (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm) f
open _root_.P2Mf6bd8d28 renaming h590 → _Pge
theorem _root_.P2Mf6bd8d28.h594 {q d n m : ℕ} [NeZero q] (h : n ≤ m)
    (sampler : (Fin n → Fin 2) →
      Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (source : (Fin d → ZMod q) → ℝ) :
    transportLaw
      (fun tape : Fin m → Bool =>
        sampler (fun i => finTwoEquiv.symm (tape (Fin.castLE h i)))) source =
      transportLaw sampler source := by
  funext output
  let test : (Fin n → Fin 2) → ℝ := fun tape =>
    ∑ error : Fin d → ZMod q,
      if evalAffine (sampler tape).1 (sampler tape).2 error = output then source error else 0
  change avg (fun tape : Fin m → Bool =>
    test (fun i => finTwoEquiv.symm (tape (Fin.castLE h i)))) = avg test
  calc
    _ = avg (fun tape : Fin n → Bool => test (fun i => finTwoEquiv.symm (tape i))) :=
      _Pgg h (fun tape => test (fun i => finTwoEquiv.symm (tape i)))
    _ = avg test := _Pge n test
open _root_.P2Mf6bd8d28 renaming h594 → _Pgi
end Integration9_9.FairBitPadding
open _root_.P2Mf6bd8d28 renaming h589 → _Pgd
open _root_.P2Mf6bd8d28 renaming h590 → _Pge
open _root_.P2Mf6bd8d28 renaming h591 → _Pgf
open _root_.P2Mf6bd8d28 renaming h592 → _Pgg
open _root_.P2Mf6bd8d28 renaming h593 → _Pgh
open _root_.P2Mf6bd8d28 renaming h594 → _Pgi
end
open _root_.P2Mf6bd8d28 renaming h589 → _Pgd
open _root_.P2Mf6bd8d28 renaming h590 → _Pge
open _root_.P2Mf6bd8d28 renaming h591 → _Pgf
open _root_.P2Mf6bd8d28 renaming h592 → _Pgg
open _root_.P2Mf6bd8d28 renaming h593 → _Pgh
open _root_.P2Mf6bd8d28 renaming h594 → _Pgi
namespace CurrentAFT.ActualConstructiveSampler
end CurrentAFT.ActualConstructiveSampler
namespace Integration9_9
end Integration9_9
namespace Integration9_9.FairBitPadding
end Integration9_9.FairBitPadding
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace InfoLossLAR.WorstCase.Integration
open AFT CurrentAFT
open scoped BigOperators Classical
attribute [local irreducible] CurrentAFT.Parameters.base CurrentAFT.Parameters.bodySize CurrentAFT.Parameters.dimension CurrentAFT.Parameters.legCount
attribute [local instance] _root_.InfoLossLAR.WorstCase.Integration.actualSamplerModulusNeZero
theorem _root_.P2Mf6bd8d28.h156 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (security : ℕ) (x : _root_.CurrentAFT.CurrentZeroFiber.Word security) :
    (_root_.CurrentAFT.ActualConstructiveSampler.law security order data).weight x =
      transportLaw (_root_.InfoLossLAR.WorstCase.Integration.actualSampler order data security)
        (chiG (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security)
          (_root_.CurrentAFT.CurrentSourceProtection.width security)) x := by
  rw [_Pr]
  simpa only [_root_.InfoLossLAR.WorstCase.Integration.actualSampler, _root_.CurrentAFT.PublicAffinePipeline.gaussianChannel] using
    _P4d security (_root_.InfoLossLAR.WorstCase.Integration.actualSampler order data security) x
open _root_.P2Mf6bd8d28 renaming h156 → _P4c
theorem _root_.P2Mf6bd8d28.h155 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (security : ℕ) :
    sdist (transportLaw (_root_.InfoLossLAR.WorstCase.Integration.actualSampler order data security)
      (chiG (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security)
        (_root_.CurrentAFT.CurrentSourceProtection.width security)))
      (unifZeroFiber (fun x => (fun _ : Fin 1 =>
        fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) x))) =
      (_root_.CurrentAFT.ActualConstructiveSampler.law security order data).totalVariation
        (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security) := by
  have ht := funext (_P4c order data security)
  have hu := funext (_P4j security)
  rw [← ht, ← hu]
  exact _P51 _ _
open _root_.P2Mf6bd8d28 renaming h155 → _P4b
theorem _root_.P2Mf6bd8d28.h174 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (m : Polynomial ℕ) (hbits : ∀ security, (_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security : ℕ) :
    sdist (transportLaw (_root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler order data m hbits security)
      (chiG (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security)
        (_root_.CurrentAFT.CurrentSourceProtection.width security)))
      (unifZeroFiber (fun x => (fun _ : Fin 1 =>
        fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) x))) =
      (_root_.CurrentAFT.ActualConstructiveSampler.law security order data).totalVariation
        (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security) := by
  unfold _root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler
  rw [_Pgi (hbits security)]
  exact _P4b order data security
open _root_.P2Mf6bd8d28 renaming h174 → _P4u
theorem _root_.P2Mf6bd8d28.h165 (accuracyOrder : ℕ) :
    ∃ data : _root_.CurrentAFT.BinaryFullResponseData.Data (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder),
      _root_.CurrentAFT.BinaryFullResponseData.Correct data ∧
      ∃ m : Polynomial ℕ, ∃ hbits : ∀ security, (_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security,
        (∀ security tape,
          IsUnit (matModq (_root_.CurrentAFT.Parameters.modulus security)
            (_root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) data m hbits security tape).1).det) ∧
        (∃ cutoff : ℕ, ∀ security ≥ cutoff,
          sdist (transportLaw
            (_root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) data m hbits security)
            (chiG (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security)
              (_root_.CurrentAFT.CurrentSourceProtection.width security)))
            (unifZeroFiber (fun x => (fun _ : Fin 1 =>
              fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) x))) ≤
              (security : ℝ) ^ (-(accuracyOrder : ℝ))) := by
  obtain ⟨data,hdata⟩ := _P16
    (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
  obtain ⟨m,hbits⟩ := _P3i
  obtain ⟨cutoff,haccuracy⟩ := ActualConstructiveSampler.accuracy_eventually accuracyOrder data hdata
  refine ⟨data, hdata, m, hbits, ?_, cutoff, ?_⟩
  · intro security tape
    have hinv := _Pt security
      (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) data
      (fun i => finTwoEquiv.symm (tape (Fin.castLE (hbits security) i)))
    exact (Matrix.isUnit_iff_isUnit_det _).mp hinv
  · intro security hsecurity
    rw [_P4u]
    exact haccuracy security hsecurity
open _root_.P2Mf6bd8d28 renaming h165 → _P4l
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h155 → _P4b
open _root_.P2Mf6bd8d28 renaming h156 → _P4c
open _root_.P2Mf6bd8d28 renaming h165 → _P4l
open _root_.P2Mf6bd8d28 renaming h174 → _P4u
end
open _root_.P2Mf6bd8d28 renaming h155 → _P4b
open _root_.P2Mf6bd8d28 renaming h156 → _P4c
open _root_.P2Mf6bd8d28 renaming h165 → _P4l
open _root_.P2Mf6bd8d28 renaming h174 → _P4u
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase.Integration
theorem _root_.P2Mf6bd8d28.h173 (lam : ℕ) : _root_.CurrentAFT.Parameters.sourceWidth lam = famσ lam := rfl
open _root_.P2Mf6bd8d28 renaming h173 → _P4t
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h173 → _P4t
end
open _root_.P2Mf6bd8d28 renaming h173 → _P4t
namespace InfoLossLAR.WorstCase.Integration.actualSampler
end InfoLossLAR.WorstCase.Integration.actualSampler
namespace InfoLossLAR.WorstCase.famL
end InfoLossLAR.WorstCase.famL
namespace InfoLossLAR.WorstCase.famd
end InfoLossLAR.WorstCase.famd
namespace InfoLossLAR.WorstCase.famq
end InfoLossLAR.WorstCase.famq
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace InfoLossLAR.WorstCase.Integration
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h178 {Ω : Type*} [Fintype Ω] {q q' d d' : ℕ}
    [NeZero q] [NeZero q'] (hq : q = q') (hd : d = d') (width : ℝ)
    (sampler : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) :
    sdist (transportLaw (_root_.InfoLossLAR.WorstCase.Integration.reindexAffine hd sampler) (chiG q' d' width))
      (unifZeroFiber (fun x => fun _ : Fin 1 => fT63 q' d' x)) =
    sdist (transportLaw sampler (chiG q d width))
      (unifZeroFiber (fun x => fun _ : Fin 1 => fT63 q d x)) := by
  cases hd
  cases hq
  rfl
open _root_.P2Mf6bd8d28 renaming h178 → _P4y
theorem _root_.P2Mf6bd8d28.h177 {Ω : Type*} {q q' d d' : ℕ}
    (hq : q = q') (hd : d = d')
    (sampler : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) (tape : Ω) :
    IsUnit (matModq q' (_root_.InfoLossLAR.WorstCase.Integration.reindexAffine hd sampler tape).1).det ↔
      IsUnit (matModq q (sampler tape).1).det := by
  cases hd
  cases hq
  rfl
open _root_.P2Mf6bd8d28 renaming h177 → _P4x
attribute [local instance] _root_.InfoLossLAR.WorstCase.Integration.fixedFamilySamplerLocalModulusNeZero
theorem _root_.P2Mf6bd8d28.h170 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (m : Polynomial ℕ)
    (hbits : ∀ security, (_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (security : ℕ) :
    sdist (transportLaw (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security)
      (chiG (famq security) (famd security) (famσ security : ℝ)))
      (unifZeroFiber (famLabel security)) =
      (_root_.CurrentAFT.ActualConstructiveSampler.law security order data).totalVariation
        (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security) := by
  unfold famLabel
  have hw : _root_.CurrentAFT.CurrentSourceProtection.width security = (famσ security : ℝ) := by
    unfold _root_.CurrentAFT.CurrentSourceProtection.width
    rw [_P4t]
  calc
    _ = sdist (transportLaw (_root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler order data m hbits security)
        (chiG (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security)
          (_root_.CurrentAFT.CurrentSourceProtection.width security)))
        (unifZeroFiber (fun x => fun _ : Fin 1 =>
          fT63 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.dimension security) x)) := by
      simpa only [_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler,hw] using
        _P4y (_root_.InfoLossLAR.WorstCase.Integration.local_modulus_eq security) (_root_.InfoLossLAR.WorstCase.Integration.local_dimension_eq security)
          (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler order data m hbits security)
    _ = _ := _P4u order data m hbits security
open _root_.P2Mf6bd8d28 renaming h170 → _P4q
theorem _root_.P2Mf6bd8d28.h164 (accuracyOrder : ℕ) :
    ∃ data : _root_.CurrentAFT.BinaryFullResponseData.Data (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder),
      _root_.CurrentAFT.BinaryFullResponseData.Correct data ∧
      ∃ m : Polynomial ℕ,
      ∃ hbits : ∀ security, (_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security,
        (∀ security tape,
          IsUnit (matModq (famq security)
            (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
              data m hbits security tape).1).det) ∧
        (∃ cutoff : ℕ, ∀ security ≥ cutoff,
          sdist (transportLaw
            (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) data m hbits security)
            (chiG (famq security) (famd security) (famσ security : ℝ)))
            (unifZeroFiber (famLabel security)) ≤ (security : ℝ) ^ (-(accuracyOrder : ℝ))) := by
  obtain ⟨data,hdata,m,hbits,hunit,cutoff,haccuracy⟩ := _P4l accuracyOrder
  refine ⟨data,hdata,m,hbits,?_,cutoff,?_⟩
  · intro security tape
    unfold _root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler
    exact (_P4x (_root_.InfoLossLAR.WorstCase.Integration.local_modulus_eq security) (_root_.InfoLossLAR.WorstCase.Integration.local_dimension_eq security)
      (_root_.InfoLossLAR.WorstCase.Integration.paddedActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) data m hbits security) tape).mpr
        (hunit security tape)
  · intro security hsecurity
    rw [_P4q]
    simpa only [_P4u] using haccuracy security hsecurity
open _root_.P2Mf6bd8d28 renaming h164 → _P4k
end InfoLossLAR.WorstCase.Integration
open _root_.P2Mf6bd8d28 renaming h164 → _P4k
open _root_.P2Mf6bd8d28 renaming h170 → _P4q
open _root_.P2Mf6bd8d28 renaming h177 → _P4x
open _root_.P2Mf6bd8d28 renaming h178 → _P4y
end
open _root_.P2Mf6bd8d28 renaming h164 → _P4k
open _root_.P2Mf6bd8d28 renaming h170 → _P4q
open _root_.P2Mf6bd8d28 renaming h177 → _P4x
open _root_.P2Mf6bd8d28 renaming h178 → _P4y
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2PlatformSerialization
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open QAlgorithms.Complexity
open Polynomial
theorem _root_.P2Mf6bd8d28.h825 {f : Str → Str} (h : Poly f) : PolyTimeComputable f := by
  let P := (BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram
  exact ⟨(P.congr f (fun _ => rfl)).stock⟩
open _root_.P2Mf6bd8d28 renaming h825 → _Pmx
@[fun_prop] theorem _root_.P2Mf6bd8d28.h828 : Poly _root_.Integration9_9.TM2PlatformSerialization.readUnary := by
  unfold _root_.Integration9_9.TM2PlatformSerialization.readUnary
  have h : Poly (fun xs : Str => (xs, inputWidth xs + 1)) := by fun_prop
  exact Poly.pair (Poly.comp parser_take_poly h) (Poly.comp parser_drop_poly h)
open _root_.P2Mf6bd8d28 renaming h828 → _Pn0
theorem _root_.P2Mf6bd8d28.h829 (xs : Str) : (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2.length ≤ xs.length := by
  simp only [_root_.Integration9_9.TM2PlatformSerialization.readUnary, List.length_drop]
  omega
open _root_.P2Mf6bd8d28 renaming h829 → _Pn1
@[fun_prop] theorem _root_.P2Mf6bd8d28.h831 : Poly _root_.Integration9_9.TM2PlatformSerialization.unarySlots := by
  unfold _root_.Integration9_9.TM2PlatformSerialization.unarySlots
  apply Poly.list_map
  · fun_prop
  · have h : Poly (fun xs : Str => (xs, inputWidth xs)) := by fun_prop
    exact Poly.comp parser_take_poly h
open _root_.P2Mf6bd8d28 renaming h831 → _Pn3
@[fun_prop] theorem _root_.P2Mf6bd8d28.h824 {α : Type} [Coding α] [Inhabited α] :
    Poly (_root_.Integration9_9.TM2PlatformSerialization.lengthToken : List α → Str) := by
  unfold _root_.Integration9_9.TM2PlatformSerialization.lengthToken
  fun_prop
open _root_.P2Mf6bd8d28 renaming h824 → _Pmw
@[fun_prop] theorem _root_.P2Mf6bd8d28.h830 : Poly _root_.Integration9_9.TM2PlatformSerialization.serializeWords := by
  unfold _root_.Integration9_9.TM2PlatformSerialization.serializeWords
  have hf : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩
  exact Poly.comp Poly.list_append (Poly.pair _Pmw hf)
open _root_.P2Mf6bd8d28 renaming h830 → _Pn2
section RepeatedParser
variable {α : Type} [Coding α] [Inhabited α]
variable (read : Str → Str × α)
@[fun_prop] theorem _root_.P2Mf6bd8d28.h826 (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) : Poly (_root_.Integration9_9.TM2PlatformSerialization.readList read) := by
  unfold _root_.Integration9_9.TM2PlatformSerialization.readList
  have hs : Poly (fun xs : Str =>
      (_root_.Integration9_9.TM2PlatformSerialization.unarySlots xs).foldl (_root_.Integration9_9.TM2PlatformSerialization.parseStep read) ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2, ([] : List α))) :=
    by
      have h : Poly (fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.unarySlots xs, ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2, ([] : List α)))) :=
        Poly.pair _Pn3 (Poly.pair (Poly.comp Poly.snd _Pn0) (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := Str) ([] : List α)))
      exact Poly.comp (_root_.Integration9_9.TM2PlatformSerialization.parserFold_poly read hr hrest) h
  exact Poly.pair (Poly.comp Poly.fst hs)
    (Poly.comp parser_reverse_poly (Poly.comp Poly.snd hs))
open _root_.P2Mf6bd8d28 renaming h826 → _Pmy
lemma _root_.P2Mf6bd8d28.h827 (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) (xs : Str) :
    (_root_.Integration9_9.TM2PlatformSerialization.readList read xs).1.length ≤ xs.length := by
  exact (_root_.Integration9_9.TM2PlatformSerialization.parser_fold_bounds read hr hrest (_root_.Integration9_9.TM2PlatformSerialization.unarySlots xs) (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2 []).1.trans
    (_Pn1 xs)
open _root_.P2Mf6bd8d28 renaming h827 → _Pmz
end RepeatedParser
open _root_.P2Mf6bd8d28 renaming h826 → _Pmy
open _root_.P2Mf6bd8d28 renaming h827 → _Pmz
end Integration9_9.TM2PlatformSerialization
open _root_.P2Mf6bd8d28 renaming h824 → _Pmw
open _root_.P2Mf6bd8d28 renaming h825 → _Pmx
open _root_.P2Mf6bd8d28 renaming h826 → _Pmy
open _root_.P2Mf6bd8d28 renaming h827 → _Pmz
open _root_.P2Mf6bd8d28 renaming h828 → _Pn0
open _root_.P2Mf6bd8d28 renaming h829 → _Pn1
open _root_.P2Mf6bd8d28 renaming h830 → _Pn2
open _root_.P2Mf6bd8d28 renaming h831 → _Pn3
end
open _root_.P2Mf6bd8d28 renaming h824 → _Pmw
open _root_.P2Mf6bd8d28 renaming h825 → _Pmx
open _root_.P2Mf6bd8d28 renaming h826 → _Pmy
open _root_.P2Mf6bd8d28 renaming h827 → _Pmz
open _root_.P2Mf6bd8d28 renaming h828 → _Pn0
open _root_.P2Mf6bd8d28 renaming h829 → _Pn1
open _root_.P2Mf6bd8d28 renaming h830 → _Pn2
open _root_.P2Mf6bd8d28 renaming h831 → _Pn3
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineBudget
open QAlgorithms.Complexity InfoLossLAR.WorstCase LARPlatformEncoding
theorem _root_.P2Mf6bd8d28.h820 (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)
open _root_.P2Mf6bd8d28 renaming h820 → _Pms
private theorem _root_.P2Mf6bd8d28.h836 {α : Type} (code : α → Str)
    (hcode : ∀ x,0 < (code x).length) (values : List α) : values.length ≤ (values.flatMap code).length := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have hx:=hcode x
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega
open _root_.P2Mf6bd8d28 renaming h836 → _Pn8
theorem _root_.P2Mf6bd8d28.h822 {q d N count : ℕ}
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q)×(Fin d → ZMod q)) :
    count ≤ (encTable table).length := by
  let code := fun sample : Matrix (Fin d) (Fin N) (ZMod q)×(Fin d → ZMod q)=>
    encPair (encMat encZM sample.1) (encVec encZM sample.2)
  have hc (sample : Matrix (Fin d) (Fin N) (ZMod q)×(Fin d → ZMod q)) : 0 < (code sample).length := by
    have h:=_root_.Integration9_9.LARPlatformEncoding.encB_length_pos (encMat encZM sample.1).length
    simp only [code,encPair,encS,List.length_append]
    omega
  have h:=_Pn8 code hc (List.ofFn table)
  simp only [List.length_ofFn] at h
  change count ≤ (encL code (List.ofFn table)).length
  simp only [encL,List.length_append]
  omega
open _root_.P2Mf6bd8d28 renaming h822 → _Pmu
theorem _root_.P2Mf6bd8d28.h821 (security : ℕ) (pp table : Str) :
    security ≤ (encInput security pp table).length := by
  simp only [encInput,encS,unary,List.length_append,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h821 → _Pmt
theorem _root_.P2Mf6bd8d28.h823 (security : ℕ) (pp table : Str) :
    table.length ≤ (encInput security pp table).length := by
  simp only [encInput,encS,List.length_append]
  omega
open _root_.P2Mf6bd8d28 renaming h823 → _Pmv
theorem _root_.P2Mf6bd8d28.h819 (m : Polynomial ℕ) (n : ℕ) : (_root_.Integration9_9.TM2NativeAffineBudget.coins m).eval n=n*m.eval n := by
  simp only [_root_.Integration9_9.TM2NativeAffineBudget.coins,Polynomial.eval_mul,Polynomial.eval_X]
open _root_.P2Mf6bd8d28 renaming h819 → _Pmr
theorem _root_.P2Mf6bd8d28.h818 (m : Polynomial ℕ) {q d N count : ℕ} (security : ℕ) (pp : Str)
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q)×(Fin d → ZMod q)) :
    count*m.eval security ≤ (_root_.Integration9_9.TM2NativeAffineBudget.coins m).eval (encInput security pp (encTable table)).length := by
  rw [_Pmr]
  exact Nat.mul_le_mul
    ((_Pmu table).trans (_Pmv security pp (encTable table)))
    (_Pms m (_Pmt security pp (encTable table)))
open _root_.P2Mf6bd8d28 renaming h818 → _Pmq
end Integration9_9.TM2NativeAffineBudget
open _root_.P2Mf6bd8d28 renaming h818 → _Pmq
open _root_.P2Mf6bd8d28 renaming h819 → _Pmr
open _root_.P2Mf6bd8d28 renaming h820 → _Pms
open _root_.P2Mf6bd8d28 renaming h821 → _Pmt
open _root_.P2Mf6bd8d28 renaming h822 → _Pmu
open _root_.P2Mf6bd8d28 renaming h823 → _Pmv
open _root_.P2Mf6bd8d28 renaming h836 → _Pn8
end
open _root_.P2Mf6bd8d28 renaming h818 → _Pmq
open _root_.P2Mf6bd8d28 renaming h819 → _Pmr
open _root_.P2Mf6bd8d28 renaming h820 → _Pms
open _root_.P2Mf6bd8d28 renaming h821 → _Pmt
open _root_.P2Mf6bd8d28 renaming h822 → _Pmu
open _root_.P2Mf6bd8d28 renaming h823 → _Pmv
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase
theorem _root_.P2Mf6bd8d28.h422 {α : Type*} [Fintype α]
    (P Q test : α → ℝ) (hmass : ∑ x, P x = ∑ x, Q x)
    (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    |(∑ x, P x * test x) - ∑ x, Q x * test x| ≤ sdist P Q := by
  have hzero : ∑ x, (P x - Q x) = 0 := by
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  have hcenter : (∑ x, P x * test x) - ∑ x, Q x * test x =
      ∑ x, (P x - Q x) * (test x - 1 / 2) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [hcenter]
  calc
    |∑ x, (P x - Q x) * (test x - 1 / 2)| ≤
      ∑ x, |(P x - Q x) * (test x - 1 / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |P x - Q x| * (1 / 2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr (by constructor <;> linarith [(htest x).1, (htest x).2])
    _ = sdist P Q := by
      unfold sdist
      rw [← Finset.sum_mul]
      ring
open _root_.P2Mf6bd8d28 renaming h422 → _Pbq
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h422 → _Pbq
end
open _root_.P2Mf6bd8d28 renaming h422 → _Pbq
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h325 (D : Family) (w : Str) :
    0 ≤ acceptProb D w ∧ acceptProb D w ≤ 1 := by
  have hmass : (∑ y : Bits (w.length + (D.anc w.length + 1)),
      ‖runLayered (D.circ w.length) (basisInput (toBits w)) y‖ ^ 2) = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (_root_.InfoLossLAR.WorstCase.runLayered_mass (D.circ w.length) (basisInput (toBits w))).trans
        (_root_.InfoLossLAR.WorstCase.basisInput_mass (a := D.anc w.length) (toBits w))
  unfold acceptProb
  constructor
  · apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> positivity
  · calc
      _ ≤ ∑ y : Bits (w.length + (D.anc w.length + 1)),
        ‖runLayered (D.circ w.length) (basisInput (toBits w)) y‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro y hy
          split_ifs <;> first | exact le_rfl | positivity
      _ = 1 := hmass
open _root_.P2Mf6bd8d28 renaming h325 → _P91
theorem _root_.P2Mf6bd8d28.h502 {α : Type*} [Fintype α]
    (P Q : α → ℝ) (hmass : ∑ x, P x = ∑ x, Q x)
    (D : Family) (input : α → Str) :
    |(∑ x, P x * acceptProb D (input x)) -
      ∑ x, Q x * acceptProb D (input x)| ≤ sdist P Q :=
  _Pbq P Q (fun x => acceptProb D (input x)) hmass
    (fun x => _P91 D (input x))
open _root_.P2Mf6bd8d28 renaming h502 → _Pdy
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h325 → _P91
open _root_.P2Mf6bd8d28 renaming h502 → _Pdy
end
open _root_.P2Mf6bd8d28 renaming h325 → _P91
open _root_.P2Mf6bd8d28 renaming h502 → _Pdy
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h558 {α : Type*} [Fintype α]
    (P Q : _root_.AFT.FiniteDist α) (t : ℕ) :
    sdist (_root_.AFT.FiniteDist.independent (fun _ : Fin t => P)).weight
      (_root_.AFT.FiniteDist.independent (fun _ : Fin t => Q)).weight ≤
        (t : ℝ) * sdist P.weight Q.weight := by
  have h := AFT.FiniteDist.l1_independent_fin_le t
    (fun _ : Fin t => P) (fun _ : Fin t => Q)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold sdist
  calc
    (1 / 2) * _ ≤ (1 / 2) * ((t : ℝ) * ∑ a, |P.weight a - Q.weight a|) := by
      exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring
open _root_.P2Mf6bd8d28 renaming h558 → _Pfi
theorem _root_.P2Mf6bd8d28.h340 {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℝ) (error : ℝ) (herror : ∀ x, |f x - g x| ≤ error) :
    |avg f - avg g| ≤ error := by
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : |(∑ x, f x) - ∑ x, g x| ≤ (Fintype.card α : ℝ) * error := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ x, (f x - g x)| ≤ ∑ x, |f x - g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : α, error := Finset.sum_le_sum (fun x hx => herror x)
      _ = _ := by simp
  unfold avg
  rw [← sub_div, abs_div, abs_of_nonneg hcard.le]
  exact (div_le_iff₀ hcard).mpr (by simpa [mul_comm] using hsum)
open _root_.P2Mf6bd8d28 renaming h340 → _P9g
theorem _root_.P2Mf6bd8d28.h500
    (D : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q]
    (P Q : _root_.AFT.FiniteDist (Fin d → ZMod q)) :
    |prRealLWE D lam pp q N d t P.weight - prRealLWE D lam pp q N d t Q.weight| ≤
      (t : ℝ) * sdist P.weight Q.weight := by
  unfold prRealLWE
  apply _P9g
  intro secret
  apply _P9g
  intro matrices
  have hmass : (∑ errors, (_root_.AFT.FiniteDist.independent (fun _ : Fin t => P)).weight errors) =
      ∑ errors, (_root_.AFT.FiniteDist.independent (fun _ : Fin t => Q)).weight errors := by
    rw [_root_.AFT.FiniteDist.sum_one, _root_.AFT.FiniteDist.sum_one]
  have htest := _Pdy
    (_root_.AFT.FiniteDist.independent (fun _ : Fin t => P)).weight
    (_root_.AFT.FiniteDist.independent (fun _ : Fin t => Q)).weight hmass D
    (fun errors => encInput lam pp (encTable
      (fun i : Fin t => (matrices i, (matrices i).mulVec secret + errors i))))
  apply le_trans _ (_Pfi P Q t)
  simpa only [_root_.AFT.FiniteDist.independent] using htest
open _root_.P2Mf6bd8d28 renaming h500 → _Pdw
theorem _root_.P2Mf6bd8d28.h335
    (D : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q]
    (P Q : _root_.AFT.FiniteDist (Fin d → ZMod q)) :
    |advLWE D lam pp q N d t P.weight - advLWE D lam pp q N d t Q.weight| ≤
      (t : ℝ) * sdist P.weight Q.weight := by
  have hreal := _Pdw D lam pp q N d t P Q
  have hforward := abs_sub_le (prRealLWE D lam pp q N d t P.weight)
    (prRealLWE D lam pp q N d t Q.weight) (prIdealLWE D lam pp q N d t)
  have hbackward := abs_sub_le (prRealLWE D lam pp q N d t Q.weight)
    (prRealLWE D lam pp q N d t P.weight) (prIdealLWE D lam pp q N d t)
  rw [abs_sub_comm (prRealLWE D lam pp q N d t Q.weight)
    (prRealLWE D lam pp q N d t P.weight)] at hbackward
  unfold advLWE
  apply abs_le.mpr
  constructor <;> linarith
open _root_.P2Mf6bd8d28 renaming h335 → _P9b
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h335 → _P9b
open _root_.P2Mf6bd8d28 renaming h340 → _P9g
open _root_.P2Mf6bd8d28 renaming h500 → _Pdw
open _root_.P2Mf6bd8d28 renaming h558 → _Pfi
end
open _root_.P2Mf6bd8d28 renaming h335 → _P9b
open _root_.P2Mf6bd8d28 renaming h340 → _P9g
open _root_.P2Mf6bd8d28 renaming h500 → _Pdw
open _root_.P2Mf6bd8d28 renaming h558 → _Pfi
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity AFT
open scoped Classical
theorem _root_.P2Mf6bd8d28.h339 {q d : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) (error : Fin d → ZMod q) :
    (_root_.InfoLossLAR.WorstCase.affineSourceLaw samp source).weight error = transportLaw samp source.weight error :=
  (_P52 samp source error).symm
open _root_.P2Mf6bd8d28 renaming h339 → _P9f
private theorem _root_.P2Mf6bd8d28.h841 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : _root_.AFT.FiniteDist α) (kernel : α → _root_.AFT.FiniteDist β) (f : β → γ) :
    (P.mix kernel).map f = P.mix (fun a => (kernel a).map f) := by
  apply _root_.AFT.FiniteDist.ext
  intro z
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.mix_weight]
  calc
    _ = ∑ b, ∑ a, if f b = z then P.weight a * (kernel a).weight b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : f b = z <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : f b = z <;> simp [h]
open _root_.P2Mf6bd8d28 renaming h841 → _Pnd
theorem _root_.P2Mf6bd8d28.h336 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) (secret : Fin N → ZMod q) :
    _root_.InfoLossLAR.WorstCase.affineLWEBlockLaw samp source secret =
      (_root_.InfoLossLAR.WorstCase.affineMatrixErrorLaw (N := N) samp source).map
        (fun draw => (draw.1, draw.1.mulVec secret + draw.2)) := by
  unfold _root_.InfoLossLAR.WorstCase.affineLWEBlockLaw _root_.InfoLossLAR.WorstCase.affineMatrixErrorLaw
  rw [_Pnd]
  apply congrArg (_root_.AFT.FiniteDist.mix (_root_.AFT.FiniteDist.uniform Ω))
  funext seed
  rw [_root_.AFT.FiniteDist.map_map]
  apply congrArg (_root_.AFT.FiniteDist.map
    ((_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod source))
  funext draw
  apply Prod.ext
  · rfl
  · simp only [evalAffine, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
open _root_.P2Mf6bd8d28 renaming h336 → _P9c
private theorem _root_.P2Mf6bd8d28.h839 {Index Input Output : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Input] [Fintype Output]
    (law : Index → _root_.AFT.FiniteDist Input) (decode : Index → Input → Output) :
    (_root_.AFT.FiniteDist.independent law).map (fun word index => decode index (word index)) =
      _root_.AFT.FiniteDist.independent (fun index => (law index).map (decode index)) := by
  apply _root_.AFT.FiniteDist.ext
  intro values
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.independent]
  have h := Fintype.prod_sum (fun index point =>
    if decode index point = values index then (law index).weight point else 0)
  apply Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro word hword
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]
open _root_.P2Mf6bd8d28 renaming h839 → _Pnb
private theorem _root_.P2Mf6bd8d28.h840 {Index First Second : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (first : Index → _root_.AFT.FiniteDist First) (second : Index → _root_.AFT.FiniteDist Second)
    (value : (Index → First × Second) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun index => (first index).prod (second index))).expectation value =
      (_root_.AFT.FiniteDist.independent first).expectation (fun left =>
        (_root_.AFT.FiniteDist.independent second).expectation
          (fun right => value (fun index => (left index, right index)))) := by
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
  rw [← (Equiv.arrowProdEquivProdArrow Index (fun _ => First) (fun _ => Second)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right hright
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, _root_.AFT.FiniteDist.prod_weight,
    Finset.prod_mul_distrib, mul_assoc]
open _root_.P2Mf6bd8d28 renaming h840 → _Pnc
private theorem _root_.P2Mf6bd8d28.h843 {Index State : Type*} [Fintype Index]
    [DecidableEq Index] [Fintype State] [Nonempty State] :
    _root_.AFT.FiniteDist.independent (fun _ : Index => _root_.AFT.FiniteDist.uniform State) =
      _root_.AFT.FiniteDist.uniform (Index → State) := by
  apply _root_.AFT.FiniteDist.ext
  intro word
  simp only [_root_.AFT.FiniteDist.independent, _root_.AFT.FiniteDist.uniform_weight, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]
open _root_.P2Mf6bd8d28 renaming h843 → _Pnf
private theorem _root_.P2Mf6bd8d28.h842 {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : (_root_.AFT.FiniteDist.uniform α).expectation f = avg f := by
  simp only [_root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.uniform_weight, avg, ← Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h842 → _Pne
theorem _root_.P2Mf6bd8d28.h498
    (D : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) :
    prRealLWE D lam pp q N d t source.weight =
      avg fun secret : Fin N → ZMod q =>
        (_root_.AFT.FiniteDist.independent (fun _ : Fin t => _root_.InfoLossLAR.WorstCase.lweBlockLaw source secret)).expectation
          (fun table => acceptProb D (encInput lam pp (encTable table))) := by
  unfold prRealLWE
  apply congrArg avg
  funext secret
  unfold _root_.InfoLossLAR.WorstCase.lweBlockLaw
  rw [← _Pnb, _root_.AFT.FiniteDist.expectation_map]
  simp only [Function.comp_def]
  have h := _Pnc
    (fun _ : Fin t => _root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q)))
    (fun _ : Fin t => source)
    (fun word => acceptProb D (encInput lam pp (encTable
      (fun i => ((word i).1, ((word i).1).mulVec secret + (word i).2)))))
  rw [_Pnf, _Pne] at h
  simpa only [_root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.independent] using h.symm
open _root_.P2Mf6bd8d28 renaming h498 → _Pdu
theorem _root_.P2Mf6bd8d28.h489
    (D : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q] :
    prIdealLWE D lam pp q N d t =
      (_root_.AFT.FiniteDist.independent (fun _ : Fin t =>
        (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod
          (_root_.AFT.FiniteDist.uniform (Fin d → ZMod q)))).expectation
        (fun table => acceptProb D (encInput lam pp (encTable table))) := by
  have h := _Pnc
    (fun _ : Fin t => _root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q)))
    (fun _ : Fin t => _root_.AFT.FiniteDist.uniform (Fin d → ZMod q))
    (fun table => acceptProb D (encInput lam pp (encTable table)))
  simp_rw [_Pnf, _Pne] at h
  simpa only [_root_.AFT.FiniteDist.independent, prIdealLWE] using h.symm
open _root_.P2Mf6bd8d28 renaming h489 → _Pdl
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h336 → _P9c
open _root_.P2Mf6bd8d28 renaming h339 → _P9f
open _root_.P2Mf6bd8d28 renaming h489 → _Pdl
open _root_.P2Mf6bd8d28 renaming h498 → _Pdu
open _root_.P2Mf6bd8d28 renaming h839 → _Pnb
open _root_.P2Mf6bd8d28 renaming h840 → _Pnc
open _root_.P2Mf6bd8d28 renaming h841 → _Pnd
open _root_.P2Mf6bd8d28 renaming h842 → _Pne
open _root_.P2Mf6bd8d28 renaming h843 → _Pnf
end
open _root_.P2Mf6bd8d28 renaming h336 → _P9c
open _root_.P2Mf6bd8d28 renaming h339 → _P9f
open _root_.P2Mf6bd8d28 renaming h489 → _Pdl
open _root_.P2Mf6bd8d28 renaming h498 → _Pdu
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped Classical
theorem _root_.P2Mf6bd8d28.h342 {α : Type*} [Fintype α] [Nonempty α]
    (test : α → ℝ) (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    0 ≤ avg test ∧ avg test ≤ 1 := by
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun x _ => (htest x).1) hc.le
  · apply (div_le_one hc).mpr
    calc
      ∑ x, test x ≤ ∑ _ : α, (1 : ℝ) := Finset.sum_le_sum fun x _ => (htest x).2
      _ = _ := by simp
open _root_.P2Mf6bd8d28 renaming h342 → _P9i
theorem _root_.P2Mf6bd8d28.h343 {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (test : α → ℝ) (point : α) (replacement : ℝ) :
    |avg test - avg (fun x => if x = point then replacement else test x)| =
      (Fintype.card α : ℝ)⁻¹ * |test point - replacement| := by
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hd (x : α) : test x - (if x = point then replacement else test x) =
      if x = point then test point - replacement else 0 := by
    by_cases h : x = point <;> simp [h]
  unfold avg
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [hd]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [abs_div, abs_of_pos hc]
  simp only [div_eq_mul_inv, mul_comm]
open _root_.P2Mf6bd8d28 renaming h343 → _P9j
theorem _root_.P2Mf6bd8d28.h496 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    |prRealLAR D lam pp q N d ℓ t label -
      _root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR D lam pp q N d ℓ t label| =
      ((q : ℝ)^N)⁻¹ * |_root_.InfoLossLAR.WorstCase.larSecretAcceptance D lam pp q N d ℓ t label 0 -
        prIdealLAR D lam pp q N d ℓ t| := by
  have h := _P9j (_root_.InfoLossLAR.WorstCase.larSecretAcceptance D lam pp q N d ℓ t label)
    0 (prIdealLAR D lam pp q N d ℓ t)
  unfold _root_.InfoLossLAR.WorstCase.larSecretAcceptance at h
  simpa only [prRealLAR, _root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR, _root_.InfoLossLAR.WorstCase.larSecretAcceptance,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using h
open _root_.P2Mf6bd8d28 renaming h496 → _Pds
theorem _root_.P2Mf6bd8d28.h497 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    |prRealLAR D lam pp q N d ℓ t label -
      _root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR D lam pp q N d ℓ t label| ≤ ((q : ℝ)^N)⁻¹ := by
  rw [_Pds]
  have hreal := _P9i
    (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
      acceptProb D (encInput lam pp (encTable
        (fun i => (matrices i, label ((matrices i).mulVec (0 : Fin N → ZMod q)))))))
    (fun _ => _P91 D _)
  have hideal := _P9i
    (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
      avg (fun labels : Fin t → Fin ℓ → ZMod q =>
        acceptProb D (encInput lam pp (encTable (fun i => (matrices i, labels i))))))
    (fun _ => _P9i _ (fun _ => _P91 D _))
  have hgap : |_root_.InfoLossLAR.WorstCase.larSecretAcceptance D lam pp q N d ℓ t label 0 -
      prIdealLAR D lam pp q N d ℓ t| ≤ 1 := by
    unfold _root_.InfoLossLAR.WorstCase.larSecretAcceptance prIdealLAR
    exact abs_le.mpr (by constructor <;> linarith)
  exact (mul_le_mul_of_nonneg_left hgap (by positivity)).trans_eq (mul_one _)
open _root_.P2Mf6bd8d28 renaming h497 → _Pdt
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h342 → _P9i
open _root_.P2Mf6bd8d28 renaming h343 → _P9j
open _root_.P2Mf6bd8d28 renaming h496 → _Pds
open _root_.P2Mf6bd8d28 renaming h497 → _Pdt
end
open _root_.P2Mf6bd8d28 renaming h342 → _P9i
open _root_.P2Mf6bd8d28 renaming h343 → _P9j
open _root_.P2Mf6bd8d28 renaming h496 → _Pds
open _root_.P2Mf6bd8d28 renaming h497 → _Pdt
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InfoLossLAR.WorstCase
open Matrix
open scoped BigOperators Classical
private theorem _root_.P2Mf6bd8d28.h846 {α : Type*} [Fintype α] [Nonempty α] (value : ℝ) :
    avg (fun _ : α => value) = value := by
  simp [avg,Fintype.card_ne_zero]
open _root_.P2Mf6bd8d28 renaming h846 → _Pni
private theorem _root_.P2Mf6bd8d28.h844 {α : Type*} [Fintype α] (first second : α → ℝ) :
    avg (fun x => first x+second x) = avg first+avg second := by
  simp only [avg,Finset.sum_add_distrib,add_div]
open _root_.P2Mf6bd8d28 renaming h844 → _Png
private theorem _root_.P2Mf6bd8d28.h848 {α : Type*} [Fintype α] (constant : ℝ) (test : α → ℝ) :
    avg (fun x => constant*test x) = constant*avg test := by
  simp only [avg,←Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h848 → _Pnk
private theorem _root_.P2Mf6bd8d28.h849 {α : Type*} [Fintype α] (test : α → ℝ) (constant : ℝ) :
    avg (fun x => test x*constant) = avg test*constant := by
  simp only [avg,←Finset.sum_mul]
  ring
open _root_.P2Mf6bd8d28 renaming h849 → _Pnl
private theorem _root_.P2Mf6bd8d28.h845 {α β : Type*} [Fintype α] [Fintype β] (test : α → β → ℝ) :
    avg (fun a => avg (fun b => test a b)) = avg (fun b => avg (fun a => test a b)) := by
  simp only [avg,←Finset.sum_div]
  rw [Finset.sum_comm]
  ring
open _root_.P2Mf6bd8d28 renaming h845 → _Pnh
private theorem _root_.P2Mf6bd8d28.h850 {α : Type*} [AddGroup α] [Fintype α]
    (shift : α) (test : α → ℝ) : avg (fun x => test (x+shift)) = avg test := by
  unfold avg
  exact congrArg (fun value : ℝ => value/(Fintype.card α : ℝ)) (Equiv.sum_comp (Equiv.addRight shift) test)
open _root_.P2Mf6bd8d28 renaming h850 → _Pnm
theorem _root_.P2Mf6bd8d28.h341 {F : Type*} [Field F] [Fintype F] {N : ℕ}
    (secret : Fin N → F) (hsecret : secret ≠ 0) (test : F → ℝ) :
    avg (fun auxiliary : Fin N → F => test (auxiliary ⬝ᵥ secret)) = avg test := by
  have hex : ∃ index, secret index ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsecret (funext h)
  obtain ⟨index,hindex⟩ := hex
  let direction : Fin N → F := Pi.single index ((secret index)⁻¹)
  have hdirection : direction ⬝ᵥ secret = 1 := by
    simp only [direction,single_dotProduct]
    exact inv_mul_cancel₀ hindex
  have htranslate (scalar : F) :
      avg (fun auxiliary : Fin N → F => test (auxiliary ⬝ᵥ secret+scalar)) =
        avg (fun auxiliary : Fin N → F => test (auxiliary ⬝ᵥ secret)) := by
    simpa only [add_dotProduct,smul_dotProduct,hdirection,smul_eq_mul,mul_one] using
      _Pnm (scalar • direction) (fun auxiliary => test (auxiliary ⬝ᵥ secret))
  calc
    _ = avg (fun scalar : F => avg (fun auxiliary : Fin N → F =>
        test (auxiliary ⬝ᵥ secret+scalar))) := by
      simp_rw [htranslate]
      rw [_Pni]
    _ = avg (fun auxiliary : Fin N → F => avg (fun scalar : F =>
        test (auxiliary ⬝ᵥ secret+scalar))) := _Pnh _
    _ = avg (fun _ : Fin N → F => avg test) := by
      congr 1
      funext auxiliary
      simpa only [add_comm] using _Pnm (auxiliary ⬝ᵥ secret) test
    _ = _ := _Pni _
open _root_.P2Mf6bd8d28 renaming h341 → _P9h
private theorem _root_.P2Mf6bd8d28.h847 {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (point : α) (real ideal : ℝ) :
    avg (fun x : α => if x=point then real else ideal) =
      (1/(Fintype.card α : ℝ))*real+(1-1/(Fintype.card α : ℝ))*ideal := by
  have hpoint : avg (fun x : α => if x=point then (1 : ℝ) else 0) = 1/(Fintype.card α : ℝ) := by
    simp [avg]
  have hfun : (fun x : α => if x=point then real else ideal) =
      (fun x => (if x=point then (1 : ℝ) else 0)*(real-ideal)+ideal) := by
    funext x
    by_cases h : x=point <;> simp [h]
  rw [hfun,_Png,_Pnl,_Pni,hpoint]
  ring
open _root_.P2Mf6bd8d28 renaming h847 → _Pnj
open QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h485 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    _root_.InfoLossLAR.WorstCase.prAlignmentLAR D lam pp q N d ℓ t label =
      (1/(q : ℝ))*_root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR D lam pp q N d ℓ t label+
        (1-1/(q : ℝ))*prIdealLAR D lam pp q N d ℓ t := by
  let ideal := prIdealLAR D lam pp q N d ℓ t
  let real := _root_.InfoLossLAR.WorstCase.larSecretAcceptance D lam pp q N d ℓ t label
  have hview (secret auxiliary : Fin N → ZMod q) :
      (avg fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
        if auxiliary ⬝ᵥ secret=1 then
          acceptProb D (encInput lam pp (encTable
            (fun i => (matrices i,label ((matrices i).mulVec secret)))))
        else avg fun labels : Fin t → Fin ℓ → ZMod q =>
          acceptProb D (encInput lam pp (encTable (fun i => (matrices i,labels i))))) =
        if auxiliary ⬝ᵥ secret=1 then real secret else ideal := by
    by_cases h : auxiliary ⬝ᵥ secret=1
    · simp only [if_pos h]
      rfl
    · simp only [if_neg h]
      rfl
  have hsecret (secret : Fin N → ZMod q) :
      (avg fun auxiliary : Fin N → ZMod q =>
        if auxiliary ⬝ᵥ secret=1 then real secret else ideal) =
      (1/(q : ℝ))*(if secret=0 then ideal else real secret)+(1-1/(q : ℝ))*ideal := by
    by_cases hs : secret=0
    · subst secret
      simp only [dotProduct_zero,zero_ne_one,if_false,if_true]
      rw [_Pni]
      ring
    · rw [_P9h secret hs
        (fun scalar : ZMod q => if scalar=1 then real secret else ideal)]
      simpa only [ZMod.card,hs,if_false] using _Pnj (1 : ZMod q) (real secret) ideal
  unfold _root_.InfoLossLAR.WorstCase.prAlignmentLAR
  simp_rw [hview,hsecret]
  rw [_Png,_Pnk,_Pni]
  rfl
open _root_.P2Mf6bd8d28 renaming h485 → _Pdh
theorem _root_.P2Mf6bd8d28.h486 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    (q : ℝ)*(_root_.InfoLossLAR.WorstCase.prAlignmentLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t) =
      _root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t := by
  rw [_Pdh]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  field_simp [hq] <;> ring
open _root_.P2Mf6bd8d28 renaming h486 → _Pdi
theorem _root_.P2Mf6bd8d28.h484 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    |_root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t| =
      (q : ℝ)*|_root_.InfoLossLAR.WorstCase.prAlignmentLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t| := by
  rw [←_Pdi D lam pp q N d ℓ t label,abs_mul,abs_of_nonneg (Nat.cast_nonneg q)]
open _root_.P2Mf6bd8d28 renaming h484 → _Pdg
theorem _root_.P2Mf6bd8d28.h332 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) :
    advLAR D lam pp q N d ℓ t label ≤
      (q : ℝ)*|_root_.InfoLossLAR.WorstCase.prAlignmentLAR D lam pp q N d ℓ t label-prIdealLAR D lam pp q N d ℓ t|+
        ((q : ℝ)^N)⁻¹ := by
  unfold advLAR
  have h := abs_sub_le (prRealLAR D lam pp q N d ℓ t label)
    (_root_.InfoLossLAR.WorstCase.prZeroSecretReplacedLAR D lam pp q N d ℓ t label) (prIdealLAR D lam pp q N d ℓ t)
  apply h.trans
  rw [_Pdg]
  have hz := _Pdt D lam pp q N d ℓ t label
  linarith
open _root_.P2Mf6bd8d28 renaming h332 → _P98
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h332 → _P98
open _root_.P2Mf6bd8d28 renaming h341 → _P9h
open _root_.P2Mf6bd8d28 renaming h484 → _Pdg
open _root_.P2Mf6bd8d28 renaming h485 → _Pdh
open _root_.P2Mf6bd8d28 renaming h486 → _Pdi
open _root_.P2Mf6bd8d28 renaming h844 → _Png
open _root_.P2Mf6bd8d28 renaming h845 → _Pnh
open _root_.P2Mf6bd8d28 renaming h846 → _Pni
open _root_.P2Mf6bd8d28 renaming h847 → _Pnj
open _root_.P2Mf6bd8d28 renaming h848 → _Pnk
open _root_.P2Mf6bd8d28 renaming h849 → _Pnl
open _root_.P2Mf6bd8d28 renaming h850 → _Pnm
end
open _root_.P2Mf6bd8d28 renaming h332 → _P98
open _root_.P2Mf6bd8d28 renaming h341 → _P9h
open _root_.P2Mf6bd8d28 renaming h484 → _Pdg
open _root_.P2Mf6bd8d28 renaming h485 → _Pdh
open _root_.P2Mf6bd8d28 renaming h486 → _Pdi
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InfoLossLAR.WorstCase
open Matrix AFT
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h513 {F Label : Type*} [Field F] [Fintype F]
    [Fintype Label] {d N : ℕ}
    (secret auxiliary : Fin N → F) (hmiss : auxiliary ⬝ᵥ secret ≠ 1)
    (source : _root_.AFT.FiniteDist (Fin d → F)) (label : (Fin d → F) → Label) :
    source.mix (fun input =>
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map
        (fun matrix => (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary matrix input, label input))) =
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (source.map label) :=
  _Pe source
    (fun input => _root_.InfoLossLAR.WorstCase.rankOneUnalignedEquiv secret auxiliary hmiss input) label
open _root_.P2Mf6bd8d28 renaming h513 → _Pe9
private theorem _root_.P2Mf6bd8d28.h898 {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    _root_.AFT.FiniteDist.uniform (α × β) = (_root_.AFT.FiniteDist.uniform α).prod (_root_.AFT.FiniteDist.uniform β) := by
  ext point
  simp only [_root_.AFT.FiniteDist.uniform_weight, _root_.AFT.FiniteDist.prod_weight,
    Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev]
  ring
open _root_.P2Mf6bd8d28 renaming h898 → _Poy
private theorem _root_.P2Mf6bd8d28.h897 {α β : Type*} [Fintype α] [Fintype β]
    (first : _root_.AFT.FiniteDist α) (second : _root_.AFT.FiniteDist β) :
    (first.prod second).map Prod.fst = first := by
  ext point
  simp only [_root_.AFT.FiniteDist.map_weight, Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight]
  simp_rw [Finset.sum_ite_irrel, ← Finset.mul_sum, second.sum_one, mul_one]
  simp
open _root_.P2Mf6bd8d28 renaming h897 → _Pox
theorem _root_.P2Mf6bd8d28.h512 {F Label : Type*} [CommRing F] [Fintype F]
    [Fintype Label] {d N : ℕ}
    (secret auxiliary : Fin N → F) (halign : auxiliary ⬝ᵥ secret = 1)
    (label : (Fin d → F) → Label) :
    (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F × (Fin d → F))).map
      (fun pair => (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary pair.1 pair.2, label pair.2)) =
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map
        (fun matrix => (matrix, label (matrix.mulVec secret))) := by
  let transform := _root_.InfoLossLAR.WorstCase.rankOneAlignedEquiv (d := d) secret auxiliary halign
  let observe := fun pair : Matrix (Fin d) (Fin N) F × (Fin d → F) =>
    (pair.1, label (pair.1.mulVec secret))
  have h := congrArg (fun law => law.map observe) (_root_.AFT.FiniteDist.uniform_map_equiv transform)
  rw [_root_.AFT.FiniteDist.map_map] at h
  have hs : (fun pair => observe (transform pair)) =
      (fun pair => (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary pair.1 pair.2, label pair.2)) := by
    funext pair
    change (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary pair.1 pair.2,
      label ((_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary pair.1 pair.2).mulVec secret)) = _
    rw [_root_.InfoLossLAR.WorstCase.rankOneMatrix_aligned secret auxiliary halign]
  rw [hs] at h
  rw [h, _Poy]
  let matrixLaw := _root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)
  let hidden := _root_.AFT.FiniteDist.uniform (Fin d → F)
  let output := fun matrix : Matrix (Fin d) (Fin N) F =>
    (matrix, label (matrix.mulVec secret))
  have hm := _root_.AFT.FiniteDist.map_map (matrixLaw.prod hidden)
    (Prod.fst : Matrix (Fin d) (Fin N) F × (Fin d → F) → Matrix (Fin d) (Fin N) F) output
  exact hm.symm.trans (congrArg (fun law => law.map output) (_Pox matrixLaw hidden))
open _root_.P2Mf6bd8d28 renaming h512 → _Pe8
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h512 → _Pe8
open _root_.P2Mf6bd8d28 renaming h513 → _Pe9
open _root_.P2Mf6bd8d28 renaming h897 → _Pox
open _root_.P2Mf6bd8d28 renaming h898 → _Poy
end
open _root_.P2Mf6bd8d28 renaming h512 → _Pe8
open _root_.P2Mf6bd8d28 renaming h513 → _Pe9
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.canonicalCarry
end AFT.canonicalCarry
namespace AFT.fiberLabel
end AFT.fiberLabel
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace InfoLossLAR.WorstCase
open AFT
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h585 {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    (label : V → K) (direction : K →+ V)
    (htranslate : ∀ x k, label (x + direction k) = label x + k)
    (pair : {x : V // label x = 0} × K) :
    label (_root_.InfoLossLAR.WorstCase.zeroFiberCoordinates label direction htranslate pair) = pair.2 := by
  change label (pair.1.val + direction pair.2) = _
  rw [htranslate,pair.1.property,zero_add]
open _root_.P2Mf6bd8d28 renaming h585 → _Pg9
theorem _root_.P2Mf6bd8d28.h586 {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    [Fintype V] [Fintype K]
    (label : V → K) (direction : K →+ V)
    (htranslate : ∀ x k, label (x + direction k) = label x + k) :
    letI : Nonempty {x : V // label x = 0} :=
      ⟨⟨0 + direction (-label 0), by rw [htranslate]; simp⟩⟩
    ((_root_.AFT.FiniteDist.uniform {x : V // label x = 0}).prod (_root_.AFT.FiniteDist.uniform K)).map
      (fun pair => (pair.1.val + direction pair.2, pair.2)) =
      (_root_.AFT.FiniteDist.uniform V).map (fun x => (x, label x)) := by
  letI : Nonempty {x : V // label x = 0} :=
    ⟨⟨0 + direction (-label 0), by rw [htranslate]; simp⟩⟩
  have hp : (_root_.AFT.FiniteDist.uniform {x : V // label x = 0}).prod (_root_.AFT.FiniteDist.uniform K) =
      _root_.AFT.FiniteDist.uniform ({x : V // label x = 0} × K) := by
    ext pair
    simp only [_root_.AFT.FiniteDist.prod_weight,_root_.AFT.FiniteDist.uniform_weight,Fintype.card_prod,
      Nat.cast_mul,mul_inv_rev]
    ring
  rw [hp]
  let equiv := _root_.InfoLossLAR.WorstCase.zeroFiberCoordinates label direction htranslate
  have hu := congrArg (fun law => law.map (fun x => (x,label x)))
    (_root_.AFT.FiniteDist.uniform_map_equiv equiv)
  rw [_root_.AFT.FiniteDist.map_map] at hu
  convert hu using 1
  apply congrArg
  funext pair
  change (pair.1.val + direction pair.2,pair.2) =
    (pair.1.val + direction pair.2,label (equiv pair))
  rw [_Pg9 label direction htranslate pair]
open _root_.P2Mf6bd8d28 renaming h586 → _Pga
private theorem _root_.P2Mf6bd8d28.h900 {α β : Type*} [Fintype α] [Fintype β]
    (first : _root_.AFT.FiniteDist α) (second : _root_.AFT.FiniteDist β) :
    (first.prod second).map Prod.snd = second := by
  ext point
  simp only [_root_.AFT.FiniteDist.map_weight,Fintype.sum_prod_type,_root_.AFT.FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel,← Finset.sum_mul,first.sum_one,one_mul]
  simp
open _root_.P2Mf6bd8d28 renaming h900 → _Pp0
theorem _root_.P2Mf6bd8d28.h441 {V K : Type*} [AddCommGroup V] [AddCommGroup K]
    [Fintype V] [Fintype K]
    (label : V → K) (direction : K →+ V)
    (htranslate : ∀ x k, label (x + direction k) = label x + k) :
    (_root_.AFT.FiniteDist.uniform V).map label = _root_.AFT.FiniteDist.uniform K := by
  letI : Nonempty {x : V // label x = 0} :=
    ⟨⟨0 + direction (-label 0), by rw [htranslate]; simp⟩⟩
  have h := congrArg (fun law => law.map (Prod.snd : V × K → K))
    (_Pga label direction htranslate)
  simp only [_root_.AFT.FiniteDist.map_map] at h
  change ((_root_.AFT.FiniteDist.uniform {x : V // label x = 0}).prod
    (_root_.AFT.FiniteDist.uniform K)).map Prod.snd = (_root_.AFT.FiniteDist.uniform V).map label at h
  exact h.symm.trans (_Pp0 _ _)
open _root_.P2Mf6bd8d28 renaming h441 → _Pc9
theorem _root_.P2Mf6bd8d28.h556 (n q : ℕ) [NeZero q]
    (column : Fin (n+1) → ℤ) (hcolumn : _root_.AFT.totalCharge column = (q : ℤ)) :
    _root_.AFT.roundingLoad n column (_root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn) =
      (q : ℤ) • (Pi.single (0 : Fin (n+1)) (1 : ℤ)) := by
  unfold _root_.InfoLossLAR.WorstCase.roundingDirectionInteger
  exact congrArg Subtype.val ((_root_.AFT.roundingCoordinates n (q : ℤ)
    (by exact_mod_cast NeZero.ne q) column hcolumn).apply_symm_apply _)
open _root_.P2Mf6bd8d28 renaming h556 → _Pfg
theorem _root_.P2Mf6bd8d28.h438 (n q : ℕ) [NeZero q]
    (column : Fin (n+1) → ℤ) (hcolumn : _root_.AFT.totalCharge column = (q : ℤ))
    (input : (Fin n → ℤ) × ℤ) (amount : ℤ) :
    _root_.AFT.integerLabel n q column (input + amount • _root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn) =
      _root_.AFT.integerLabel n q column input + (amount : ZMod q) := by
  have hl : _root_.AFT.roundingLoad n column (input + amount • _root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn) =
      _root_.AFT.roundingLoad n column input + (q : ℤ) • (amount • (Pi.single (0 : Fin (n+1)) (1 : ℤ))) := by
    have h := (_root_.AFT.roundingCoordinates n (q : ℤ) (by exact_mod_cast NeZero.ne q) column hcolumn).map_add
      input (amount • _root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn)
    have hh := congrArg Subtype.val h
    change _root_.AFT.roundingLoad n column _ = _root_.AFT.roundingLoad n column input + _root_.AFT.roundingLoad n column _ at hh
    rw [_root_.AFT.roundingLoad_smul,_Pfg] at hh
    simpa only [smul_smul,Int.mul_comm] using hh
  have hc : _root_.AFT.canonicalCarry n q (_root_.AFT.roundingLoad n column
      (input + amount • _root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn)) =
      _root_.AFT.canonicalCarry n q (_root_.AFT.roundingLoad n column input) +
        amount • (Pi.single (0 : Fin (n+1)) (1 : ℤ)) := by
    funext i
    rw [hl]
    change (_root_.AFT.roundingLoad n column input i + (q : ℤ) * (amount * ((Pi.single (0 : Fin (n+1)) (1 : ℤ) : Fin (n+1) → ℤ) i))) /
      (q : ℤ) = _root_.AFT.roundingLoad n column input i / (q : ℤ) + amount * ((Pi.single (0 : Fin (n+1)) (1 : ℤ) : Fin (n+1) → ℤ) i)
    exact Int.add_mul_ediv_left _ _ (by exact_mod_cast NeZero.ne q)
  unfold _root_.AFT.integerLabel
  rw [hc,_root_.AFT.totalCharge_add,Int.cast_add,_root_.AFT.totalCharge_smul]
  simp [_root_.AFT.totalCharge]
open _root_.P2Mf6bd8d28 renaming h438 → _Pc6
theorem _root_.P2Mf6bd8d28.h421 (n q : ℕ) [NeZero q]
    (column : Fin (n+1) → ℤ) (hcolumn : _root_.AFT.totalCharge column = (q : ℤ))
    (input : (Fin n → ZMod q) × ZMod q) (amount : ZMod q) :
    _root_.AFT.fiberLabel n q column (input + _root_.InfoLossLAR.WorstCase.roundingDirection n q column hcolumn amount) =
      _root_.AFT.fiberLabel n q column input + amount := by
  have hr : _root_.AFT.reduceCoordinates n q
      (_root_.AFT.liftCoordinates n q input + (amount.val : ℤ) • _root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn) =
      input + _root_.InfoLossLAR.WorstCase.roundingDirection n q column hcolumn amount := by
    apply Prod.ext
    · funext i
      simp only [_root_.AFT.reduceCoordinates,_root_.AFT.liftCoordinates,_root_.InfoLossLAR.WorstCase.roundingDirection,AddMonoidHom.coe_mk,
        ZeroHom.coe_mk,Prod.fst_add,Prod.smul_fst,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
        Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
    · simp [_root_.AFT.reduceCoordinates,_root_.AFT.liftCoordinates,_root_.InfoLossLAR.WorstCase.roundingDirection]
  rw [← hr,_root_.AFT.fiberLabel_reduceCoordinates n q column hcolumn,
    _Pc6 n q column hcolumn]
  change _root_.AFT.fiberLabel n q column input + ((amount.val : ℤ) : ZMod q) = _
  simp
open _root_.P2Mf6bd8d28 renaming h421 → _Pbp
theorem _root_.P2Mf6bd8d28.h416 (q n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (input : Fin (n+1) → ZMod q) (amount : ZMod q) :
    fT63 q (n+1) (input + _root_.InfoLossLAR.WorstCase.fixedRoundingDirection q n hq amount) =
      fT63 q (n+1) input + amount := by
  rw [_P4m,_P4m]
  have hr := _Pbp n q (_root_.AFT.injectionColumn n q)
    (_root_.AFT.totalCharge_injectionColumn n q hq)
    (fun j => input j.castSucc,input (Fin.last n)) amount
  have hp : (fun j => (input + _root_.InfoLossLAR.WorstCase.fixedRoundingDirection q n hq amount) j.castSucc,
      (input + _root_.InfoLossLAR.WorstCase.fixedRoundingDirection q n hq amount) (Fin.last n)) =
      (fun j => input j.castSucc,input (Fin.last n)) +
        _root_.InfoLossLAR.WorstCase.roundingDirection n q (_root_.AFT.injectionColumn n q) (_root_.AFT.totalCharge_injectionColumn n q hq) amount := by
    apply Prod.ext
    · funext j
      simp [_root_.InfoLossLAR.WorstCase.fixedRoundingDirection]
    · simp [_root_.InfoLossLAR.WorstCase.fixedRoundingDirection]
  exact (congrArg (_root_.AFT.fiberLabel n q (_root_.AFT.injectionColumn n q)) hp).trans hr
open _root_.P2Mf6bd8d28 renaming h416 → _Pbk
theorem _root_.P2Mf6bd8d28.h424 (q d : ℕ) [NeZero q] (x : Fin d → ZMod q) :
    (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q d).weight x =
      unifZeroFiber (fun input => (fun _ : Fin 1 => fT63 q d input)) x := by
  letI : Nonempty {x : Fin d → ZMod q // fT63 q d x = 0} := ⟨⟨0,_root_.InfoLossLAR.WorstCase.fT63_zero q d⟩⟩
  exact _P53 (fT63 q d) x
open _root_.P2Mf6bd8d28 renaming h424 → _Pbs
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h416 → _Pbk
open _root_.P2Mf6bd8d28 renaming h421 → _Pbp
open _root_.P2Mf6bd8d28 renaming h424 → _Pbs
open _root_.P2Mf6bd8d28 renaming h438 → _Pc6
open _root_.P2Mf6bd8d28 renaming h441 → _Pc9
open _root_.P2Mf6bd8d28 renaming h556 → _Pfg
open _root_.P2Mf6bd8d28 renaming h585 → _Pg9
open _root_.P2Mf6bd8d28 renaming h586 → _Pga
open _root_.P2Mf6bd8d28 renaming h900 → _Pp0
end
open _root_.P2Mf6bd8d28 renaming h416 → _Pbk
open _root_.P2Mf6bd8d28 renaming h421 → _Pbp
open _root_.P2Mf6bd8d28 renaming h424 → _Pbs
open _root_.P2Mf6bd8d28 renaming h438 → _Pc6
open _root_.P2Mf6bd8d28 renaming h441 → _Pc9
open _root_.P2Mf6bd8d28 renaming h556 → _Pfg
open _root_.P2Mf6bd8d28 renaming h585 → _Pg9
open _root_.P2Mf6bd8d28 renaming h586 → _Pga
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InfoLossLAR.WorstCase
open AFT
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h481 (n : ℕ) (load : Fin (n+1) → ℤ)
    (hload : _root_.AFT.totalCharge load = 0) : _root_.AFT.pathLoad n (_root_.InfoLossLAR.WorstCase.pathPrefix n load) = load := by
  induction n with
  | zero =>
      funext i
      have hi : i=0 := Fin.ext (by omega)
      subst i
      simpa [_root_.AFT.pathLoad,_root_.AFT.totalCharge] using hload.symm
  | succ n ih =>
      let residual : Fin (n+1) → ℤ := fun i => load i.succ + if i=0 then load 0 else 0
      have hresidual : _root_.AFT.totalCharge residual = 0 := by
        have hsum : load 0+(∑ i : Fin (n+1),load i.succ)=0 := by
          simpa [_root_.AFT.totalCharge,Fin.sum_univ_succ] using hload
        simp only [residual,_root_.AFT.totalCharge,Finset.sum_add_distrib]
        simpa [add_comm] using hsum
      have hp := ih residual hresidual
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [_root_.InfoLossLAR.WorstCase.pathPrefix,_root_.AFT.pathLoad]
      · change _root_.AFT.pathLoad n (_root_.InfoLossLAR.WorstCase.pathPrefix n residual) j - (if j=0 then load 0 else 0) = load j.succ
        rw [hp]
        simp [residual]
open _root_.P2Mf6bd8d28 renaming h481 → _Pdd
theorem _root_.P2Mf6bd8d28.h400 (n q : ℕ)
    (column : Fin (n+1) → ℤ) (hcolumn : _root_.AFT.totalCharge column = (q : ℤ)) :
    _root_.AFT.roundingLoad n column (_root_.InfoLossLAR.WorstCase.computableRoundingDirectionInteger n q column) =
      (q : ℤ) • (Pi.single (0 : Fin (n+1)) (1 : ℤ)) := by
  have hz : _root_.AFT.totalCharge ((q : ℤ) • (Pi.single (0 : Fin (n+1)) (1 : ℤ))-column) = 0 := by
    rw [_root_.AFT.totalCharge_sub,_root_.AFT.totalCharge_smul,hcolumn]
    simp [_root_.AFT.totalCharge]
  unfold _root_.AFT.roundingLoad _root_.InfoLossLAR.WorstCase.computableRoundingDirectionInteger
  rw [_Pdd n _ hz]
  simp
open _root_.P2Mf6bd8d28 renaming h400 → _Pb4
theorem _root_.P2Mf6bd8d28.h399 (n q : ℕ) [NeZero q]
    (column : Fin (n+1) → ℤ) (hcolumn : _root_.AFT.totalCharge column = (q : ℤ)) :
    _root_.InfoLossLAR.WorstCase.computableRoundingDirectionInteger n q column =
      _root_.InfoLossLAR.WorstCase.roundingDirectionInteger n q column hcolumn := by
  apply _root_.AFT.roundingLoad_injective n (q : ℤ) (by exact_mod_cast NeZero.ne q) column hcolumn
  rw [_Pb4 n q column hcolumn,_Pfg]
open _root_.P2Mf6bd8d28 renaming h399 → _Pb3
theorem _root_.P2Mf6bd8d28.h395 (q n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (amount : ZMod q) :
    _root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection q n amount = _root_.InfoLossLAR.WorstCase.fixedRoundingDirection q n hq amount := by
  unfold _root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection
  rw [_Pb3 n q _ (_root_.AFT.totalCharge_injectionColumn n q hq)]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [_root_.InfoLossLAR.WorstCase.fixedRoundingDirection,_root_.InfoLossLAR.WorstCase.roundingDirection,_root_.AFT.reduceCoordinates]
open _root_.P2Mf6bd8d28 renaming h395 → _Paz
theorem _root_.P2Mf6bd8d28.h397 (q n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (label : Fin 1 → ZMod q) :
    _root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n label = _root_.InfoLossLAR.WorstCase.fixedVectorDirection q n hq label :=
  _Paz q n hq (label 0)
open _root_.P2Mf6bd8d28 renaming h397 → _Pb1
theorem _root_.P2Mf6bd8d28.h423 (q n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (input : Fin (n+1) → ZMod q) (label : Fin 1 → ZMod q) :
    (fun _ : Fin 1 => fT63 q (n+1) (input + _root_.InfoLossLAR.WorstCase.fixedVectorDirection q n hq label)) =
      (fun _ : Fin 1 => fT63 q (n+1) input) + label := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact _Pbk q n hq input (label 0)
open _root_.P2Mf6bd8d28 renaming h423 → _Pbr
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h395 → _Paz
open _root_.P2Mf6bd8d28 renaming h397 → _Pb1
open _root_.P2Mf6bd8d28 renaming h399 → _Pb3
open _root_.P2Mf6bd8d28 renaming h400 → _Pb4
open _root_.P2Mf6bd8d28 renaming h423 → _Pbr
open _root_.P2Mf6bd8d28 renaming h481 → _Pdd
end
open _root_.P2Mf6bd8d28 renaming h395 → _Paz
open _root_.P2Mf6bd8d28 renaming h397 → _Pb1
open _root_.P2Mf6bd8d28 renaming h399 → _Pb3
open _root_.P2Mf6bd8d28 renaming h400 → _Pb4
open _root_.P2Mf6bd8d28 renaming h423 → _Pbr
open _root_.P2Mf6bd8d28 renaming h481 → _Pdd
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace InfoLossLAR.WorstCase
open AFT Matrix QAlgorithms.Complexity
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h447 {F K : Type*} [CommRing F] {d N : ℕ}
    (secret auxiliary : Fin N → F) (direction : K → (Fin d → F))
    (matrix : Matrix (Fin d) (Fin N) F) (error : Fin d → F) (mark : K) :
    _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction matrix (matrix.mulVec secret+error) mark =
      (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary matrix (error+direction mark),mark) := by
  unfold _root_.InfoLossLAR.WorstCase.larRankOnePreprocess _root_.InfoLossLAR.WorstCase.rankOneMatrix
  rw [add_assoc]
open _root_.P2Mf6bd8d28 renaming h447 → _Pcf
theorem _root_.P2Mf6bd8d28.h453 {V K : Type*} [Fintype V] [AddCommGroup V]
    [Fintype K] [AddCommGroup K] (label : V → K) (hzero : label 0=0)
    (direction : K →+ V) (htranslate : ∀ input mark,label (input+direction mark)=label input+mark) :
    ((_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero).prod (_root_.AFT.FiniteDist.uniform K)).map
      (fun pair => (pair.1+direction pair.2,pair.2)) =
      (_root_.AFT.FiniteDist.uniform V).map (fun input => (input,label input)) := by
  letI : Nonempty {x : V // label x=0} := ⟨⟨0,hzero⟩⟩
  have h := _Pga label direction htranslate
  have hi : @Subtype.fintype V (fun x => label x=0)
      (fun x => Classical.propDecidable (label x=0)) inferInstance =
      Subtype.fintype (fun x : V => label x=0) := Subsingleton.elim _ _
  rw [hi] at h
  let source := _root_.AFT.FiniteDist.uniform {x : V // label x=0}
  let marks := _root_.AFT.FiniteDist.uniform K
  have hm := _Pd source marks
    (Subtype.val : {x : V // label x=0} → V) (id : K → K)
  have hid : marks.map id=marks := _root_.AFT.FiniteDist.uniform_map_equiv (Equiv.refl K)
  rw [hid] at hm
  change ((source.map Subtype.val).prod marks).map (fun pair => (pair.1+direction pair.2,pair.2)) = _
  rw [←hm,_root_.AFT.FiniteDist.map_map]
  exact h
open _root_.P2Mf6bd8d28 renaming h453 → _Pcl
private theorem _root_.P2Mf6bd8d28.h884 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (first : _root_.AFT.FiniteDist A) (second : _root_.AFT.FiniteDist B) (decode : A × B → C) :
    (first.prod second).map decode = second.mix (fun b => first.map (fun a => decode (a,b))) := by
  ext output
  simp only [_root_.AFT.FiniteDist.map_weight,_root_.AFT.FiniteDist.mix_weight,_root_.AFT.FiniteDist.prod_weight,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : decode (a,b)=output <;> simp [h,mul_comm]
open _root_.P2Mf6bd8d28 renaming h884 → _Pok
private theorem _root_.P2Mf6bd8d28.h889 {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (_root_.AFT.FiniteDist.uniform A).prod (_root_.AFT.FiniteDist.uniform B) = _root_.AFT.FiniteDist.uniform (A × B) := by
  ext pair
  simp only [_root_.AFT.FiniteDist.prod_weight,_root_.AFT.FiniteDist.uniform_weight,Fintype.card_prod,Nat.cast_mul,_root_.mul_inv_rev]
  ring
open _root_.P2Mf6bd8d28 renaming h889 → _Pop
private theorem _root_.P2Mf6bd8d28.h885 {A B : Type*} [Fintype A] [Fintype B]
    (first : _root_.AFT.FiniteDist A) (second : _root_.AFT.FiniteDist B) : (first.prod second).map Prod.snd=second := by
  ext output
  simp only [_root_.AFT.FiniteDist.map_weight,_root_.AFT.FiniteDist.prod_weight,Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [←Finset.sum_mul,first.sum_one,one_mul]
open _root_.P2Mf6bd8d28 renaming h885 → _Pol
theorem _root_.P2Mf6bd8d28.h450 {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [AddCommGroup K] {d N : ℕ}
    (label : (Fin d → F) → K) (hzero : label 0=0) (direction : K →+ (Fin d → F))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → F) :
    _root_.InfoLossLAR.WorstCase.larRankOneRealBlock (_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero) direction secret auxiliary =
      (_root_.AFT.FiniteDist.uniform (Fin d → F)).mix fun input =>
        (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map fun matrix =>
          (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary matrix input,label input) := by
  let kernel := fun pair : (Fin d → F) × K =>
    (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map fun matrix =>
      (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary matrix pair.1,pair.2)
  have hm := _root_.AFT.FiniteDist.mix_map
    ((_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero).prod (_root_.AFT.FiniteDist.uniform K))
    (fun pair => (pair.1+direction pair.2,pair.2)) kernel
  calc
    _ = (((_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero).prod (_root_.AFT.FiniteDist.uniform K)).map
        (fun pair => (pair.1+direction pair.2,pair.2))).mix kernel := by
      simpa only [_root_.InfoLossLAR.WorstCase.larRankOneRealBlock,_Pcf,kernel] using hm.symm
    _ = ((_root_.AFT.FiniteDist.uniform (Fin d → F)).map (fun input => (input,label input))).mix kernel := by
      rw [_Pcl label hzero direction htranslate]
    _ = _ := _root_.AFT.FiniteDist.mix_map _ _ _
open _root_.P2Mf6bd8d28 renaming h450 → _Pci
theorem _root_.P2Mf6bd8d28.h448 {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [AddCommGroup K] {d N : ℕ}
    (label : (Fin d → F) → K) (hzero : label 0=0) (direction : K →+ (Fin d → F))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → F) (halign : auxiliary ⬝ᵥ secret=1) :
    _root_.InfoLossLAR.WorstCase.larRankOneRealBlock (_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero) direction secret auxiliary =
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).map
        (fun matrix => (matrix,label (matrix.mulVec secret))) := by
  rw [_Pci label hzero direction htranslate]
  have hm := _Pok
    (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)) (_root_.AFT.FiniteDist.uniform (Fin d → F))
    (fun pair => (_root_.InfoLossLAR.WorstCase.rankOneMatrix secret auxiliary pair.1 pair.2,label pair.2))
  rw [←hm,_Pop]
  exact _Pe8 secret auxiliary halign label
open _root_.P2Mf6bd8d28 renaming h448 → _Pcg
theorem _root_.P2Mf6bd8d28.h449 {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [AddCommGroup K] {d N : ℕ}
    (label : (Fin d → F) → K) (hzero : label 0=0) (direction : K →+ (Fin d → F))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → F) (hmiss : auxiliary ⬝ᵥ secret≠1) :
    _root_.InfoLossLAR.WorstCase.larRankOneRealBlock (_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero) direction secret auxiliary =
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (_root_.AFT.FiniteDist.uniform K) := by
  rw [_Pci label hzero direction htranslate,
    _Pe9 secret auxiliary hmiss,
    _Pc9 label direction htranslate]
open _root_.P2Mf6bd8d28 renaming h449 → _Pch
theorem _root_.P2Mf6bd8d28.h445 {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [Nonempty K] {d N : ℕ}
    (direction : K → (Fin d → F)) (auxiliary : Fin N → F) :
    _root_.InfoLossLAR.WorstCase.larRankOneIdealBlock direction auxiliary =
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (_root_.AFT.FiniteDist.uniform K) := by
  have hmiss : auxiliary ⬝ᵥ (0 : Fin N → F) ≠ 1 := by simp
  have h := _Pe
    ((_root_.AFT.FiniteDist.uniform (Fin d → F)).prod (_root_.AFT.FiniteDist.uniform K))
    (fun pair => _root_.InfoLossLAR.WorstCase.rankOneUnalignedEquiv (d := d) (0 : Fin N → F) auxiliary hmiss (pair.1+direction pair.2))
    Prod.snd
  rw [_Pol] at h
  have hpoint (pair : (Fin d → F) × K) (matrix : Matrix (Fin d) (Fin N) F) :
      _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction matrix pair.1 pair.2 =
        (_root_.InfoLossLAR.WorstCase.rankOneUnalignedEquiv (0 : Fin N → F) auxiliary hmiss (pair.1+direction pair.2) matrix,pair.2) := by
    change _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction matrix pair.1 pair.2 =
      (_root_.InfoLossLAR.WorstCase.rankOneMatrix (0 : Fin N → F) auxiliary matrix (pair.1+direction pair.2),pair.2)
    simp only [_root_.InfoLossLAR.WorstCase.larRankOnePreprocess,_root_.InfoLossLAR.WorstCase.rankOneMatrix,Matrix.mulVec_zero,zero_add]
  simpa only [_root_.InfoLossLAR.WorstCase.larRankOneIdealBlock,hpoint] using h
open _root_.P2Mf6bd8d28 renaming h445 → _Pcd
private theorem _root_.P2Mf6bd8d28.h882 {Index Input Output : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Input] [Fintype Output]
    (law : Index → _root_.AFT.FiniteDist Input) (decode : Index → Input → Output) :
    (_root_.AFT.FiniteDist.independent law).map (fun word index => decode index (word index)) =
      _root_.AFT.FiniteDist.independent (fun index => (law index).map (decode index)) := by
  ext values
  simp only [_root_.AFT.FiniteDist.map_weight,_root_.AFT.FiniteDist.independent]
  have h := Fintype.prod_sum (fun index point =>
    if decode index point=values index then (law index).weight point else 0)
  apply Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]
open _root_.P2Mf6bd8d28 renaming h882 → _Poi
private theorem _root_.P2Mf6bd8d28.h883 {Index First Second : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (first : Index → _root_.AFT.FiniteDist First) (second : Index → _root_.AFT.FiniteDist Second)
    (value : (Index → First × Second) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun index => (first index).prod (second index))).expectation value =
      (_root_.AFT.FiniteDist.independent first).expectation (fun left =>
        (_root_.AFT.FiniteDist.independent second).expectation (fun right => value (fun index => (left index,right index)))) := by
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
  rw [←(Equiv.arrowProdEquivProdArrow Index (fun _ => First) (fun _ => Second)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.arrowProdEquivProdArrow,Equiv.coe_fn_symm_mk,_root_.AFT.FiniteDist.prod_weight,
    Finset.prod_mul_distrib,mul_assoc]
open _root_.P2Mf6bd8d28 renaming h883 → _Poj
private theorem _root_.P2Mf6bd8d28.h888 {Index State : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype State] [Nonempty State] :
    _root_.AFT.FiniteDist.independent (fun _ : Index => _root_.AFT.FiniteDist.uniform State) = _root_.AFT.FiniteDist.uniform (Index → State) := by
  ext word
  simp only [_root_.AFT.FiniteDist.independent,_root_.AFT.FiniteDist.uniform_weight,Finset.prod_const,
    Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]
open _root_.P2Mf6bd8d28 renaming h888 → _Poo
private theorem _root_.P2Mf6bd8d28.h887 {A : Type*} [Fintype A] [Nonempty A] (test : A → ℝ) :
    (_root_.AFT.FiniteDist.uniform A).expectation test = avg test := by
  simp only [_root_.AFT.FiniteDist.expectation,_root_.AFT.FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h887 → _Pon
theorem _root_.P2Mf6bd8d28.h455 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q] :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin t =>
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod
        (_root_.AFT.FiniteDist.uniform (Fin ℓ → ZMod q)))).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
      prIdealLAR D lam pp q N d ℓ t := by
  rw [_Poj]
  simp only [_Poo,_Pon,prIdealLAR]
open _root_.P2Mf6bd8d28 renaming h455 → _Pcn
theorem _root_.P2Mf6bd8d28.h456 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (secret : Fin N → ZMod q) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin t =>
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).map
        (fun matrix => (matrix,label (matrix.mulVec secret))))).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
      _root_.InfoLossLAR.WorstCase.larSecretAcceptance D lam pp q N d ℓ t label secret := by
  rw [←_Poi,_root_.AFT.FiniteDist.expectation_map,_Poo]
  simp only [_Pon,_root_.InfoLossLAR.WorstCase.larSecretAcceptance,Function.comp_def]
open _root_.P2Mf6bd8d28 renaming h456 → _Pco
theorem _root_.P2Mf6bd8d28.h451 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (direction : (Fin ℓ → ZMod q) →+ (Fin d → ZMod q))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark)
    (secret auxiliary : Fin N → ZMod q) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin t =>
      _root_.InfoLossLAR.WorstCase.larRankOneRealBlock (_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero) direction secret auxiliary)).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
      if auxiliary ⬝ᵥ secret=1 then _root_.InfoLossLAR.WorstCase.larSecretAcceptance D lam pp q N d ℓ t label secret
      else prIdealLAR D lam pp q N d ℓ t := by
  by_cases h : auxiliary ⬝ᵥ secret=1
  · simp only [if_pos h,_Pcg label hzero direction htranslate secret auxiliary h]
    exact _Pco D lam pp q N d ℓ t label secret
  · simp only [if_neg h,_Pch label hzero direction htranslate secret auxiliary h]
    exact _Pcn D lam pp q N d ℓ t
open _root_.P2Mf6bd8d28 renaming h451 → _Pcj
theorem _root_.P2Mf6bd8d28.h446 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) (auxiliary : Fin N → ZMod q) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin t => _root_.InfoLossLAR.WorstCase.larRankOneIdealBlock direction auxiliary)).expectation
      (fun table => acceptProb D (encInput lam pp (encTable table))) =
        prIdealLAR D lam pp q N d ℓ t := by
  simp only [_Pcd]
  exact _Pcn D lam pp q N d ℓ t
open _root_.P2Mf6bd8d28 renaming h446 → _Pce
theorem _root_.P2Mf6bd8d28.h495 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (direction : (Fin ℓ → ZMod q) →+ (Fin d → ZMod q))
    (htranslate : ∀ input mark,label (input+direction mark)=label input+mark) :
    _root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t (_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero) direction =
      _root_.InfoLossLAR.WorstCase.prAlignmentLAR D lam pp q N d ℓ t label := by
  unfold _root_.InfoLossLAR.WorstCase.prRankOneRealLAR _root_.InfoLossLAR.WorstCase.prAlignmentLAR
  apply congrArg avg
  funext secret
  apply congrArg avg
  funext auxiliary
  rw [_Pcj D lam pp q N d ℓ t label hzero direction htranslate]
  by_cases h : auxiliary ⬝ᵥ secret=1
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]
    rfl
open _root_.P2Mf6bd8d28 renaming h495 → _Pdr
theorem _root_.P2Mf6bd8d28.h491 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction = prIdealLAR D lam pp q N d ℓ t := by
  unfold _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR
  simp only [_Pce]
  have hc : (Fintype.card (Fin N → ZMod q) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hc
open _root_.P2Mf6bd8d28 renaming h491 → _Pdn
theorem _root_.P2Mf6bd8d28.h454 (q d ℓ : ℕ) [NeZero q]
    (label : (Fin d → ZMod q) → Fin ℓ → ZMod q) (hzero : label 0=0)
    (input : Fin d → ZMod q) :
    (_root_.InfoLossLAR.WorstCase.larUniformZeroLaw label hzero).weight input = unifZeroFiber label input := by
  letI : Nonempty {x : Fin d → ZMod q // label x=0} := ⟨⟨0,hzero⟩⟩
  have hi : @Subtype.fintype (Fin d → ZMod q) (fun x => label x=0)
      (fun x => Classical.propDecidable (label x=0)) inferInstance =
      Subtype.fintype (fun x : Fin d → ZMod q => label x=0) := Subsingleton.elim _ _
  unfold _root_.InfoLossLAR.WorstCase.larUniformZeroLaw unifZeroFiber
  rw [hi]
  exact _P54 (fun x : Fin d → ZMod q => label x=0) input
open _root_.P2Mf6bd8d28 renaming h454 → _Pcm
theorem _root_.P2Mf6bd8d28.h442 (q d : ℕ) :
    (fun input : Fin d → ZMod q => fun _ : Fin 1 => fT63 q d input) 0=0 := by
  funext index
  exact _root_.InfoLossLAR.WorstCase.fT63_zero q d
open _root_.P2Mf6bd8d28 renaming h442 → _Pca
theorem _root_.P2Mf6bd8d28.h452 (q d : ℕ) [NeZero q] :
    _root_.InfoLossLAR.WorstCase.larUniformZeroLaw (fun input : Fin d → ZMod q => fun _ : Fin 1 => fT63 q d input)
      (_Pca q d) = _root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q d := by
  ext input
  rw [_Pcm,_Pbs]
open _root_.P2Mf6bd8d28 renaming h452 → _Pck
theorem _root_.P2Mf6bd8d28.h493 (D : Family) (lam : ℕ) (pp : Str)
    (q N n t : ℕ) [Fact q.Prime] [NeZero q] (hq : q ≤ n+1) :
    _root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N (n+1) 1 t (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q (n+1))
      (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) =
      _root_.InfoLossLAR.WorstCase.prAlignmentLAR D lam pp q N (n+1) 1 t
        (fun input => fun _ : Fin 1 => fT63 q (n+1) input) := by
  have hdir : _root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n =
      (_root_.InfoLossLAR.WorstCase.fixedVectorDirection q n hq : (Fin 1 → ZMod q) → (Fin (n+1) → ZMod q)) := by
    funext mark
    exact _Pb1 q n hq mark
  rw [hdir,←_Pck q (n+1)]
  exact _Pdr D lam pp q N (n+1) 1 t
    (fun input => fun _ : Fin 1 => fT63 q (n+1) input) (_Pca q (n+1))
    (_root_.InfoLossLAR.WorstCase.fixedVectorDirection q n hq) (_Pbr q n hq)
open _root_.P2Mf6bd8d28 renaming h493 → _Pdp
theorem _root_.P2Mf6bd8d28.h334 (D : Family) (lam : ℕ) (pp : Str)
    (q N n t : ℕ) [Fact q.Prime] [NeZero q] (hq : q ≤ n+1) :
    advLAR D lam pp q N (n+1) 1 t (fun input => fun _ : Fin 1 => fT63 q (n+1) input) ≤
      (q : ℝ)*|_root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N (n+1) 1 t (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q (n+1))
          (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n)-
        _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N (n+1) 1 t (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n)|+
        ((q : ℝ)^N)⁻¹ := by
  rw [_Pdp D lam pp q N n t hq,_Pdn]
  exact _P98 D lam pp q N (n+1) 1 t
    (fun input => fun _ : Fin 1 => fT63 q (n+1) input)
open _root_.P2Mf6bd8d28 renaming h334 → _P9a
private theorem _root_.P2Mf6bd8d28.h886 {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [Nonempty K] {d N : ℕ} (source : _root_.AFT.FiniteDist (Fin d → F))
    (direction : K → (Fin d → F)) (secret auxiliary : Fin N → F) :
    _root_.InfoLossLAR.WorstCase.larRankOneRealBlock source direction secret auxiliary =
      ((_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod (source.prod (_root_.AFT.FiniteDist.uniform K))).map
        (fun draw => _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction draw.1
          (draw.1.mulVec secret+draw.2.1) draw.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.larRankOneRealBlock
  exact (_Pok (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F))
    (source.prod (_root_.AFT.FiniteDist.uniform K))
    (fun draw => _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction draw.1 (draw.1.mulVec secret+draw.2.1) draw.2.2)).symm
open _root_.P2Mf6bd8d28 renaming h886 → _Pom
private theorem _root_.P2Mf6bd8d28.h881 {F K : Type*} [Field F] [Fintype F]
    [Fintype K] [Nonempty K] {d N : ℕ}
    (direction : K → (Fin d → F)) (auxiliary : Fin N → F) :
    _root_.InfoLossLAR.WorstCase.larRankOneIdealBlock direction auxiliary =
      ((_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F)).prod
        ((_root_.AFT.FiniteDist.uniform (Fin d → F)).prod (_root_.AFT.FiniteDist.uniform K))).map
        (fun draw => _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction draw.1 draw.2.1 draw.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.larRankOneIdealBlock
  exact (_Pok (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) F))
    ((_root_.AFT.FiniteDist.uniform (Fin d → F)).prod (_root_.AFT.FiniteDist.uniform K))
    (fun draw => _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction draw.1 draw.2.1 draw.2.2)).symm
open _root_.P2Mf6bd8d28 renaming h881 → _Poh
theorem _root_.P2Mf6bd8d28.h494 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t source direction =
      avg (fun secret : Fin N → ZMod q => avg (fun auxiliary : Fin N → ZMod q =>
        avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
          ∑ errors : Fin t → Fin d → ZMod q, (∏ index,source.weight (errors index))*
            avg (fun marks : Fin t → Fin ℓ → ZMod q =>
              acceptProb D (encInput lam pp (encTable (fun index =>
                _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction (matrices index)
                  ((matrices index).mulVec secret+errors index) (marks index)))))))) := by
  unfold _root_.InfoLossLAR.WorstCase.prRankOneRealLAR
  apply congrArg avg
  funext secret
  apply congrArg avg
  funext auxiliary
  simp_rw [_Pom]
  rw [←_Poi,_root_.AFT.FiniteDist.expectation_map,_Poj,
    _Poo,_Pon]
  apply congrArg avg
  funext matrices
  rw [_Poj,_Poo]
  simp only [Function.comp_def]
  simp_rw [_Pon]
  rfl
open _root_.P2Mf6bd8d28 renaming h494 → _Pdq
theorem _root_.P2Mf6bd8d28.h492 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction =
      avg (fun auxiliary : Fin N → ZMod q =>
        avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
          avg (fun responses : Fin t → Fin d → ZMod q =>
            avg (fun marks : Fin t → Fin ℓ → ZMod q =>
              acceptProb D (encInput lam pp (encTable (fun index =>
                _root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary direction (matrices index) (responses index) (marks index)))))))) := by
  unfold _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR
  apply congrArg avg
  funext auxiliary
  simp_rw [_Poh]
  rw [←_Poi,_root_.AFT.FiniteDist.expectation_map,_Poj,
    _Poo,_Pon]
  apply congrArg avg
  funext matrices
  rw [_Poj]
  simp only [_Poo,_Pon,Function.comp_def]
open _root_.P2Mf6bd8d28 renaming h492 → _Pdo
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h334 → _P9a
open _root_.P2Mf6bd8d28 renaming h442 → _Pca
open _root_.P2Mf6bd8d28 renaming h445 → _Pcd
open _root_.P2Mf6bd8d28 renaming h446 → _Pce
open _root_.P2Mf6bd8d28 renaming h447 → _Pcf
open _root_.P2Mf6bd8d28 renaming h448 → _Pcg
open _root_.P2Mf6bd8d28 renaming h449 → _Pch
open _root_.P2Mf6bd8d28 renaming h450 → _Pci
open _root_.P2Mf6bd8d28 renaming h451 → _Pcj
open _root_.P2Mf6bd8d28 renaming h452 → _Pck
open _root_.P2Mf6bd8d28 renaming h453 → _Pcl
open _root_.P2Mf6bd8d28 renaming h454 → _Pcm
open _root_.P2Mf6bd8d28 renaming h455 → _Pcn
open _root_.P2Mf6bd8d28 renaming h456 → _Pco
open _root_.P2Mf6bd8d28 renaming h491 → _Pdn
open _root_.P2Mf6bd8d28 renaming h492 → _Pdo
open _root_.P2Mf6bd8d28 renaming h493 → _Pdp
open _root_.P2Mf6bd8d28 renaming h494 → _Pdq
open _root_.P2Mf6bd8d28 renaming h495 → _Pdr
open _root_.P2Mf6bd8d28 renaming h881 → _Poh
open _root_.P2Mf6bd8d28 renaming h882 → _Poi
open _root_.P2Mf6bd8d28 renaming h883 → _Poj
open _root_.P2Mf6bd8d28 renaming h884 → _Pok
open _root_.P2Mf6bd8d28 renaming h885 → _Pol
open _root_.P2Mf6bd8d28 renaming h886 → _Pom
open _root_.P2Mf6bd8d28 renaming h887 → _Pon
open _root_.P2Mf6bd8d28 renaming h888 → _Poo
open _root_.P2Mf6bd8d28 renaming h889 → _Pop
end
open _root_.P2Mf6bd8d28 renaming h334 → _P9a
open _root_.P2Mf6bd8d28 renaming h442 → _Pca
open _root_.P2Mf6bd8d28 renaming h445 → _Pcd
open _root_.P2Mf6bd8d28 renaming h446 → _Pce
open _root_.P2Mf6bd8d28 renaming h447 → _Pcf
open _root_.P2Mf6bd8d28 renaming h448 → _Pcg
open _root_.P2Mf6bd8d28 renaming h449 → _Pch
open _root_.P2Mf6bd8d28 renaming h450 → _Pci
open _root_.P2Mf6bd8d28 renaming h451 → _Pcj
open _root_.P2Mf6bd8d28 renaming h452 → _Pck
open _root_.P2Mf6bd8d28 renaming h453 → _Pcl
open _root_.P2Mf6bd8d28 renaming h454 → _Pcm
open _root_.P2Mf6bd8d28 renaming h455 → _Pcn
open _root_.P2Mf6bd8d28 renaming h456 → _Pco
open _root_.P2Mf6bd8d28 renaming h491 → _Pdn
open _root_.P2Mf6bd8d28 renaming h492 → _Pdo
open _root_.P2Mf6bd8d28 renaming h493 → _Pdp
open _root_.P2Mf6bd8d28 renaming h494 → _Pdq
open _root_.P2Mf6bd8d28 renaming h495 → _Pdr
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace InfoLossLAR.WorstCase
open AFT
open scoped BigOperators Classical
private theorem _root_.P2Mf6bd8d28.h861 (count : ℕ) (tape : Fin (Nat.size count) → Bool)
    (index : Fin count) :
    _root_.InfoLossLAR.WorstCase.boundedFinDraw count tape=some index ↔
      _root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size count) tape=Fin.castLE (Nat.lt_size_self count).le index := by
  unfold _root_.InfoLossLAR.WorstCase.boundedFinDraw
  dsimp only
  split_ifs with h
  · simp only [Option.some.injEq,Fin.ext_iff,Fin.val_mk,Fin.coe_castLE]
  · constructor
    · intro heq
      cases heq
    · intro heq
      have hv := congrArg Fin.val heq
      exact (h (by simpa only [Fin.coe_castLE] using hv.symm ▸ index.isLt)).elim
open _root_.P2Mf6bd8d28 renaming h861 → _Pnx
theorem _root_.P2Mf6bd8d28.h357 (count : ℕ) (index : Fin count) :
    (_root_.InfoLossLAR.WorstCase.boundedFinLaw count).weight (some index)=((2 : ℝ)^Nat.size count)⁻¹ := by
  simp only [_root_.InfoLossLAR.WorstCase.boundedFinLaw,_root_.AFT.FiniteDist.map_weight,_root_.AFT.FiniteDist.uniform_weight]
  simp_rw [_Pnx,←(_root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size count)).eq_symm_apply]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
open _root_.P2Mf6bd8d28 renaming h357 → _P9x
theorem _root_.P2Mf6bd8d28.h356 (count : ℕ) :
    (_root_.InfoLossLAR.WorstCase.boundedFinLaw count).weight none=1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess count := by
  have h := (_root_.InfoLossLAR.WorstCase.boundedFinLaw count).sum_one
  simp only [Fintype.sum_option,_P9x,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at h
  unfold _root_.InfoLossLAR.WorstCase.boundedFinSuccess
  rw [div_eq_mul_inv]
  linarith
open _root_.P2Mf6bd8d28 renaming h356 → _P9w
theorem _root_.P2Mf6bd8d28.h358 (count : ℕ) : 0 ≤ _root_.InfoLossLAR.WorstCase.boundedFinSuccess count ∧ _root_.InfoLossLAR.WorstCase.boundedFinSuccess count ≤ 1 := by
  have hp : (0 : ℝ)<(2 : ℝ)^Nat.size count := by positivity
  have hc : (count : ℝ) ≤ (2 : ℝ)^Nat.size count := by
    exact_mod_cast (Nat.lt_size_self count).le
  exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,(div_le_one hp).mpr hc⟩
open _root_.P2Mf6bd8d28 renaming h358 → _P9y
theorem _root_.P2Mf6bd8d28.h359 (count : ℕ) (hcount : 0<count) :
    (1/2 : ℝ) ≤ _root_.InfoLossLAR.WorstCase.boundedFinSuccess count := by
  have hs : 0<Nat.size count := Nat.size_pos.mpr hcount
  have hm : Nat.size count-1<Nat.size count := by omega
  have hpow : 2^(Nat.size count-1) ≤ count := Nat.lt_size.mp hm
  have hsucc : Nat.size count-1+1=Nat.size count := by omega
  have hcap : 2^Nat.size count ≤ 2*count := by
    calc
      _ = 2^(Nat.size count-1)*2 := by
        simpa only [Nat.succ_eq_add_one,hsucc] using Nat.pow_succ 2 (Nat.size count-1)
      _ ≤ count*2 := Nat.mul_le_mul_right 2 hpow
      _ = _ := Nat.mul_comm _ _
  have hcap' : (2 : ℝ)^Nat.size count ≤ 2*(count : ℝ) := by exact_mod_cast hcap
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^Nat.size count)).mpr
  nlinarith
open _root_.P2Mf6bd8d28 renaming h359 → _P9z
theorem _root_.P2Mf6bd8d28.h352 (q coordinates : ℕ) (hq : 0<q) (ticket : Fin (q^coordinates)) :
    _root_.InfoLossLAR.WorstCase.boundedBaseQDecode q coordinates hq ticket=finFunctionFinEquiv.symm ticket := by
  funext index
  apply Fin.ext
  rfl
open _root_.P2Mf6bd8d28 renaming h352 → _P9s
theorem _root_.P2Mf6bd8d28.h353 (q coordinates : ℕ) [NeZero q] (ticket : Fin (q^coordinates)) :
    _root_.InfoLossLAR.WorstCase.boundedFieldDecode q coordinates ticket=_root_.InfoLossLAR.WorstCase.boundedFieldEquiv q coordinates ticket := by
  unfold _root_.InfoLossLAR.WorstCase.boundedFieldDecode
  rw [_P9s]
  rfl
open _root_.P2Mf6bd8d28 renaming h353 → _P9t
private theorem _root_.P2Mf6bd8d28.h862 {A B : Type*} [Fintype A] [Fintype B]
    (equiv : A ≃ B) (test : B → ℝ) : avg (fun a => test (equiv a))=avg test := by
  unfold avg
  rw [equiv.sum_comp,Fintype.card_congr equiv]
open _root_.P2Mf6bd8d28 renaming h862 → _Pny
private theorem _root_.P2Mf6bd8d28.h864 {A : Type*} [Fintype A] [Nonempty A] (test : A → ℝ) :
    (_root_.AFT.FiniteDist.uniform A).expectation test=avg test := by
  simp only [_root_.AFT.FiniteDist.expectation,_root_.AFT.FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h864 → _Po0
theorem _root_.P2Mf6bd8d28.h354 (count : ℕ) (hcount : 0<count) (test : Fin count → ℝ) (fallback : ℝ) :
    avg (fun tape : Fin (Nat.size count) → Bool =>
      (_root_.InfoLossLAR.WorstCase.boundedFinDraw count tape).elim fallback test) =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess count*avg test+(1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess count)*fallback := by
  rw [←_Po0]
  have hmap := _root_.AFT.FiniteDist.expectation_map (_root_.AFT.FiniteDist.uniform (Fin (Nat.size count) → Bool))
    (_root_.InfoLossLAR.WorstCase.boundedFinDraw count) (fun output : Option (Fin count) => output.elim fallback test)
  change (_root_.InfoLossLAR.WorstCase.boundedFinLaw count).expectation (fun output => output.elim fallback test)=
    (_root_.AFT.FiniteDist.uniform (Fin (Nat.size count) → Bool)).expectation
      (fun tape => (_root_.InfoLossLAR.WorstCase.boundedFinDraw count tape).elim fallback test) at hmap
  rw [←hmap]
  unfold _root_.AFT.FiniteDist.expectation
  simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,_P9w,_P9x]
  rw [←Finset.mul_sum]
  have hc : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
  unfold _root_.InfoLossLAR.WorstCase.boundedFinSuccess avg
  rw [Fintype.card_fin]
  field_simp [hc] <;> ring
open _root_.P2Mf6bd8d28 renaming h354 → _P9u
theorem _root_.P2Mf6bd8d28.h355 {A : Type*} [Fintype A]
    (count : ℕ) (hcount : 0<count) (equiv : Fin count ≃ A) (test : A → ℝ) (fallback : ℝ) :
    avg (fun tape : Fin (Nat.size count) → Bool =>
      (_root_.InfoLossLAR.WorstCase.boundedFinDraw count tape).elim fallback (fun index => test (equiv index))) =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess count*avg test+(1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess count)*fallback := by
  rw [_P9u count hcount,_Pny]
open _root_.P2Mf6bd8d28 renaming h355 → _P9v
theorem _root_.P2Mf6bd8d28.h365 (F : Type*) (N samples labels : ℕ) (word : Fin (N+samples*labels) → F) :
    _root_.InfoLossLAR.WorstCase.boundedSplit F N samples labels word=_root_.InfoLossLAR.WorstCase.boundedSplitEquiv F N samples labels word := rfl
open _root_.P2Mf6bd8d28 renaming h365 → _Pa5
theorem _root_.P2Mf6bd8d28.h361 (q N samples labels : ℕ) [NeZero q]
    (tape : Fin (Nat.size (q^(N+samples*labels))) → Bool) :
    _root_.InfoLossLAR.WorstCase.boundedJointDraw q N samples labels tape =
      (_root_.InfoLossLAR.WorstCase.boundedFinDraw (q^(N+samples*labels)) tape).map (_root_.InfoLossLAR.WorstCase.boundedJointEquiv q N samples labels) := by
  unfold _root_.InfoLossLAR.WorstCase.boundedJointDraw
  generalize _root_.InfoLossLAR.WorstCase.boundedFinDraw (q^(N+samples*labels)) tape=chosen
  cases chosen with
  | none => rfl
  | some ticket =>
    simp only [Option.map_some,_Pa5,_P9t,_root_.InfoLossLAR.WorstCase.boundedJointEquiv,Equiv.trans_apply]
open _root_.P2Mf6bd8d28 renaming h361 → _Pa1
private theorem _root_.P2Mf6bd8d28.h863 {A B : Type*} [Fintype A] [Fintype B]
    (test : A × B → ℝ) :
    avg test=avg (fun first : A => avg (fun second : B => test (first,second))) := by
  simp only [avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,←Finset.sum_div]
  rw [div_div,mul_comm]
open _root_.P2Mf6bd8d28 renaming h863 → _Pnz
theorem _root_.P2Mf6bd8d28.h360 (q N samples labels : ℕ) [NeZero q]
    (test : ((Fin N → ZMod q) × (Fin samples → Fin labels → ZMod q)) → ℝ) (fallback : ℝ) :
    avg (fun tape : Fin (Nat.size (q^(N+samples*labels))) → Bool =>
      (_root_.InfoLossLAR.WorstCase.boundedJointDraw q N samples labels tape).elim fallback test) =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+samples*labels))*
        avg (fun auxiliary : Fin N → ZMod q => avg (fun marks : Fin samples → Fin labels → ZMod q =>
          test (auxiliary,marks)))+
        (1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+samples*labels)))*fallback := by
  have hpoint (tape : Fin (Nat.size (q^(N+samples*labels))) → Bool) :
      (_root_.InfoLossLAR.WorstCase.boundedJointDraw q N samples labels tape).elim fallback test =
        (_root_.InfoLossLAR.WorstCase.boundedFinDraw (q^(N+samples*labels)) tape).elim fallback
          (fun index => test (_root_.InfoLossLAR.WorstCase.boundedJointEquiv q N samples labels index)) := by
    rw [_Pa1]
    cases _root_.InfoLossLAR.WorstCase.boundedFinDraw (q^(N+samples*labels)) tape <;> rfl
  simp_rw [hpoint]
  rw [_P9v _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _),_Pnz]
open _root_.P2Mf6bd8d28 renaming h360 → _Pa0
theorem _root_.P2Mf6bd8d28.h362 (q N samples labels : ℕ) [NeZero q] :
    (1/2 : ℝ) ≤ _root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+samples*labels)) :=
  _P9z _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
open _root_.P2Mf6bd8d28 renaming h362 → _Pa2
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h352 → _P9s
open _root_.P2Mf6bd8d28 renaming h353 → _P9t
open _root_.P2Mf6bd8d28 renaming h354 → _P9u
open _root_.P2Mf6bd8d28 renaming h355 → _P9v
open _root_.P2Mf6bd8d28 renaming h356 → _P9w
open _root_.P2Mf6bd8d28 renaming h357 → _P9x
open _root_.P2Mf6bd8d28 renaming h358 → _P9y
open _root_.P2Mf6bd8d28 renaming h359 → _P9z
open _root_.P2Mf6bd8d28 renaming h360 → _Pa0
open _root_.P2Mf6bd8d28 renaming h361 → _Pa1
open _root_.P2Mf6bd8d28 renaming h362 → _Pa2
open _root_.P2Mf6bd8d28 renaming h365 → _Pa5
open _root_.P2Mf6bd8d28 renaming h861 → _Pnx
open _root_.P2Mf6bd8d28 renaming h862 → _Pny
open _root_.P2Mf6bd8d28 renaming h863 → _Pnz
open _root_.P2Mf6bd8d28 renaming h864 → _Po0
end
open _root_.P2Mf6bd8d28 renaming h352 → _P9s
open _root_.P2Mf6bd8d28 renaming h353 → _P9t
open _root_.P2Mf6bd8d28 renaming h354 → _P9u
open _root_.P2Mf6bd8d28 renaming h355 → _P9v
open _root_.P2Mf6bd8d28 renaming h356 → _P9w
open _root_.P2Mf6bd8d28 renaming h357 → _P9x
open _root_.P2Mf6bd8d28 renaming h358 → _P9y
open _root_.P2Mf6bd8d28 renaming h359 → _P9z
open _root_.P2Mf6bd8d28 renaming h360 → _Pa0
open _root_.P2Mf6bd8d28 renaming h361 → _Pa1
open _root_.P2Mf6bd8d28 renaming h362 → _Pa2
open _root_.P2Mf6bd8d28 renaming h365 → _Pa5
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinMachine
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open LARPlatformEncoding Polynomial
open scoped BigOperators
private theorem _root_.P2Mf6bd8d28.h867 (slots : List Unit) (base value : ℕ) :
    slots.foldl _root_.Integration9_9.LARCoinMachine.powerStep (base,value)=(base,value*base^slots.length) := by
  induction slots generalizing value with
  | nil => simp
  | cons slot slots ih =>
    simp only [List.foldl_cons,_root_.Integration9_9.LARCoinMachine.powerStep,ih,List.length_cons,pow_succ]
    congr 1
    ring
open _root_.P2Mf6bd8d28 renaming h867 → _Po3
theorem _root_.P2Mf6bd8d28.h760 (base : ℕ) (slots : List Unit) : _root_.Integration9_9.LARCoinMachine.powerWithSlots (base,slots)=base^slots.length := by
  simp only [_root_.Integration9_9.LARCoinMachine.powerWithSlots,_Po3,one_mul]
open _root_.P2Mf6bd8d28 renaming h760 → _Pl4
theorem _root_.P2Mf6bd8d28.h756 (base count ticket : ℕ) (slots : List Unit) (hslots : slots.length=count) :
    _root_.Integration9_9.LARCoinMachine.decodeBaseQ (base,(slots,ticket))=List.ofFn (fun index : Fin count => ticket/base^index.val%base) := by
  apply List.ext_getElem
  · simp only [_root_.Integration9_9.LARCoinMachine.decodeBaseQ,List.length_map,List.length_range,List.length_ofFn,hslots]
  · intro index hleft hright
    have hi : index<count := by simpa only [List.length_ofFn] using hright
    simp only [_root_.Integration9_9.LARCoinMachine.decodeBaseQ,List.getElem_map,List.getElem_range,_Pl4,List.length_take,
      hslots,Nat.min_eq_left hi.le,List.getElem_ofFn]
open _root_.P2Mf6bd8d28 renaming h756 → _Pl0
private theorem _root_.P2Mf6bd8d28.h868 (count : ℕ) (tape : Fin count → Bool) :
    Word.value (List.ofFn tape)=∑ index,(tape index).toNat*2^index.val := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.ofFn_succ,Word.value_cons,Fin.sum_univ_succ,Fin.val_zero,pow_zero,
      mul_one,Fin.val_succ]
    rw [ih]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [pow_succ]
    ring
open _root_.P2Mf6bd8d28 renaming h868 → _Po4
theorem _root_.P2Mf6bd8d28.h752 (count : ℕ) (tape : Fin count → Bool) :
    bitValue (List.ofFn tape)=(_root_.InfoLossLAR.WorstCase.boundedBoolTicket count tape).val := by
  rw [bitValue_eq_word,_Po4]
  change (∑ index,(tape index).toNat*2^index.val)=
    ∑ index,((finTwoEquiv.symm (tape index)).val)*2^index.val
  apply Finset.sum_congr rfl
  intro index _
  cases tape index <;> rfl
open _root_.P2Mf6bd8d28 renaming h752 → _Pkw
theorem _root_.P2Mf6bd8d28.h757 (q count : ℕ)
    (tape : Fin (Nat.size (q^count)) → Bool) :
    _root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q,(List.replicate count (),List.ofFn tape))=
      (decide ((_root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size (q^count)) tape).val<q^count),
        List.ofFn (fun index : Fin count =>
          (_root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size (q^count)) tape).val/q^index.val%q)) := by
  unfold _root_.Integration9_9.LARCoinMachine.jointDrawNumbers
  simp only [_Pl4,List.length_replicate]
  have ht : (List.ofFn tape).take (Nat.size (q^count))=List.ofFn tape := by
    exact List.take_of_length_le (by simp)
  rw [ht,_Pkw]
  congr 1
  exact _Pl0 q count _ _ (by simp)
open _root_.P2Mf6bd8d28 renaming h757 → _Pl1
theorem _root_.P2Mf6bd8d28.h753 (q count : ℕ) [NeZero q] (ticket : Fin (q^count)) (index : Fin count) :
    (_root_.InfoLossLAR.WorstCase.boundedFieldDecode q count ticket index).val=ticket.val/q^index.val%q := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl
open _root_.P2Mf6bd8d28 renaming h753 → _Pkx
end Integration9_9.LARCoinMachine
open _root_.P2Mf6bd8d28 renaming h752 → _Pkw
open _root_.P2Mf6bd8d28 renaming h753 → _Pkx
open _root_.P2Mf6bd8d28 renaming h756 → _Pl0
open _root_.P2Mf6bd8d28 renaming h757 → _Pl1
open _root_.P2Mf6bd8d28 renaming h760 → _Pl4
open _root_.P2Mf6bd8d28 renaming h867 → _Po3
open _root_.P2Mf6bd8d28 renaming h868 → _Po4
end
open _root_.P2Mf6bd8d28 renaming h752 → _Pkw
open _root_.P2Mf6bd8d28 renaming h753 → _Pkx
open _root_.P2Mf6bd8d28 renaming h756 → _Pl0
open _root_.P2Mf6bd8d28 renaming h757 → _Pl1
open _root_.P2Mf6bd8d28 renaming h760 → _Pl4
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open AFT
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h411 (n q : ℕ) (hq : q ≤ n + 1) :
    _root_.AFT.pathLoad n (fun j => ((q - (j.val + 1) : ℕ) : ℤ)) =
      (q : ℤ) • (Pi.single (0 : Fin (n + 1)) (1 : ℤ)) - _root_.AFT.injectionColumn n q := by
  rw [_P31]
  cases n with
  | zero =>
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Pi.sub_apply, Fin.snoc_zero, Fin.cons_zero, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, _root_.AFT.injectionColumn, Fin.val_zero]
    split_ifs <;> omega
  | succ n =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((q - 1 : ℕ) : ℤ) - 0 = (q : ℤ) * 1 - (if 0 < q then 1 else 0)
      split_ifs <;> omega
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Pi.sub_apply, Fin.cons_succ, Pi.smul_apply, Pi.single_apply,
          Fin.succ_ne_zero, if_false, smul_eq_mul, mul_zero]
        rw [Fin.succ_last, Fin.snoc_last]
        change (0 : ℤ) - ((q - (n + 1) : ℕ) : ℤ) = 0 - (if n + 1 < q then 1 else 0)
        split_ifs <;> omega
      · simp only [Pi.sub_apply, Fin.cons_succ, Pi.smul_apply, Pi.single_apply,
          Fin.succ_ne_zero, if_false, smul_eq_mul, mul_zero]
        rw [show k.castSucc.succ = k.succ.castSucc by rfl, Fin.snoc_castSucc]
        change ((q - (k.val + 2) : ℕ) : ℤ) - ((q - (k.val + 1) : ℕ) : ℤ) =
          0 - (if k.val + 1 < q then 1 else 0)
        split_ifs <;> omega
open _root_.P2Mf6bd8d28 renaming h411 → _Pbf
theorem _root_.P2Mf6bd8d28.h398 (n q : ℕ) (hq : q ≤ n + 1) :
    (_root_.InfoLossLAR.WorstCase.computableRoundingDirectionInteger n q (_root_.AFT.injectionColumn n q)).1 =
      (fun j => ((q - (j.val + 1) : ℕ) : ℤ)) := by
  apply _root_.AFT.pathLoad_injective n
  rw [_Pbf n q hq]
  apply _Pdd
  rw [_root_.AFT.totalCharge_sub, _root_.AFT.totalCharge_smul, _root_.AFT.totalCharge_injectionColumn n q hq]
  simp [_root_.AFT.totalCharge]
open _root_.P2Mf6bd8d28 renaming h398 → _Pb2
theorem _root_.P2Mf6bd8d28.h396 (q n : ℕ) (amount : ZMod q) :
    _root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection q n amount (Fin.last n) = amount := by
  simp [_root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection, _root_.InfoLossLAR.WorstCase.computableRoundingDirectionInteger]
open _root_.P2Mf6bd8d28 renaming h396 → _Pb0
theorem _root_.P2Mf6bd8d28.h393 (q n : ℕ) (hq : q ≤ n + 1)
    (amount : ZMod q) (j : Fin n) :
    _root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection q n amount j.castSucc =
      amount * ((q - (j.val + 1) : ℕ) : ZMod q) := by
  simp only [_root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection, Fin.lastCases_castSucc]
  rw [_Pb2 n q hq]
  simp
open _root_.P2Mf6bd8d28 renaming h393 → _Pax
theorem _root_.P2Mf6bd8d28.h394 (q n : ℕ) (hq : q ≤ n + 1)
    (amount : ZMod q) (j : Fin (n + 1)) :
    _root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection q n amount j =
      if j.val = n then amount else amount * ((q - min q (j.val + 1) : ℕ) : ZMod q) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [_Pb0]
  · rw [_Pax q n hq]
    have hk : k.val ≠ n := Nat.ne_of_lt k.isLt
    have he : q - min q (k.val + 1) = q - (k.val + 1) := by omega
    simp [hk, he]
open _root_.P2Mf6bd8d28 renaming h394 → _Pay
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h393 → _Pax
open _root_.P2Mf6bd8d28 renaming h394 → _Pay
open _root_.P2Mf6bd8d28 renaming h396 → _Pb0
open _root_.P2Mf6bd8d28 renaming h398 → _Pb2
open _root_.P2Mf6bd8d28 renaming h411 → _Pbf
end
open _root_.P2Mf6bd8d28 renaming h393 → _Pax
open _root_.P2Mf6bd8d28 renaming h394 → _Pay
open _root_.P2Mf6bd8d28 renaming h396 → _Pb0
open _root_.P2Mf6bd8d28 renaming h398 → _Pb2
open _root_.P2Mf6bd8d28 renaming h411 → _Pbf
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinMachine
open InfoLossLAR.WorstCase
theorem _root_.P2Mf6bd8d28.h755 (q N samples labels : ℕ) [NeZero q]
    (word : Fin (N + samples * labels) → ZMod q) :
    (List.ofFn (fun i => (word i).val)).take N =
      List.ofFn (fun i => ((_root_.InfoLossLAR.WorstCase.boundedSplit (ZMod q) N samples labels word).1 i).val) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn, _root_.InfoLossLAR.WorstCase.boundedSplit]
    rfl
open _root_.P2Mf6bd8d28 renaming h755 → _Pkz
theorem _root_.P2Mf6bd8d28.h754 (q N samples : ℕ) [NeZero q]
    (word : Fin (N + samples * 1) → ZMod q) :
    (List.ofFn (fun i => (word i).val)).drop N =
      List.ofFn (fun i => ((_root_.InfoLossLAR.WorstCase.boundedSplit (ZMod q) N samples 1 word).2 i 0).val) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn, Nat.mul_one]
    omega
  · intro i hi hj
    simp only [List.getElem_drop, List.getElem_ofFn, _root_.InfoLossLAR.WorstCase.boundedSplit]
    congr 2
    apply Fin.ext
    simp [finProdFinEquiv]
open _root_.P2Mf6bd8d28 renaming h754 → _Pky
theorem _root_.P2Mf6bd8d28.h759 (q N samples : ℕ) [NeZero q]
    (tape : Fin (Nat.size (q ^ (N + samples * 1))) → Bool)
    (coins : (Fin N → ZMod q) × (Fin samples → Fin 1 → ZMod q))
    (hsuccess : _root_.InfoLossLAR.WorstCase.boundedJointDraw q N samples 1 tape = some coins) :
    let decoded := _root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q, (List.replicate (N + samples * 1) (), List.ofFn tape))
    decoded.1 = true ∧
      decoded.2.take N = List.ofFn (fun i => (coins.1 i).val) ∧
      decoded.2.drop N = List.ofFn (fun i => (coins.2 i 0).val) := by
  rw [_Pl1]
  unfold _root_.InfoLossLAR.WorstCase.boundedJointDraw _root_.InfoLossLAR.WorstCase.boundedFinDraw at hsuccess
  dsimp only at hsuccess ⊢
  split_ifs at hsuccess with hticket
  · have hc := Option.some.inj hsuccess
    subst coins
    simp only [decide_eq_true_eq, hticket, true_and]
    have hd : (List.ofFn (fun index : Fin (N + samples * 1) =>
        (_root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size (q ^ (N + samples * 1))) tape).val / q ^ index.val % q)) =
        List.ofFn (fun index =>
          (_root_.InfoLossLAR.WorstCase.boundedFieldDecode q (N + samples * 1)
            ⟨(_root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size (q ^ (N + samples * 1))) tape).val,hticket⟩ index).val) := by
      congr 1
      funext index
      exact (_Pkx q (N + samples * 1)
        ⟨(_root_.InfoLossLAR.WorstCase.boundedBoolTicket (Nat.size (q ^ (N + samples * 1))) tape).val, hticket⟩ index).symm
    rw [hd]
    exact ⟨_Pkz q N samples 1 _, _Pky q N samples _⟩
open _root_.P2Mf6bd8d28 renaming h759 → _Pl3
theorem _root_.P2Mf6bd8d28.h758 (q N samples : ℕ) [NeZero q]
    (tape : Fin (Nat.size (q ^ (N + samples * 1))) → Bool)
    (hfailure : _root_.InfoLossLAR.WorstCase.boundedJointDraw q N samples 1 tape = none) :
    (_root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q, (List.replicate (N + samples * 1) (), List.ofFn tape))).1 = false := by
  rw [_Pl1]
  unfold _root_.InfoLossLAR.WorstCase.boundedJointDraw _root_.InfoLossLAR.WorstCase.boundedFinDraw at hfailure
  dsimp only at hfailure ⊢
  split_ifs at hfailure with hticket
  exact decide_eq_false hticket
open _root_.P2Mf6bd8d28 renaming h758 → _Pl2
end Integration9_9.LARCoinMachine
open _root_.P2Mf6bd8d28 renaming h754 → _Pky
open _root_.P2Mf6bd8d28 renaming h755 → _Pkz
open _root_.P2Mf6bd8d28 renaming h758 → _Pl2
open _root_.P2Mf6bd8d28 renaming h759 → _Pl3
end
open _root_.P2Mf6bd8d28 renaming h754 → _Pky
open _root_.P2Mf6bd8d28 renaming h755 → _Pkz
open _root_.P2Mf6bd8d28 renaming h758 → _Pl2
open _root_.P2Mf6bd8d28 renaming h759 → _Pl3
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace InfoLossLAR.WorstCase
open AFT Matrix QAlgorithms.Complexity
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h363 (D : Family) (lam : ℕ) (pp fallback : Str)
    (q N d ℓ t : ℕ) [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q))
    (input : Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) :
    avg (fun tape : Fin (Nat.size (q^(N+t*ℓ))) → Bool =>
      acceptProb D (_root_.InfoLossLAR.WorstCase.boundedRankOnePre lam pp fallback q N d ℓ t direction tape input)) =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ))*
        avg (fun auxiliary : Fin N → ZMod q =>
          avg (fun marks : Fin t → Fin ℓ → ZMod q =>
            acceptProb D (_root_.InfoLossLAR.WorstCase.rankOneEncodedQuery lam pp q N d ℓ t direction (auxiliary,marks) input)))+
        (1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ)))*acceptProb D fallback := by
  have hpoint (tape : Fin (Nat.size (q^(N+t*ℓ))) → Bool) :
      acceptProb D (_root_.InfoLossLAR.WorstCase.boundedRankOnePre lam pp fallback q N d ℓ t direction tape input) =
      (_root_.InfoLossLAR.WorstCase.boundedJointDraw q N t ℓ tape).elim (acceptProb D fallback)
        (fun coins => acceptProb D (_root_.InfoLossLAR.WorstCase.rankOneEncodedQuery lam pp q N d ℓ t direction coins input)) := by
    unfold _root_.InfoLossLAR.WorstCase.boundedRankOnePre
    cases _root_.InfoLossLAR.WorstCase.boundedJointDraw q N t ℓ tape <;> rfl
  simp_rw [hpoint]
  exact _Pa0 q N t ℓ _ _
open _root_.P2Mf6bd8d28 renaming h363 → _Pa3
private theorem _root_.P2Mf6bd8d28.h860 {A : Type*} [Fintype A] [Nonempty A] (test : A → ℝ) :
    (_root_.AFT.FiniteDist.uniform A).expectation test=avg test := by
  simp only [_root_.AFT.FiniteDist.expectation,_root_.AFT.FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h860 → _Pnw
private theorem _root_.P2Mf6bd8d28.h854 {A : Type*} [Fintype A] (first second : A → ℝ) :
    avg (fun a => first a+second a)=avg first+avg second := by
  simp only [avg,Finset.sum_add_distrib,add_div]
open _root_.P2Mf6bd8d28 renaming h854 → _Pnq
private theorem _root_.P2Mf6bd8d28.h856 {A : Type*} [Fintype A] (scalar : ℝ) (test : A → ℝ) :
    avg (fun a => scalar*test a)=scalar*avg test := by
  simp only [avg,←Finset.mul_sum,mul_div_assoc]
open _root_.P2Mf6bd8d28 renaming h856 → _Pns
private theorem _root_.P2Mf6bd8d28.h855 {A : Type*} [Fintype A] [Nonempty A] (value : ℝ) :
    avg (fun _ : A => value)=value := by
  rw [←_Pnw]
  exact _root_.AFT.FiniteDist.expectation_const _ _
open _root_.P2Mf6bd8d28 renaming h855 → _Pnr
private theorem _root_.P2Mf6bd8d28.h857 {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (law : _root_.AFT.FiniteDist A) (test : A → B → ℝ) :
    law.expectation (fun a => avg (test a))=avg (fun b => law.expectation (fun a => test a b)) := by
  simp_rw [←_Pnw (A := B)]
  exact _root_.AFT.FiniteDist.expectation_comm law (_root_.AFT.FiniteDist.uniform B) test
open _root_.P2Mf6bd8d28 renaming h857 → _Pnt
private theorem _root_.P2Mf6bd8d28.h859 (q N d t : ℕ) [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) (secret : Fin N → ZMod q)
    (test : (Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) → ℝ) :
    (_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw q N d t source secret).expectation test =
      avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
        ∑ errors : Fin t → Fin d → ZMod q,(∏ index,source.weight (errors index))*
          test (fun index => (matrices index,(matrices index).mulVec secret+errors index))) := by
  rw [_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod,
    _Pnw]
  rfl
open _root_.P2Mf6bd8d28 renaming h859 → _Pnv
private theorem _root_.P2Mf6bd8d28.h858 (q N d t : ℕ) [NeZero q]
    (test : (Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) → ℝ) :
    (_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw q N d t).expectation test =
      avg (fun matrices : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
        avg (fun responses : Fin t → Fin d → ZMod q =>
          test (fun index => (matrices index,responses index)))) := by
  rw [_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod]
  simp only [_Pnw,Function.comp_def]
open _root_.P2Mf6bd8d28 renaming h858 → _Pnu
theorem _root_.P2Mf6bd8d28.h444 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    avg (fun secret : Fin N → ZMod q =>
      (_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw q N d t source secret).expectation (fun input =>
        avg (fun auxiliary : Fin N → ZMod q =>
          avg (fun marks : Fin t → Fin ℓ → ZMod q =>
            acceptProb D (_root_.InfoLossLAR.WorstCase.rankOneEncodedQuery lam pp q N d ℓ t direction (auxiliary,marks) input))))) =
    _root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t source direction := by
  rw [_Pdq]
  apply congrArg avg
  funext secret
  rw [_Pnt]
  simp_rw [_Pnv]
  rfl
open _root_.P2Mf6bd8d28 renaming h444 → _Pcc
theorem _root_.P2Mf6bd8d28.h443 (D : Family) (lam : ℕ) (pp : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    (_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw q N d t).expectation (fun input =>
      avg (fun auxiliary : Fin N → ZMod q =>
        avg (fun marks : Fin t → Fin ℓ → ZMod q =>
          acceptProb D (_root_.InfoLossLAR.WorstCase.rankOneEncodedQuery lam pp q N d ℓ t direction (auxiliary,marks) input)))) =
    _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction := by
  rw [_Pdo]
  rw [_Pnt]
  simp_rw [_Pnu]
  rfl
open _root_.P2Mf6bd8d28 renaming h443 → _Pcb
theorem _root_.P2Mf6bd8d28.h488 (D : Family) (lam : ℕ) (pp fallback : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR D lam pp fallback q N d ℓ t source direction =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ))*_root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t source direction+
        (1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ)))*acceptProb D fallback := by
  unfold _root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR
  simp_rw [_Pa3,_root_.AFT.FiniteDist.expectation_add,
    _root_.AFT.FiniteDist.expectation_const_mul,_root_.AFT.FiniteDist.expectation_const]
  rw [_Pnq,_Pns,_Pnr,_Pcc]
open _root_.P2Mf6bd8d28 renaming h488 → _Pdk
theorem _root_.P2Mf6bd8d28.h487 (D : Family) (lam : ℕ) (pp fallback : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR D lam pp fallback q N d ℓ t direction =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ))*_root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction+
        (1-_root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ)))*acceptProb D fallback := by
  unfold _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR
  simp_rw [_Pa3,_root_.AFT.FiniteDist.expectation_add,
    _root_.AFT.FiniteDist.expectation_const_mul,_root_.AFT.FiniteDist.expectation_const]
  rw [_Pcb]
open _root_.P2Mf6bd8d28 renaming h487 → _Pdj
theorem _root_.P2Mf6bd8d28.h364 (D : Family) (lam : ℕ) (pp fallback : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR D lam pp fallback q N d ℓ t source direction-
      _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR D lam pp fallback q N d ℓ t direction =
      _root_.InfoLossLAR.WorstCase.boundedFinSuccess (q^(N+t*ℓ))*(_root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t source direction-
        _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction) := by
  rw [_Pdk,_Pdj]
  ring
open _root_.P2Mf6bd8d28 renaming h364 → _Pa4
theorem _root_.P2Mf6bd8d28.h514 (D : Family) (lam : ℕ) (pp fallback : Str)
    (q N d ℓ t : ℕ) [Fact q.Prime] [NeZero q]
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (direction : (Fin ℓ → ZMod q) → (Fin d → ZMod q)) :
    |_root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t source direction-
      _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction| ≤
      2*|_root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR D lam pp fallback q N d ℓ t source direction-
        _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR D lam pp fallback q N d ℓ t direction| := by
  rw [_Pa4,abs_mul,
    abs_of_nonneg (_P9y _).1]
  have h := mul_le_mul_of_nonneg_right (_Pa2 q N t ℓ)
    (abs_nonneg (_root_.InfoLossLAR.WorstCase.prRankOneRealLAR D lam pp q N d ℓ t source direction-
      _root_.InfoLossLAR.WorstCase.prRankOneIdealLAR D lam pp q N d ℓ t direction))
  linarith
open _root_.P2Mf6bd8d28 renaming h514 → _Pea
theorem _root_.P2Mf6bd8d28.h333 (D : Family) (lam : ℕ) (pp fallback : Str)
    (q N n t : ℕ) [Fact q.Prime] [NeZero q] (hq : q ≤ n+1) :
    advLAR D lam pp q N (n+1) 1 t (fun input => fun _ : Fin 1 => fT63 q (n+1) input) ≤
      (2*(q : ℝ))*|_root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR D lam pp fallback q N (n+1) 1 t
          (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q (n+1)) (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n)-
        _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR D lam pp fallback q N (n+1) 1 t
          (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n)|+((q : ℝ)^N)⁻¹ := by
  have h := _P9a D lam pp q N n t hq
  have hg := _Pea D lam pp fallback q N (n+1) 1 t
    (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q (n+1)) (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  nlinarith
open _root_.P2Mf6bd8d28 renaming h333 → _P99
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h333 → _P99
open _root_.P2Mf6bd8d28 renaming h363 → _Pa3
open _root_.P2Mf6bd8d28 renaming h364 → _Pa4
open _root_.P2Mf6bd8d28 renaming h443 → _Pcb
open _root_.P2Mf6bd8d28 renaming h444 → _Pcc
open _root_.P2Mf6bd8d28 renaming h487 → _Pdj
open _root_.P2Mf6bd8d28 renaming h488 → _Pdk
open _root_.P2Mf6bd8d28 renaming h514 → _Pea
open _root_.P2Mf6bd8d28 renaming h854 → _Pnq
open _root_.P2Mf6bd8d28 renaming h855 → _Pnr
open _root_.P2Mf6bd8d28 renaming h856 → _Pns
open _root_.P2Mf6bd8d28 renaming h857 → _Pnt
open _root_.P2Mf6bd8d28 renaming h858 → _Pnu
open _root_.P2Mf6bd8d28 renaming h859 → _Pnv
open _root_.P2Mf6bd8d28 renaming h860 → _Pnw
end
open _root_.P2Mf6bd8d28 renaming h333 → _P99
open _root_.P2Mf6bd8d28 renaming h363 → _Pa3
open _root_.P2Mf6bd8d28 renaming h364 → _Pa4
open _root_.P2Mf6bd8d28 renaming h443 → _Pcb
open _root_.P2Mf6bd8d28 renaming h444 → _Pcc
open _root_.P2Mf6bd8d28 renaming h487 → _Pdj
open _root_.P2Mf6bd8d28 renaming h488 → _Pdk
open _root_.P2Mf6bd8d28 renaming h514 → _Pea
namespace InfoLossLAR.WorstCase.boundedSplit
end InfoLossLAR.WorstCase.boundedSplit
namespace InfoLossLAR.WorstCase.computableFixedRoundingDirection
end InfoLossLAR.WorstCase.computableFixedRoundingDirection
namespace InfoLossLAR.WorstCase.computableRoundingDirectionInteger
end InfoLossLAR.WorstCase.computableRoundingDirectionInteger
namespace Integration9_9.LARCoinMachine
end Integration9_9.LARCoinMachine
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARRankOneMachine
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open LARPlatformEncoding LARCoinMachine TM2PlatformSerialization
theorem _root_.P2Mf6bd8d28.h765 (q n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (amount : ZMod q) (index : Fin (n+1)) :
    (_root_.Integration9_9.LARRankOneMachine.directionNumber q (n+1) amount.val index.val : ZMod q)=
      _root_.InfoLossLAR.WorstCase.computableFixedRoundingDirection q n amount index := by
  rw [_Pay q n hq]
  have he : q-min q (index.val+1)=q-(index.val+1) := by omega
  by_cases hi : index.val=n
  · have hi' : index.val+1=n+1 := by omega
    simp [_root_.Integration9_9.LARRankOneMachine.directionNumber,hi,hi',he]
  · have hi' : index.val+1 ≠ n+1 := by omega
    simp [_root_.Integration9_9.LARRankOneMachine.directionNumber,hi,hi',he]
open _root_.P2Mf6bd8d28 renaming h765 → _Pl9
private theorem _root_.P2Mf6bd8d28.h891 (q : ℕ) [NeZero q] (value : ZMod q) :
    ((q-value.val%q : ℕ) : ZMod q) = -value := by
  rw [Nat.mod_eq_of_lt (ZMod.val_lt value),Nat.cast_sub (ZMod.val_lt value).le]
  simp
open _root_.P2Mf6bd8d28 renaming h891 → _Por
theorem _root_.P2Mf6bd8d28.h768 (q N n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (auxiliary : Fin N → ZMod q) (mark : ZMod q)
    (matrix : Matrix (Fin (n+1)) (Fin N) (ZMod q)) (response : Fin (n+1) → ZMod q)
    (row : Fin (n+1)) (column : Fin N) :
    _root_.Integration9_9.LARRankOneMachine.rankOneNaturalEntry ((q,(List.ofFn (fun i => (auxiliary i).val),
      (mark.val,(List.ofFn (fun i => List.ofFn (fun j => (matrix i j).val)),
        List.ofFn (fun i => (response i).val))))),(row.val,column.val)) =
      ((_root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) matrix response
        (fun _ : Fin 1 => mark)).1 row column).val := by
  have hz : ((_root_.Integration9_9.LARRankOneMachine.rankOneNaturalEntry ((q,(List.ofFn (fun i => (auxiliary i).val),
      (mark.val,(List.ofFn (fun i => List.ofFn (fun j => (matrix i j).val)),
        List.ofFn (fun i => (response i).val))))),(row.val,column.val))) : ZMod q) =
      (_root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) matrix response
        (fun _ : Fin 1 => mark)).1 row column := by
    simp only [_root_.Integration9_9.LARRankOneMachine.rankOneNaturalEntry,List.length_ofFn]
    simp only [List.getElem?_ofFn,row.isLt,column.isLt,dif_pos,Fin.eta,Option.getD_some]
    simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val]
    rw [_Por,_Pl9 q n hq]
    rfl
  have hv := congrArg ZMod.val hz
  simpa only [ZMod.val_natCast,_root_.Integration9_9.LARRankOneMachine.rankOneNaturalEntry,Nat.mod_mod] using hv
open _root_.P2Mf6bd8d28 renaming h768 → _Plc
private theorem _root_.P2Mf6bd8d28.h890 {α : Type*} (count : ℕ) (f : ℕ → α) :
    (List.range count).map f=List.ofFn (fun index : Fin count => f index.val) := by
  apply List.ext_getElem <;> simp
open _root_.P2Mf6bd8d28 renaming h890 → _Poq
theorem _root_.P2Mf6bd8d28.h769 (q N n : ℕ) [NeZero q] (hq : q ≤ n+1)
    (auxiliary : Fin N → ZMod q) (mark : ZMod q)
    (matrix : Matrix (Fin (n+1)) (Fin N) (ZMod q)) (response : Fin (n+1) → ZMod q) :
    _root_.Integration9_9.LARRankOneMachine.rankOneNaturalSample (q,(List.ofFn (fun i => (auxiliary i).val),
      (mark.val,(List.ofFn (fun i => List.ofFn (fun j => (matrix i j).val)),
        List.ofFn (fun i => (response i).val))))) =
      (List.ofFn (fun row => List.ofFn (fun column =>
        ((_root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) matrix response
          (fun _ : Fin 1 => mark)).1 row column).val)),
        List.ofFn (fun _ : Fin 1 => mark.val)) := by
  apply Prod.ext
  · simp only [_root_.Integration9_9.LARRankOneMachine.rankOneNaturalSample,List.length_ofFn]
    rw [_Poq]
    apply congrArg List.ofFn
    funext row
    simp only [List.getElem?_ofFn,row.isLt,dif_pos,Fin.eta,Option.getD_some,List.length_ofFn]
    rw [_Poq]
    apply congrArg List.ofFn
    funext column
    exact _Plc q N n hq auxiliary mark matrix response row column
  · simp [_root_.Integration9_9.LARRankOneMachine.rankOneNaturalSample,List.ofFn_succ]
open _root_.P2Mf6bd8d28 renaming h769 → _Pld
private theorem _root_.P2Mf6bd8d28.h894 {α β : Type*} {count : ℕ} (first : Fin count → α) (second : Fin count → β) :
    (List.ofFn first).zip (List.ofFn second)=List.ofFn (fun index => (first index,second index)) := by
  apply List.ext_getElem <;> simp
open _root_.P2Mf6bd8d28 renaming h894 → _Pou
theorem _root_.P2Mf6bd8d28.h770 (q N n t : ℕ) [NeZero q] (hq : q ≤ n+1)
    (auxiliary : Fin N → ZMod q) (marks : Fin t → ZMod q)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.rankOneNaturalTable (q,(List.ofFn (fun i => (auxiliary i).val),
      (List.ofFn (fun i => (marks i).val),List.ofFn (fun index =>
        (List.ofFn (fun i => List.ofFn (fun j => ((table index).1 i j).val)),
          List.ofFn (fun i => ((table index).2 i).val)))))) =
      List.ofFn (fun index =>
        (List.ofFn (fun row => List.ofFn (fun column =>
          ((_root_.InfoLossLAR.WorstCase.larRankOnePreprocess auxiliary (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n)
            (table index).1 (table index).2 (fun _ : Fin 1 => marks index)).1 row column).val)),
          List.ofFn (fun _ : Fin 1 => (marks index).val))) := by
  unfold _root_.Integration9_9.LARRankOneMachine.rankOneNaturalTable
  rw [_Pou,List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact _Pld q N n hq auxiliary (marks index) (table index).1 (table index).2
open _root_.P2Mf6bd8d28 renaming h770 → _Ple
private theorem _root_.P2Mf6bd8d28.h892 {q N n t : ℕ}
    (table : Fin (t+1) → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedAuxiliarySlots (List.ofFn (fun index =>
      (List.ofFn (fun i => List.ofFn (fun j => ((table index).1 i j).val)),
        List.ofFn (fun i => ((table index).2 i).val))))=List.replicate N () := by
  simp only [_root_.Integration9_9.LARRankOneMachine.observedAuxiliarySlots,List.ofFn_succ,List.head?_cons,Option.getD_some]
  rw [List.map_const']
  simp
open _root_.P2Mf6bd8d28 renaming h892 → _Pos
theorem _root_.P2Mf6bd8d28.h766 {q N n t : ℕ} (ht : 0<t)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedJointSlots (List.ofFn (fun index =>
      (List.ofFn (fun i => List.ofFn (fun j => ((table index).1 i j).val)),
        List.ofFn (fun i => ((table index).2 i).val))))=List.replicate (N+t) () := by
  cases t with
  | zero => omega
  | succ t =>
    rw [_root_.Integration9_9.LARRankOneMachine.observedJointSlots,_Pos,List.map_const']
    simp only [List.length_ofFn,←List.replicate_add]
open _root_.P2Mf6bd8d28 renaming h766 → _Pla
theorem _root_.P2Mf6bd8d28.h767 {q N n t : ℕ} (ht : 0<t) (lam width : ℕ)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))=q^(N+t) := by
  unfold _root_.Integration9_9.LARRankOneMachine.observedTicketCount
  have hinput := _root_.Integration9_9.LARPlatformEncoding.readObservedInput_append lam (encB q++encB N++encB (n+1)++encB width) [] table
  simp only [List.append_nil] at hinput
  rw [hinput]
  dsimp only
  have hpp := _root_.Integration9_9.LARPlatformEncoding.readParameters_append q N (n+1) width []
  simp only [List.append_nil] at hpp
  rw [hpp,_Pla ht table,_Pl4,List.length_replicate]
open _root_.P2Mf6bd8d28 renaming h767 → _Plb
theorem _root_.P2Mf6bd8d28.h761 (fallback : Str) (q N n t : ℕ) [NeZero q]
    (hq : q ≤ n+1) (ht : 0<t) (lam width : ℕ)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q))
    (tape : Fin (Nat.size (q^(N+t*1))) → Bool) :
    _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape)
      (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))) =
      _root_.InfoLossLAR.WorstCase.boundedRankOnePre lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
        (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) tape table := by
  let pp := encB q++encB N++encB (n+1)++encB width
  let values : List _root_.Integration9_9.LARRankOneMachine.NaturalSample := List.ofFn (fun index =>
    (List.ofFn (fun i => List.ofFn (fun j => ((table index).1 i j).val)),
      List.ofFn (fun i => ((table index).2 i).val)))
  let input : _root_.Integration9_9.LARRankOneMachine.ObservedInput := (unary lam,(pp,values))
  have hinput : _root_.Integration9_9.LARPlatformEncoding.readObservedInput (encInput lam pp (encTable table))=([],input) := by
    simpa only [List.append_nil] using _root_.Integration9_9.LARPlatformEncoding.readObservedInput_append lam pp [] table
  have hs : _root_.Integration9_9.LARPlatformEncoding.readS (encS (encInput lam pp (encTable table)))=([],encInput lam pp (encTable table)) := by
    simpa only [List.append_nil] using _root_.Integration9_9.LARPlatformEncoding.readS_append (encInput lam pp (encTable table)) []
  have hread : _root_.Integration9_9.LARRankOneMachine.readCoinObserved (encPair (List.ofFn tape) (encInput lam pp (encTable table)))=
      (List.ofFn tape,input) := by
    simp only [_root_.Integration9_9.LARRankOneMachine.readCoinObserved,encPair,_root_.Integration9_9.LARPlatformEncoding.readS_append,hs,hinput]
  have haux : _root_.Integration9_9.LARRankOneMachine.observedAuxiliarySlots values=List.replicate N () := by
    cases t with
    | zero => omega
    | succ t => exact _Pos table
  have hslots : _root_.Integration9_9.LARRankOneMachine.observedJointSlots values=List.replicate (N+t*1) () := by
    simpa only [Nat.mul_one] using _Pla ht table
  have hpp : _root_.Integration9_9.LARPlatformEncoding.readParameters pp=([],(q,(N,(n+1,width)))) := by
    simpa only [List.append_nil] using _root_.Integration9_9.LARPlatformEncoding.readParameters_append q N (n+1) width []
  have hcontext : _root_.Integration9_9.LARRankOneMachine.makeBoundedContext (List.ofFn tape,input)=
      (input,(q,(N,_root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q,(List.replicate (N+t*1) (),List.ofFn tape))))) := by
    unfold _root_.Integration9_9.LARRankOneMachine.makeBoundedContext
    dsimp only [input]
    rw [hpp,haux,hslots,List.length_replicate]
  change _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape)
      (encInput lam pp (encTable table))) = _
  rw [_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre,hread,hcontext]
  unfold _root_.InfoLossLAR.WorstCase.boundedRankOnePre
  cases hdraw : _root_.InfoLossLAR.WorstCase.boundedJointDraw q N t 1 tape with
  | none =>
    have hf := _Pl2 q N t tape hdraw
    simp only [_root_.Integration9_9.LARRankOneMachine.renderBoundedContext,hf,Bool.false_eq_true,if_false]
  | some coins =>
    have hc := _Pl3 q N t tape coins hdraw
    dsimp only at hc
    simp only [_root_.Integration9_9.LARRankOneMachine.renderBoundedContext,hc.1,if_true]
    rw [hc.2.1,hc.2.2]
    dsimp only [input]
    rw [_Ple q N n t hq coins.1 (fun index => coins.2 index 0) table]
    trans encInput lam pp (encTable (fun index => _root_.InfoLossLAR.WorstCase.larRankOnePreprocess coins.1
      (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) (table index).1 (table index).2
      (fun _ : Fin 1 => coins.2 index 0)))
    · exact _root_.Integration9_9.LARPlatformEncoding.serializeObservedInput_ofFn lam pp (fun index => _root_.InfoLossLAR.WorstCase.larRankOnePreprocess coins.1
        (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) (table index).1 (table index).2
        (fun _ : Fin 1 => coins.2 index 0))
    · unfold _root_.InfoLossLAR.WorstCase.rankOneEncodedQuery
      apply congrArg (fun output => encInput lam pp (encTable output))
      funext index
      have hm : (fun _ : Fin 1 => coins.2 index 0)=coins.2 index := by
        funext coordinate
        exact congrArg (coins.2 index) (Subsingleton.elim _ _)
      rw [hm]
open _root_.P2Mf6bd8d28 renaming h761 → _Pl5
theorem _root_.P2Mf6bd8d28.h764 (fallback coins observed : Str) :
    _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair coins observed)=
      _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
        (encPair (coins.take (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount observed))) observed) := by
  let input := (_root_.Integration9_9.LARPlatformEncoding.readObservedInput observed).2
  let q := (_root_.Integration9_9.LARPlatformEncoding.readParameters input.2.1).2.1
  let slots := _root_.Integration9_9.LARRankOneMachine.observedJointSlots input.2.2
  have hdraw : _root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q,(slots,coins.take (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount observed))))=
      _root_.Integration9_9.LARCoinMachine.jointDrawNumbers (q,(slots,coins)) := by
    unfold _root_.Integration9_9.LARCoinMachine.jointDrawNumbers
    dsimp only [_root_.Integration9_9.LARRankOneMachine.observedTicketCount,input,q,slots]
    rw [List.take_take,Nat.min_self]
  unfold _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre
  rw [_root_.Integration9_9.LARRankOneMachine.readCoinObserved_encPair,_root_.Integration9_9.LARRankOneMachine.readCoinObserved_encPair]
  unfold _root_.Integration9_9.LARRankOneMachine.makeBoundedContext
  dsimp only
  rw [hdraw]
open _root_.P2Mf6bd8d28 renaming h764 → _Pl8
private theorem _root_.P2Mf6bd8d28.h893 {short long : ℕ} (h : short ≤ long) (tape : Fin long → Bool) :
    (List.ofFn tape).take short=List.ofFn (fun index => tape (Fin.castLE h index)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left h]
  · intro index hleft hright
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl
open _root_.P2Mf6bd8d28 renaming h893 → _Pot
theorem _root_.P2Mf6bd8d28.h763 (fallback : Str) (q N n t : ℕ) [NeZero q]
    (hq : q ≤ n+1) (ht : 0<t) (lam width long : ℕ)
    (hbits : Nat.size (q^(N+t*1)) ≤ long)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q))
    (tape : Fin long → Bool) :
    _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape)
      (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))) =
      _root_.InfoLossLAR.WorstCase.boundedRankOnePre lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
        (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) (fun index => tape (Fin.castLE hbits index)) table := by
  rw [_Pl8]
  rw [_Plb ht lam width table]
  have htake : (List.ofFn tape).take (Nat.size (q^(N+t)))=
      List.ofFn (fun index => tape (Fin.castLE hbits index)) := by
    simpa only [Nat.mul_one] using _Pot hbits tape
  rw [htake]
  exact _Pl5 fallback q N n t hq ht lam width table _
open _root_.P2Mf6bd8d28 renaming h763 → _Pl7
theorem _root_.P2Mf6bd8d28.h762 (D : Family) (fallback : Str)
    (q N n t : ℕ) [NeZero q] (hq : q ≤ n+1) (ht : 0<t) (lam width long : ℕ)
    (hbits : Nat.size (q^(N+t*1)) ≤ long)
    (table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
    avg (fun tape : Fin long → Bool => acceptProb D
      (_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape)
        (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))))) =
      avg (fun tape : Fin (Nat.size (q^(N+t*1))) → Bool => acceptProb D
        (_root_.InfoLossLAR.WorstCase.boundedRankOnePre lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
          (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) tape table)) := by
  simp_rw [_Pl7 fallback q N n t hq ht lam width long hbits table]
  exact _Pgg hbits (fun tape : Fin (Nat.size (q^(N+t*1))) → Bool =>
    acceptProb D (_root_.InfoLossLAR.WorstCase.boundedRankOnePre lam (encB q++encB N++encB (n+1)++encB width)
      fallback q N (n+1) 1 t (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) tape table))
open _root_.P2Mf6bd8d28 renaming h762 → _Pl6
end Integration9_9.LARRankOneMachine
open _root_.P2Mf6bd8d28 renaming h761 → _Pl5
open _root_.P2Mf6bd8d28 renaming h762 → _Pl6
open _root_.P2Mf6bd8d28 renaming h763 → _Pl7
open _root_.P2Mf6bd8d28 renaming h764 → _Pl8
open _root_.P2Mf6bd8d28 renaming h765 → _Pl9
open _root_.P2Mf6bd8d28 renaming h766 → _Pla
open _root_.P2Mf6bd8d28 renaming h767 → _Plb
open _root_.P2Mf6bd8d28 renaming h768 → _Plc
open _root_.P2Mf6bd8d28 renaming h769 → _Pld
open _root_.P2Mf6bd8d28 renaming h770 → _Ple
open _root_.P2Mf6bd8d28 renaming h890 → _Poq
open _root_.P2Mf6bd8d28 renaming h891 → _Por
open _root_.P2Mf6bd8d28 renaming h892 → _Pos
open _root_.P2Mf6bd8d28 renaming h893 → _Pot
open _root_.P2Mf6bd8d28 renaming h894 → _Pou
end
open _root_.P2Mf6bd8d28 renaming h761 → _Pl5
open _root_.P2Mf6bd8d28 renaming h762 → _Pl6
open _root_.P2Mf6bd8d28 renaming h763 → _Pl7
open _root_.P2Mf6bd8d28 renaming h764 → _Pl8
open _root_.P2Mf6bd8d28 renaming h765 → _Pl9
open _root_.P2Mf6bd8d28 renaming h766 → _Pla
open _root_.P2Mf6bd8d28 renaming h767 → _Plb
open _root_.P2Mf6bd8d28 renaming h768 → _Plc
open _root_.P2Mf6bd8d28 renaming h769 → _Pld
open _root_.P2Mf6bd8d28 renaming h770 → _Ple
namespace Integration9_9.TM2NativePrime
end Integration9_9.TM2NativePrime
namespace Integration9_9.TM2NativePrime.candidateTest
end Integration9_9.TM2NativePrime.candidateTest
namespace Integration9_9.TM2NativePrime.doubleSlots
end Integration9_9.TM2NativePrime.doubleSlots
namespace Integration9_9.TM2NativePrime.powerSlots
end Integration9_9.TM2NativePrime.powerSlots
namespace Integration9_9.TM2NativePrime.powerSlots.match_1
end Integration9_9.TM2NativePrime.powerSlots.match_1
namespace Integration9_9.TM2NativePrime.primeTrial
end Integration9_9.TM2NativePrime.primeTrial
namespace Integration9_9.TM2NativePrime.thresholdSlots
end Integration9_9.TM2NativePrime.thresholdSlots
namespace Integration9_9.TM2NativePrime.upperSlots
end Integration9_9.TM2NativePrime.upperSlots
namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget
section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase QAlgorithms.Complexity Function Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime LARPlatformEncoding LARRankOneMachine TM2PlatformSerialization
theorem _root_.P2Mf6bd8d28.h741 (budget : Polynomial ℕ) :
    StrictMono (fun n => budget.eval n+n) := by
  intro a b hab
  have hm := polynomial_eval_mono budget hab.le
  change budget.eval a+a<budget.eval b+b
  omega
open _root_.P2Mf6bd8d28 renaming h741 → _Pkl
theorem _root_.P2Mf6bd8d28.h738 (budget : Polynomial ℕ) (coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    _root_.Integration9_9.LARCoinLayout.coinBaseLength budget (coins++input)=input.length := by
  let candidates := (List.range ((coins++input).length+1)).filter
    (fun index => decide (budget.eval index+index=(coins++input).length))
  have hn : input.length∈candidates := by
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      simp only [List.length_append,hc]
      omega
    · simp only [List.length_append,hc,decide_true]
  have hall : ∀ index∈candidates,index=input.length := by
    intro index hi
    have he := (List.mem_filter.mp hi).2
    have heq : budget.eval index+index=budget.eval input.length+input.length := by
      simpa only [decide_eq_true_eq,List.length_append,hc] using he
    exact (_Pkl budget).injective heq
  cases h : candidates with
  | nil => simp [h] at hn
  | cons first rest =>
    have hf : first=input.length := hall first (by simp [h])
    change (candidates.head?).getD 0=input.length
    simp [h,hf]
open _root_.P2Mf6bd8d28 renaming h738 → _Pki
theorem _root_.P2Mf6bd8d28.h739 (budget : Polynomial ℕ) (coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    _root_.Integration9_9.LARCoinLayout.coinFirstPair budget (coins++input)=encPair coins input := by
  unfold _root_.Integration9_9.LARCoinLayout.coinFirstPair
  rw [_Pki budget coins input hc,←hc]
  dsimp only
  rw [List.take_left,List.drop_left]
open _root_.P2Mf6bd8d28 renaming h739 → _Pkj
theorem _root_.P2Mf6bd8d28.h740 (budget : Polynomial ℕ) (fallback coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    _root_.Integration9_9.LARCoinLayout.coinFirstPre budget fallback (coins++input)=_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair coins input) := by
  unfold _root_.Integration9_9.LARCoinLayout.coinFirstPre
  rw [_Pkj budget coins input hc]
open _root_.P2Mf6bd8d28 renaming h740 → _Pkk
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h738 → _Pki
open _root_.P2Mf6bd8d28 renaming h739 → _Pkj
open _root_.P2Mf6bd8d28 renaming h740 → _Pkk
open _root_.P2Mf6bd8d28 renaming h741 → _Pkl
end
open _root_.P2Mf6bd8d28 renaming h738 → _Pki
open _root_.P2Mf6bd8d28 renaming h739 → _Pkj
open _root_.P2Mf6bd8d28 renaming h740 → _Pkk
open _root_.P2Mf6bd8d28 renaming h741 → _Pkl
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime LARRankOneMachine TM2PlatformSerialization
theorem _root_.P2Mf6bd8d28.h744 (slots : List Unit) (query : Str) (index : ℕ) (hi : index ≤ slots.length) :
    (_root_.Integration9_9.LARCoinLayout.encodeQueryOutput slots query)[index]?=some (decide (query.length=index)) := by
  unfold _root_.Integration9_9.LARCoinLayout.encodeQueryOutput
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_map,List.getElem?_range (show index<slots.length+1 by omega)]
  rfl
open _root_.P2Mf6bd8d28 renaming h744 → _Pko
theorem _root_.P2Mf6bd8d28.h743 (slots : List Unit) (query : Str) (index : ℕ) (hi : index<slots.length) :
    (_root_.Integration9_9.LARCoinLayout.encodeQueryOutput slots query)[slots.length+1+index]?=some ((query[index]?).getD false) := by
  unfold _root_.Integration9_9.LARCoinLayout.encodeQueryOutput
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map,List.length_range,Nat.add_sub_cancel_left]
  rw [List.getElem?_take_of_lt hi]
  by_cases hq : index<query.length
  · rw [List.getElem?_append_left hq,List.getElem?_eq_getElem hq]
    rfl
  · have hnone : query[index]?=none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_append_right (by omega),hnone]
    simp only [Option.getD_none]
    rw [List.getElem?_map,List.getElem?_eq_getElem (show index-query.length<slots.length by omega)]
    rfl
open _root_.P2Mf6bd8d28 renaming h743 → _Pkn
attribute [local irreducible] coinFirstPre queryOutputSlots
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h743 → _Pkn
open _root_.P2Mf6bd8d28 renaming h744 → _Pko
end
open _root_.P2Mf6bd8d28 renaming h743 → _Pkn
open _root_.P2Mf6bd8d28 renaming h744 → _Pko
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
private theorem _root_.P2Mf6bd8d28.h915 {N : ℕ} (f g : QState N → QState N)
    (a b : Bits N → ℂ)
    (hf : ∀ φ x, f φ x = a x * φ x) (hg : ∀ φ x, g φ x = b x * φ x)
    (φ : QState N) (x : Bits N) : g (f φ) x = b x * a x * φ x := by
  rw [hg, hf, mul_assoc]
open _root_.P2Mf6bd8d28 renaming h915 → _Ppf
private theorem _root_.P2Mf6bd8d28.h913 {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N)
    (F : QState N → QState N) (a : Bits N → ℂ)
    (hF : ∀ φ x, F φ x = a x * φ x) :
    cnotState i j hij (F (cnotState i j hij ψ)) =
      fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  simp only [cnotState, hF, Function.update_self, Function.update_of_ne hij, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Function.update_idem, Function.update_eq_self]
open _root_.P2Mf6bd8d28 renaming h913 → _Ppd
private theorem _root_.P2Mf6bd8d28.h912 {N : ℕ} (i : Fin N) (ψ : QState N) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  simp [apply1, tMat]
open _root_.P2Mf6bd8d28 renaming h912 → _Ppc
private theorem _root_.P2Mf6bd8d28.h914 :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
open _root_.P2Mf6bd8d28 renaming h914 → _Ppe
private abbrev _root_.P2Mf6bd8d28.h916 {N : ℕ} (F : QState N → QState N) (a : Bits N → ℂ) : Prop :=
  ∀ (φ : QState N) (x : Bits N), F φ x = a x * φ x
open _root_.P2Mf6bd8d28 renaming h916 → _Ppg
private lemma _root_.P2Mf6bd8d28.h921 {N : ℕ} {f g : QState N → QState N} {a b : Bits N → ℂ}
    (hf : _Ppg f a) (hg : _Ppg g b) :
    _Ppg (fun ψ => g (f ψ)) (fun x => b x * a x) := by
  intro ψ x
  exact _Ppf f g a b hf hg ψ x
open _root_.P2Mf6bd8d28 renaming h921 → _Ppl
private lemma _root_.P2Mf6bd8d28.h922 {N : ℕ} {F : QState N → QState N} {a : Bits N → ℂ}
    (i j : Fin N) (hij : i ≠ j) (hF : _Ppg F a) :
    _Ppg (fun ψ => cnotState i j hij (F (cnotState i j hij ψ)))
      (fun x => a (Function.update x j (xor (x j) (x i)))) := by
  intro ψ x
  exact congrFun (_Ppd i j hij ψ F a hF) x
open _root_.P2Mf6bd8d28 renaming h922 → _Ppm
private lemma _root_.P2Mf6bd8d28.h923 {N : ℕ} (i : Fin N) :
    _Ppg (apply1 tMat i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  simp only [_Ppc]
open _root_.P2Mf6bd8d28 renaming h923 → _Ppn
private noncomputable def _root_.P2Mf6bd8d28.h924 {N : ℕ} (i : Fin N) (ψ : QState N) : QState N :=
  apply1 tMat i (apply1 tMat i (apply1 tMat i (apply1 tMat i
    (apply1 tMat i (apply1 tMat i (apply1 tMat i ψ))))))
open _root_.P2Mf6bd8d28 renaming h924 → _Ppo
private lemma _root_.P2Mf6bd8d28.h917 {N : ℕ} (i : Fin N) :
    _Ppg (_Ppo i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  simp only [_Ppo, _Ppc]
  cases hx : x i with
  | false => simp [hx]
  | true =>
      simp only [hx, if_true]
      ring
open _root_.P2Mf6bd8d28 renaming h917 → _Pph
private noncomputable def _root_.P2Mf6bd8d28.h925 {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N) :
    QState N :=
  cnotState i j hij (_Ppo j (cnotState i j hij ψ))
open _root_.P2Mf6bd8d28 renaming h925 → _Ppp
private lemma _root_.P2Mf6bd8d28.h918 {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    _Ppg (_Ppp i j hij)
      (fun x => if xor (x j) (x i) then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  have h := _Ppm i j hij (_Pph j) φ x
  simp only [Function.update_self] at h
  exact h
open _root_.P2Mf6bd8d28 renaming h918 → _Ppi
private noncomputable def _root_.P2Mf6bd8d28.h926 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) : QState N :=
  cnotState p r hpr (cnotState q r hqr (apply1 tMat r
    (cnotState q r hqr (cnotState p r hpr ψ))))
open _root_.P2Mf6bd8d28 renaming h926 → _Ppq
private lemma _root_.P2Mf6bd8d28.h919 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r) :
    _Ppg (_Ppq p q r hpr hqr)
      (fun x => if xor (xor (x r) (x p)) (x q) then
        Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  have h := _Ppm p r hpr (_Ppm q r hqr (_Ppn r)) φ x
  simp only [Function.update_self, Function.update_of_ne hqr] at h
  exact h
open _root_.P2Mf6bd8d28 renaming h919 → _Ppj
private lemma _root_.P2Mf6bd8d28.h931 (a b c : Bool) :
    (if xor (xor c a) b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
      ((if xor c a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
        ((if xor c b then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
          ((if xor b a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
            ((if c then Complex.exp (Complex.I * Real.pi / 4) else 1) *
              ((if b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
                (if a then Complex.exp (Complex.I * Real.pi / 4) else 1))))))
      = if a && b && c then (-1 : ℂ) else 1 := by
  let w : ℂ := Complex.exp (Complex.I * Real.pi / 4)
  have h4 : w ^ 4 = -1 := by
    rw [show w ^ 4 = Complex.exp (4 * (Complex.I * Real.pi / 4)) from
      (Complex.exp_nat_mul _ 4).symm]
    convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring
  have h16 : w ^ 16 = 1 := by
    rw [show 16 = 4 * 4 from rfl, pow_mul, h4]
    norm_num
  change (if xor (xor c a) b then w else 1) *
      ((if xor c a then w ^ 7 else 1) *
        ((if xor c b then w ^ 7 else 1) *
          ((if xor b a then w ^ 7 else 1) *
            ((if c then w else 1) * ((if b then w else 1) * (if a then w else 1)))))) = _
  cases a <;> cases b <;> cases c <;> norm_num <;> ring_nf <;> first | exact h16 | exact h4
open _root_.P2Mf6bd8d28 renaming h931 → _Ppv
private noncomputable def _root_.P2Mf6bd8d28.h927 {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) : QState N :=
  _Ppq p q r hpr hqr (_Ppp p r hpr (_Ppp q r hqr (_Ppp p q hpq
    (apply1 tMat r (apply1 tMat q (apply1 tMat p ψ))))))
open _root_.P2Mf6bd8d28 renaming h927 → _Ppr
private lemma _root_.P2Mf6bd8d28.h920 {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    _Ppg (_Ppr p q r hpq hpr hqr)
      (fun x => if x p && x q && x r then (-1 : ℂ) else 1) := by
  have c7 := _Ppl (_Ppl (_Ppl (_Ppl
      (_Ppl (_Ppl (_Ppn p) (_Ppn q)) (_Ppn r))
      (_Ppi p q hpq)) (_Ppi q r hqr)) (_Ppi p r hpr))
      (_Ppj p q r hpr hqr)
  intro φ x
  first
    | exact (c7 φ x).trans
        (congrArg (fun z : ℂ => z * φ x) (_Ppv (x p) (x q) (x r)))
    | (refine (c7 φ x).trans ?_
       rw [← shiTof_phase_prod (x p) (x q) (x r)])
    | (refine (c7 φ x).trans ?_
       beta_reduce
       rw [shiTof_phase_prod (x p) (x q) (x r)])
open _root_.P2Mf6bd8d28 renaming h920 → _Ppk
private lemma _root_.P2Mf6bd8d28.h929 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (F : QState N → QState N)
    (hF : ∀ (φ : QState N) (y : Bits N),
      F φ y = (if y p && y q && y r then (-1 : ℂ) else 1) * φ y)
    (ψ : QState N) :
    apply1 hMat r (F (apply1 hMat r ψ))
      = fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
    _Ppe
  funext x
  have hup : ∀ b : Bool, F (apply1 hMat r ψ) (Function.update x r b)
      = (if x p && x q && b then (-1 : ℂ) else 1)
        * ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
    intro b
    have e1 : Function.update x r b p = x p := Function.update_of_ne hpr b x
    have e2 : Function.update x r b q = x q := Function.update_of_ne hqr b x
    have e3 : Function.update x r b r = b := Function.update_self r b x
    have e4 : apply1 hMat r ψ (Function.update x r b)
        = ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
      simp only [apply1, Function.update_self, Function.update_idem]
    simp only [hF, e1, e2, e3, e4]
  have main : apply1 hMat r (F (apply1 hMat r ψ)) x
      = ∑ b : Bool, hMat (x r) b * F (apply1 hMat r ψ) (Function.update x r b) := rfl
  rw [main]
  simp only [Fintype.sum_bool]
  first
    | rw [hup true, hup false]
    | simp only [hup]
  simp only [hMat, Matrix.of_apply, Fintype.sum_bool, Complex.ofReal_inv]
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hsdef
  cases hr : x r <;> cases hm : (x p && x q) <;> (try simp only [hr, hm]) <;> norm_num <;>
    first
      | linear_combination (2 * ψ (Function.update x r false)) * hs
      | linear_combination (2 * ψ (Function.update x r true)) * hs
      | linear_combination (-2 * ψ (Function.update x r false)) * hs
      | linear_combination (-2 * ψ (Function.update x r true)) * hs
open _root_.P2Mf6bd8d28 renaming h929 → _Ppt
private lemma _root_.P2Mf6bd8d28.h930 {N : ℕ} (gs : List (Instr N)) :
    ∀ l ∈ gs.map (fun g => [g]), LayerOk l := by
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨g, _, hg⟩ := hl
  subst hg
  exact List.pairwise_singleton _ g
open _root_.P2Mf6bd8d28 renaming h930 → _Ppu
private lemma _root_.P2Mf6bd8d28.h932 {N : ℕ} (gs : List (Instr N)) (ψ : QState N) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g => Instr.apply g st) ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      have hstep : runLayered ((g :: gs).map (fun z => [z])) ψ
          = runLayered (gs.map (fun z => [z])) (Instr.apply g ψ) := rfl
      rw [hstep, ih, List.foldl_cons]
open _root_.P2Mf6bd8d28 renaming h932 → _Ppw
private lemma _root_.P2Mf6bd8d28.h928 {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) :
    (_root_.InfoLossLAR.WorstCase.toffoliGates p q r hpq hpr hqr).foldl (fun st g => Instr.apply g st) ψ
      = apply1 hMat r (_Ppr p q r hpq hpr hqr (apply1 hMat r ψ)) := by
  first
    | rfl
    | simp only [toffoliGates, shiTof_cczOp, shiTof_cB, shiTof_cB7, shiTof_T7,
        List.foldl_cons, List.foldl_nil, Instr.apply]
open _root_.P2Mf6bd8d28 renaming h928 → _Pps
theorem _root_.P2Mf6bd8d28.h579 {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) :
    runLayered (_root_.InfoLossLAR.WorstCase.toffoliCircuit p q r hpq hpr hqr) ψ =
      fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  rw [_root_.InfoLossLAR.WorstCase.toffoliCircuit, _Ppw, _Pps]
  exact _Ppt p q r hpr hqr _ (fun φ y => _Ppk p q r hpq hpr hqr φ y) ψ
open _root_.P2Mf6bd8d28 renaming h579 → _Pg3
theorem _root_.P2Mf6bd8d28.h580 {N : ℕ} (p q r : Fin N)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ layer ∈ _root_.InfoLossLAR.WorstCase.toffoliCircuit p q r hpq hpr hqr, LayerOk layer := _Ppu _
open _root_.P2Mf6bd8d28 renaming h580 → _Pg4
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h579 → _Pg3
open _root_.P2Mf6bd8d28 renaming h580 → _Pg4
open _root_.P2Mf6bd8d28 renaming h912 → _Ppc
open _root_.P2Mf6bd8d28 renaming h913 → _Ppd
open _root_.P2Mf6bd8d28 renaming h914 → _Ppe
open _root_.P2Mf6bd8d28 renaming h915 → _Ppf
open _root_.P2Mf6bd8d28 renaming h916 → _Ppg
open _root_.P2Mf6bd8d28 renaming h917 → _Pph
open _root_.P2Mf6bd8d28 renaming h918 → _Ppi
open _root_.P2Mf6bd8d28 renaming h919 → _Ppj
open _root_.P2Mf6bd8d28 renaming h920 → _Ppk
open _root_.P2Mf6bd8d28 renaming h921 → _Ppl
open _root_.P2Mf6bd8d28 renaming h922 → _Ppm
open _root_.P2Mf6bd8d28 renaming h923 → _Ppn
open _root_.P2Mf6bd8d28 renaming h924 → _Ppo
open _root_.P2Mf6bd8d28 renaming h925 → _Ppp
open _root_.P2Mf6bd8d28 renaming h926 → _Ppq
open _root_.P2Mf6bd8d28 renaming h927 → _Ppr
open _root_.P2Mf6bd8d28 renaming h928 → _Pps
open _root_.P2Mf6bd8d28 renaming h929 → _Ppt
open _root_.P2Mf6bd8d28 renaming h930 → _Ppu
open _root_.P2Mf6bd8d28 renaming h931 → _Ppv
open _root_.P2Mf6bd8d28 renaming h932 → _Ppw
end
open _root_.P2Mf6bd8d28 renaming h579 → _Pg3
open _root_.P2Mf6bd8d28 renaming h580 → _Pg4
namespace Integration9_9.TM2Composition
end Integration9_9.TM2Composition
namespace Integration9_9.TM2Composition.Alphabet
end Integration9_9.TM2Composition.Alphabet
namespace Integration9_9.TM2Composition.Alphabet.match_1
end Integration9_9.TM2Composition.Alphabet.match_1
namespace Integration9_9.TM2Composition.canonical
end Integration9_9.TM2Composition.canonical
namespace Integration9_9.TM2Composition.leftStack
end Integration9_9.TM2Composition.leftStack
namespace Integration9_9.TM2Composition.leftSymbol
end Integration9_9.TM2Composition.leftSymbol
namespace Integration9_9.TM2Composition.machine
end Integration9_9.TM2Composition.machine
namespace Integration9_9.TM2Composition.middle
end Integration9_9.TM2Composition.middle
namespace Integration9_9.TM2Composition.program
end Integration9_9.TM2Composition.program
namespace Integration9_9.TM2Composition.rightStack
end Integration9_9.TM2Composition.rightStack
namespace Integration9_9.TM2Composition.rightSymbol
end Integration9_9.TM2Composition.rightSymbol
namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength
namespace Integration9_9.TM2OutputLength.pushBound
end Integration9_9.TM2OutputLength.pushBound
namespace Integration9_9.TM2OutputLength.pushBound.match_1
end Integration9_9.TM2OutputLength.pushBound.match_1
namespace Integration9_9.TM2Simulation
end Integration9_9.TM2Simulation
namespace Integration9_9.TM2Simulation.ControlLens
end Integration9_9.TM2Simulation.ControlLens
namespace Integration9_9.TM2Simulation.ControlLens.mk
end Integration9_9.TM2Simulation.ControlLens.mk
namespace Integration9_9.TM2Simulation.singleStack
end Integration9_9.TM2Simulation.singleStack
namespace Integration9_9.TM2Simulation.statement
end Integration9_9.TM2Simulation.statement
namespace Integration9_9.TM2Simulation.statement.match_1
end Integration9_9.TM2Simulation.statement.match_1
namespace Integration9_9.TM2Simulation.statement.match_3
end Integration9_9.TM2Simulation.statement.match_3
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h520 : Poly _root_.InfoLossLAR.WorstCase.readCircuitInstruction := by
  unfold _root_.InfoLossLAR.WorstCase.readCircuitInstruction
  fun_prop
open _root_.P2Mf6bd8d28 renaming h520 → _Peg
theorem _root_.P2Mf6bd8d28.h521 (xs : Str) :
    (_root_.InfoLossLAR.WorstCase.readCircuitInstruction xs).1.length ≤ xs.length := by
  unfold _root_.InfoLossLAR.WorstCase.readCircuitInstruction
  split_ifs
  · exact (_Pn1 _).trans ((_Pn1 _).trans (_Pn1 _))
  · exact (_Pn1 _).trans (_Pn1 _)
open _root_.P2Mf6bd8d28 renaming h521 → _Peh
@[fun_prop] theorem _root_.P2Mf6bd8d28.h522 : Poly _root_.InfoLossLAR.WorstCase.readCircuitLayer :=
  _Pmy _root_.InfoLossLAR.WorstCase.readCircuitInstruction _Peg _Peh
open _root_.P2Mf6bd8d28 renaming h522 → _Pei
theorem _root_.P2Mf6bd8d28.h523 (xs : Str) :
    (_root_.InfoLossLAR.WorstCase.readCircuitLayer xs).1.length ≤ xs.length :=
  _Pmz _root_.InfoLossLAR.WorstCase.readCircuitInstruction _Peg _Peh xs
open _root_.P2Mf6bd8d28 renaming h523 → _Pej
@[fun_prop] theorem _root_.P2Mf6bd8d28.h524 : Poly _root_.InfoLossLAR.WorstCase.readCircuitLayers :=
  _Pmy _root_.InfoLossLAR.WorstCase.readCircuitLayer _Pei _Pej
open _root_.P2Mf6bd8d28 renaming h524 → _Pek
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h520 → _Peg
open _root_.P2Mf6bd8d28 renaming h521 → _Peh
open _root_.P2Mf6bd8d28 renaming h522 → _Pei
open _root_.P2Mf6bd8d28 renaming h523 → _Pej
open _root_.P2Mf6bd8d28 renaming h524 → _Pek
end
open _root_.P2Mf6bd8d28 renaming h520 → _Peg
open _root_.P2Mf6bd8d28 renaming h521 → _Peh
open _root_.P2Mf6bd8d28 renaming h522 → _Pei
open _root_.P2Mf6bd8d28 renaming h523 → _Pej
open _root_.P2Mf6bd8d28 renaming h524 → _Pek
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization
namespace ReversibleGate
theorem _root_.P2Mf6bd8d28.h185 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) (ψ : QState n) :
    runLayered g.compile ψ = fun x => ψ (g.act x) := by
  cases g with
  | flip i =>
    funext x
    simp only [_root_.InfoLossLAR.WorstCase.ReversibleGate.compile, runLayered, runLayer, List.foldl_cons, List.foldl_nil, Instr.apply, apply1]
    cases hx : x i <;> simp [xMat, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, hx]
  | controlled i j hij => rfl
  | toffoli i j k hij hik hjk => exact _Pg3 i j k hij hik hjk ψ
open _root_.P2Mf6bd8d28 renaming h185 → InfoLossLAR.WorstCase.ReversibleGate.compile_apply
open _root_.P2Mf6bd8d28 renaming h185 → _P55
theorem _root_.P2Mf6bd8d28.h187 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) :
    ∀ layer ∈ g.compile, LayerOk layer := by
  cases g with
  | flip i => simp [_root_.InfoLossLAR.WorstCase.ReversibleGate.compile, LayerOk]
  | controlled i j hij => simp [_root_.InfoLossLAR.WorstCase.ReversibleGate.compile, LayerOk]
  | toffoli i j k hij hik hjk => exact _Pg4 i j k hij hik hjk
open _root_.P2Mf6bd8d28 renaming h187 → InfoLossLAR.WorstCase.ReversibleGate.compile_wellFormed
open _root_.P2Mf6bd8d28 renaming h187 → _P57
theorem _root_.P2Mf6bd8d28.h186 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) : depth g.compile ≤ 37 := by
  cases g <;> simp [_root_.InfoLossLAR.WorstCase.ReversibleGate.compile, depth, _root_.InfoLossLAR.WorstCase.toffoliCircuit, _root_.InfoLossLAR.WorstCase.toffoliGates]
open _root_.P2Mf6bd8d28 renaming h186 → InfoLossLAR.WorstCase.ReversibleGate.compile_depth
open _root_.P2Mf6bd8d28 renaming h186 → _P56
end ReversibleGate
open _root_.P2Mf6bd8d28 renaming h185 → InfoLossLAR.WorstCase.ReversibleGate.compile_apply
open _root_.P2Mf6bd8d28 renaming h185 → _P55
open _root_.P2Mf6bd8d28 renaming h186 → InfoLossLAR.WorstCase.ReversibleGate.compile_depth
open _root_.P2Mf6bd8d28 renaming h186 → _P56
open _root_.P2Mf6bd8d28 renaming h187 → InfoLossLAR.WorstCase.ReversibleGate.compile_wellFormed
open _root_.P2Mf6bd8d28 renaming h187 → _P57
private theorem _root_.P2Mf6bd8d28.h905 {n : ℕ} (c d : Layered n) (ψ : QState n) :
    runLayered (c ++ d) ψ = runLayered d (runLayered c ψ) := List.foldl_append
open _root_.P2Mf6bd8d28 renaming h905 → _Pp5
theorem _root_.P2Mf6bd8d28.h389 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) (ψ : QState n) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible gates) ψ = fun x => ψ ((_root_.InfoLossLAR.WorstCase.reversibleAction gates).symm x) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runLayered (g.compile ++ _root_.InfoLossLAR.WorstCase.compileReversible gs) ψ = _
    rw [_Pp5, ih, g.compile_apply]
    rfl
open _root_.P2Mf6bd8d28 renaming h389 → _Pat
theorem _root_.P2Mf6bd8d28.h392 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) :
    ∀ layer ∈ _root_.InfoLossLAR.WorstCase.compileReversible gates, LayerOk layer := by
  intro layer hl
  obtain ⟨g, _, hgl⟩ := List.mem_flatMap.1 hl
  exact g.compile_wellFormed layer hgl
open _root_.P2Mf6bd8d28 renaming h392 → _Paw
theorem _root_.P2Mf6bd8d28.h391 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) :
    depth (_root_.InfoLossLAR.WorstCase.compileReversible gates) ≤ 37 * gates.length := by
  induction gates with
  | nil => simp [_root_.InfoLossLAR.WorstCase.compileReversible, depth]
  | cons g gs ih =>
    have hg := g.compile_depth
    change (g.compile ++ _root_.InfoLossLAR.WorstCase.compileReversible gs).length ≤ _
    simp only [List.length_append, List.length_cons]
    change g.compile.length ≤ 37 at hg
    change (_root_.InfoLossLAR.WorstCase.compileReversible gs).length ≤ _ at ih
    omega
open _root_.P2Mf6bd8d28 renaming h391 → _Pav
theorem _root_.P2Mf6bd8d28.h390 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) (x : Bits n) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = _root_.InfoLossLAR.WorstCase.reversibleAction gates x then 1 else 0 := by
  rw [_Pat]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)
open _root_.P2Mf6bd8d28 renaming h390 → _Pau
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h185 → InfoLossLAR.WorstCase.ReversibleGate.compile_apply
open _root_.P2Mf6bd8d28 renaming h185 → _P55
open _root_.P2Mf6bd8d28 renaming h186 → InfoLossLAR.WorstCase.ReversibleGate.compile_depth
open _root_.P2Mf6bd8d28 renaming h186 → _P56
open _root_.P2Mf6bd8d28 renaming h187 → InfoLossLAR.WorstCase.ReversibleGate.compile_wellFormed
open _root_.P2Mf6bd8d28 renaming h187 → _P57
open _root_.P2Mf6bd8d28 renaming h389 → _Pat
open _root_.P2Mf6bd8d28 renaming h390 → _Pau
open _root_.P2Mf6bd8d28 renaming h391 → _Pav
open _root_.P2Mf6bd8d28 renaming h392 → _Paw
open _root_.P2Mf6bd8d28 renaming h905 → _Pp5
end
open _root_.P2Mf6bd8d28 renaming h185 → InfoLossLAR.WorstCase.ReversibleGate.compile_apply
open _root_.P2Mf6bd8d28 renaming h185 → _P55
open _root_.P2Mf6bd8d28 renaming h186 → InfoLossLAR.WorstCase.ReversibleGate.compile_depth
open _root_.P2Mf6bd8d28 renaming h186 → _P56
open _root_.P2Mf6bd8d28 renaming h187 → InfoLossLAR.WorstCase.ReversibleGate.compile_wellFormed
open _root_.P2Mf6bd8d28 renaming h187 → _P57
open _root_.P2Mf6bd8d28 renaming h389 → _Pat
open _root_.P2Mf6bd8d28 renaming h390 → _Pau
open _root_.P2Mf6bd8d28 renaming h391 → _Pav
open _root_.P2Mf6bd8d28 renaming h392 → _Paw
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h581 :
    Poly (fun x : Str × Str × Str => _root_.InfoLossLAR.WorstCase.toffoliInstructionWords x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.toffoliInstructionWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h581 → _Pg5
@[fun_prop] theorem _root_.P2Mf6bd8d28.h536 : Poly _root_.InfoLossLAR.WorstCase.readReversibleInstruction := by
  unfold _root_.InfoLossLAR.WorstCase.readReversibleInstruction
  fun_prop
open _root_.P2Mf6bd8d28 renaming h536 → _Pew
theorem _root_.P2Mf6bd8d28.h537 (xs : Str) :
    (_root_.InfoLossLAR.WorstCase.readReversibleInstruction xs).1.length ≤ xs.length := by
  unfold _root_.InfoLossLAR.WorstCase.readReversibleInstruction
  split_ifs
  · exact (_Pn1 _).trans (_Pn1 _)
  · exact (_Pn1 _).trans ((_Pn1 _).trans (_Pn1 _))
  · exact (_Pn1 _).trans ((_Pn1 _).trans
      ((_Pn1 _).trans (_Pn1 _)))
open _root_.P2Mf6bd8d28 renaming h537 → _Pex
private theorem _root_.P2Mf6bd8d28.h907 (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs
open _root_.P2Mf6bd8d28 renaming h907 → _Pp7
theorem _root_.P2Mf6bd8d28.h535 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) (xs : Str) :
    _root_.InfoLossLAR.WorstCase.readReversibleInstruction (g.code ++ xs) = (xs, g.compile.flatten.map encInstr) := by
  cases g <;> simp only [_root_.InfoLossLAR.WorstCase.ReversibleGate.code, List.append_assoc, _root_.InfoLossLAR.WorstCase.readReversibleInstruction,
    _Pp7, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append] <;> norm_num <;> rfl
open _root_.P2Mf6bd8d28 renaming h535 → _Pev
@[fun_prop] theorem _root_.P2Mf6bd8d28.h539 : Poly _root_.InfoLossLAR.WorstCase.readReversibleProgram :=
  _Pmy _root_.InfoLossLAR.WorstCase.readReversibleInstruction _Pew _Pex
open _root_.P2Mf6bd8d28 renaming h539 → _Pez
theorem _root_.P2Mf6bd8d28.h538 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) (xs : Str) :
    _root_.InfoLossLAR.WorstCase.readReversibleProgram (encStr (gates.map _root_.InfoLossLAR.WorstCase.ReversibleGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.flatten.map encInstr)) :=
  _root_.Integration9_9.TM2PlatformSerialization.readList_append_mapped _root_.InfoLossLAR.WorstCase.readReversibleInstruction _root_.InfoLossLAR.WorstCase.ReversibleGate.code
    (fun g => g.compile.flatten.map encInstr) _Pev gates xs
open _root_.P2Mf6bd8d28 renaming h538 → _Pey
private theorem _root_.P2Mf6bd8d28.h906 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) :
    ((gates.map (fun g => g.compile.flatten.map encInstr)).flatten).map (fun word => [word]) =
      (_root_.InfoLossLAR.WorstCase.compileReversible gates).map (List.map encInstr) := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, _root_.InfoLossLAR.WorstCase.compileReversible,
      List.flatMap_cons] at ih ⊢
    rw [ih]
    congr 1
    cases g <;> rfl
open _root_.P2Mf6bd8d28 renaming h906 → _Pp6
@[fun_prop] theorem _root_.P2Mf6bd8d28.h388 : Poly _root_.InfoLossLAR.WorstCase.compileReversibleDescription := by
  unfold _root_.InfoLossLAR.WorstCase.compileReversibleDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop
open _root_.P2Mf6bd8d28 renaming h388 → _Pas
theorem _root_.P2Mf6bd8d28.h387 (F : _root_.InfoLossLAR.WorstCase.ReversibleFamily) (n : ℕ) :
    _root_.InfoLossLAR.WorstCase.compileReversibleDescription (F.code n) = encFamilyAt F.compile n := by
  unfold _root_.InfoLossLAR.WorstCase.ReversibleFamily.code _root_.InfoLossLAR.WorstCase.compileReversibleDescription
  simp only [List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append]
  have h := _Pey (F.gates n) []
  simp only [List.append_nil] at h
  rw [h]
  have hh := congrArg (fun xs : List (List Str) => _root_.Integration9_9.TM2PlatformSerialization.serializeWords (xs.map _root_.Integration9_9.TM2PlatformSerialization.serializeWords))
    (_Pp6 (F.gates n))
  simp only [List.map_map, Function.comp_def] at hh
  rw [hh]
  simp only [_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq, encFamilyAt, _root_.InfoLossLAR.WorstCase.ReversibleFamily.compile, encCirc, List.append_assoc]
  rfl
open _root_.P2Mf6bd8d28 renaming h387 → _Par
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h387 → _Par
open _root_.P2Mf6bd8d28 renaming h388 → _Pas
open _root_.P2Mf6bd8d28 renaming h535 → _Pev
open _root_.P2Mf6bd8d28 renaming h536 → _Pew
open _root_.P2Mf6bd8d28 renaming h537 → _Pex
open _root_.P2Mf6bd8d28 renaming h538 → _Pey
open _root_.P2Mf6bd8d28 renaming h539 → _Pez
open _root_.P2Mf6bd8d28 renaming h581 → _Pg5
open _root_.P2Mf6bd8d28 renaming h906 → _Pp6
open _root_.P2Mf6bd8d28 renaming h907 → _Pp7
end
open _root_.P2Mf6bd8d28 renaming h387 → _Par
open _root_.P2Mf6bd8d28 renaming h388 → _Pas
open _root_.P2Mf6bd8d28 renaming h535 → _Pev
open _root_.P2Mf6bd8d28 renaming h536 → _Pew
open _root_.P2Mf6bd8d28 renaming h537 → _Pex
open _root_.P2Mf6bd8d28 renaming h538 → _Pey
open _root_.P2Mf6bd8d28 renaming h539 → _Pez
open _root_.P2Mf6bd8d28 renaming h581 → _Pg5
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
namespace BooleanGate
theorem _root_.P2Mf6bd8d28.h135 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.BooleanGate n) (x : Bits n) (i : Fin n)
    (hi : i ≠ g.target) : g.assign x i = x i := Function.update_of_ne hi _ _
open _root_.P2Mf6bd8d28 renaming h135 → InfoLossLAR.WorstCase.BooleanGate.assign_other
open _root_.P2Mf6bd8d28 renaming h135 → _P3r
theorem _root_.P2Mf6bd8d28.h137 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.BooleanGate n) : g.compile.length ≤ 2 := by
  cases g <;> simp only [_root_.InfoLossLAR.WorstCase.BooleanGate.compile] <;> (try split_ifs) <;> simp
open _root_.P2Mf6bd8d28 renaming h137 → InfoLossLAR.WorstCase.BooleanGate.compile_length
open _root_.P2Mf6bd8d28 renaming h137 → _P3t
theorem _root_.P2Mf6bd8d28.h136 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.BooleanGate n) (x : Bits n)
    (hz : x g.target = false) : _root_.InfoLossLAR.WorstCase.reversibleAction g.compile x = g.assign x := by
  cases g with
  | constant t b =>
    cases b <;> simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value]
  | copy s t h =>
    simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value]
  | negate s t h =>
    funext i
    by_cases hi : i = t
    · subst i
      cases hv : x s <;>
        simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value,
          Function.update_of_ne h]
    · simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value,
        Function.update_of_ne hi]
  | xor a b t ha hb =>
    simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value,
      Function.update_of_ne hb]
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value]
    · simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.reversibleAction, _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv, _root_.InfoLossLAR.WorstCase.ReversibleGate.act, _root_.InfoLossLAR.WorstCase.BooleanGate.assign, _root_.InfoLossLAR.WorstCase.BooleanGate.target, _root_.InfoLossLAR.WorstCase.BooleanGate.value]
open _root_.P2Mf6bd8d28 renaming h136 → InfoLossLAR.WorstCase.BooleanGate.compile_action
open _root_.P2Mf6bd8d28 renaming h136 → _P3s
end BooleanGate
open _root_.P2Mf6bd8d28 renaming h135 → InfoLossLAR.WorstCase.BooleanGate.assign_other
open _root_.P2Mf6bd8d28 renaming h135 → _P3r
open _root_.P2Mf6bd8d28 renaming h136 → InfoLossLAR.WorstCase.BooleanGate.compile_action
open _root_.P2Mf6bd8d28 renaming h136 → _P3s
open _root_.P2Mf6bd8d28 renaming h137 → InfoLossLAR.WorstCase.BooleanGate.compile_length
open _root_.P2Mf6bd8d28 renaming h137 → _P3t
theorem _root_.P2Mf6bd8d28.h549 {n : ℕ} (a b : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) :
    _root_.InfoLossLAR.WorstCase.reversibleAction (a ++ b) = (_root_.InfoLossLAR.WorstCase.reversibleAction a).trans (_root_.InfoLossLAR.WorstCase.reversibleAction b) := by
  induction a with
  | nil => rfl
  | cons g a ih =>
    simp only [List.cons_append, _root_.InfoLossLAR.WorstCase.reversibleAction, ih]
    rfl
open _root_.P2Mf6bd8d28 renaming h549 → _Pf9
theorem _root_.P2Mf6bd8d28.h348 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n))
    (hf : _root_.InfoLossLAR.WorstCase.BooleanFresh gates) (x : Bits n)
    (hz : ∀ g ∈ gates, x g.target = false) :
    _root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates) x = _root_.InfoLossLAR.WorstCase.booleanRun gates x := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hf
    have hzero : ∀ h ∈ gates, g.assign x h.target = false := by
      intro h hh
      rw [g.assign_other x h.target (Ne.symm (hhead h hh))]
      exact hz h (by simp [hh])
    change _root_.InfoLossLAR.WorstCase.reversibleAction (g.compile ++ _root_.InfoLossLAR.WorstCase.booleanToReversible gates) x = _
    rw [_Pf9]
    change _root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates) (_root_.InfoLossLAR.WorstCase.reversibleAction g.compile x) = _
    rw [g.compile_action x (hz g (by simp)), ih htail _ hzero]
    rfl
open _root_.P2Mf6bd8d28 renaming h348 → _P9o
theorem _root_.P2Mf6bd8d28.h350 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) :
    (_root_.InfoLossLAR.WorstCase.booleanToReversible gates).length ≤ 2 * gates.length := by
  induction gates with
  | nil => simp [_root_.InfoLossLAR.WorstCase.booleanToReversible]
  | cons g gates ih =>
    have hg := g.compile_length
    change (g.compile ++ _root_.InfoLossLAR.WorstCase.booleanToReversible gates).length ≤ _
    simp only [List.length_append, List.length_cons]
    omega
open _root_.P2Mf6bd8d28 renaming h350 → _P9q
theorem _root_.P2Mf6bd8d28.h346 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) :
    depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)) ≤ 74 * gates.length := by
  have h := (_Pav (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)).trans
    (Nat.mul_le_mul_left 37 (_P9q gates))
  omega
open _root_.P2Mf6bd8d28 renaming h346 → _P9m
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h135 → InfoLossLAR.WorstCase.BooleanGate.assign_other
open _root_.P2Mf6bd8d28 renaming h135 → _P3r
open _root_.P2Mf6bd8d28 renaming h136 → InfoLossLAR.WorstCase.BooleanGate.compile_action
open _root_.P2Mf6bd8d28 renaming h136 → _P3s
open _root_.P2Mf6bd8d28 renaming h137 → InfoLossLAR.WorstCase.BooleanGate.compile_length
open _root_.P2Mf6bd8d28 renaming h137 → _P3t
open _root_.P2Mf6bd8d28 renaming h346 → _P9m
open _root_.P2Mf6bd8d28 renaming h348 → _P9o
open _root_.P2Mf6bd8d28 renaming h350 → _P9q
open _root_.P2Mf6bd8d28 renaming h549 → _Pf9
end
open _root_.P2Mf6bd8d28 renaming h135 → InfoLossLAR.WorstCase.BooleanGate.assign_other
open _root_.P2Mf6bd8d28 renaming h135 → _P3r
open _root_.P2Mf6bd8d28 renaming h136 → InfoLossLAR.WorstCase.BooleanGate.compile_action
open _root_.P2Mf6bd8d28 renaming h136 → _P3s
open _root_.P2Mf6bd8d28 renaming h137 → InfoLossLAR.WorstCase.BooleanGate.compile_length
open _root_.P2Mf6bd8d28 renaming h137 → _P3t
open _root_.P2Mf6bd8d28 renaming h346 → _P9m
open _root_.P2Mf6bd8d28 renaming h348 → _P9o
open _root_.P2Mf6bd8d28 renaming h350 → _P9q
open _root_.P2Mf6bd8d28 renaming h549 → _Pf9
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h516 : Poly _root_.InfoLossLAR.WorstCase.readBooleanInstruction := by
  unfold _root_.InfoLossLAR.WorstCase.readBooleanInstruction
  fun_prop
open _root_.P2Mf6bd8d28 renaming h516 → _Pec
theorem _root_.P2Mf6bd8d28.h517 (xs : Str) :
    (_root_.InfoLossLAR.WorstCase.readBooleanInstruction xs).1.length ≤ xs.length := by
  unfold _root_.InfoLossLAR.WorstCase.readBooleanInstruction
  dsimp only
  split_ifs <;>
    first
      | exact (_Pn1 _).trans (_Pn1 _)
      | exact (_Pn1 _).trans ((_Pn1 _).trans (_Pn1 _))
      | exact (_Pn1 _).trans ((_Pn1 _).trans
          ((_Pn1 _).trans (_Pn1 _)))
open _root_.P2Mf6bd8d28 renaming h517 → _Ped
private theorem _root_.P2Mf6bd8d28.h904 (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs
open _root_.P2Mf6bd8d28 renaming h904 → _Pp4
private theorem _root_.P2Mf6bd8d28.h903 (n : ℕ) : inputWidth (encNat n) = n := by
  simpa using _Pp4 n []
open _root_.P2Mf6bd8d28 renaming h903 → _Pp3
theorem _root_.P2Mf6bd8d28.h515 {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.BooleanGate n) (xs : Str) :
    _root_.InfoLossLAR.WorstCase.readBooleanInstruction (g.code ++ xs) = (xs, g.compile.map _root_.InfoLossLAR.WorstCase.ReversibleGate.code) := by
  cases g with
  | constant t b =>
    cases b <;> simp only [_root_.InfoLossLAR.WorstCase.BooleanGate.code, Bool.false_eq_true, ite_false, ite_true,
      _root_.InfoLossLAR.WorstCase.readBooleanInstruction, List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append, _Pp4] <;> norm_num <;> rfl
  | copy s t h =>
    simp only [_root_.InfoLossLAR.WorstCase.BooleanGate.code, _root_.InfoLossLAR.WorstCase.readBooleanInstruction, List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append,
      _Pp4] <;> norm_num <;> rfl
  | negate s t h =>
    simp only [_root_.InfoLossLAR.WorstCase.BooleanGate.code, _root_.InfoLossLAR.WorstCase.readBooleanInstruction, List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append,
      _Pp4] <;> norm_num <;> rfl
  | xor a b t ha hb =>
    simp only [_root_.InfoLossLAR.WorstCase.BooleanGate.code, _root_.InfoLossLAR.WorstCase.readBooleanInstruction, List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append,
      _Pp4] <;> norm_num <;> rfl
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp [_root_.InfoLossLAR.WorstCase.BooleanGate.code, _root_.InfoLossLAR.WorstCase.readBooleanInstruction, List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append,
        _Pp4, _Pp3, _root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.ReversibleGate.code]
    · have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp [_root_.InfoLossLAR.WorstCase.BooleanGate.code, _root_.InfoLossLAR.WorstCase.readBooleanInstruction, List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append,
        _Pp4, _Pp3, _root_.InfoLossLAR.WorstCase.BooleanGate.compile, _root_.InfoLossLAR.WorstCase.ReversibleGate.code, hab, habv]
open _root_.P2Mf6bd8d28 renaming h515 → _Peb
@[fun_prop] theorem _root_.P2Mf6bd8d28.h519 : Poly _root_.InfoLossLAR.WorstCase.readBooleanProgram :=
  _Pmy _root_.InfoLossLAR.WorstCase.readBooleanInstruction _Pec _Ped
open _root_.P2Mf6bd8d28 renaming h519 → _Pef
theorem _root_.P2Mf6bd8d28.h518 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) (xs : Str) :
    _root_.InfoLossLAR.WorstCase.readBooleanProgram (encStr (gates.map _root_.InfoLossLAR.WorstCase.BooleanGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.map _root_.InfoLossLAR.WorstCase.ReversibleGate.code)) :=
  _root_.Integration9_9.TM2PlatformSerialization.readList_append_mapped _root_.InfoLossLAR.WorstCase.readBooleanInstruction _root_.InfoLossLAR.WorstCase.BooleanGate.code
    (fun g => g.compile.map _root_.InfoLossLAR.WorstCase.ReversibleGate.code) _Peb gates xs
open _root_.P2Mf6bd8d28 renaming h518 → _Pee
@[fun_prop] theorem _root_.P2Mf6bd8d28.h386 : Poly _root_.InfoLossLAR.WorstCase.compileBooleanDescription := by
  unfold _root_.InfoLossLAR.WorstCase.compileBooleanDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop
open _root_.P2Mf6bd8d28 renaming h386 → _Paq
theorem _root_.P2Mf6bd8d28.h385 (F : _root_.InfoLossLAR.WorstCase.BooleanFamily) (n : ℕ) :
    _root_.InfoLossLAR.WorstCase.compileBooleanDescription (F.code n) = F.reversible.code n := by
  unfold _root_.InfoLossLAR.WorstCase.BooleanFamily.code _root_.InfoLossLAR.WorstCase.compileBooleanDescription
  simp only [List.append_assoc, _root_.Integration9_9.TM2PlatformSerialization.readUnary_append]
  have h := _Pee (F.gates n) []
  simp only [List.append_nil] at h
  rw [h, _root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq]
  have hh : (List.map (fun g => List.map _root_.InfoLossLAR.WorstCase.ReversibleGate.code g.compile) (F.gates n)).flatten =
      (_root_.InfoLossLAR.WorstCase.booleanToReversible (F.gates n)).map _root_.InfoLossLAR.WorstCase.ReversibleGate.code := by
    simp only [_root_.InfoLossLAR.WorstCase.booleanToReversible, List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def]
  rw [hh]
  simp only [_root_.InfoLossLAR.WorstCase.ReversibleFamily.code, _root_.InfoLossLAR.WorstCase.BooleanFamily.reversible, List.append_assoc]
open _root_.P2Mf6bd8d28 renaming h385 → _Pap
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h385 → _Pap
open _root_.P2Mf6bd8d28 renaming h386 → _Paq
open _root_.P2Mf6bd8d28 renaming h515 → _Peb
open _root_.P2Mf6bd8d28 renaming h516 → _Pec
open _root_.P2Mf6bd8d28 renaming h517 → _Ped
open _root_.P2Mf6bd8d28 renaming h518 → _Pee
open _root_.P2Mf6bd8d28 renaming h519 → _Pef
open _root_.P2Mf6bd8d28 renaming h903 → _Pp3
open _root_.P2Mf6bd8d28 renaming h904 → _Pp4
end
open _root_.P2Mf6bd8d28 renaming h385 → _Pap
open _root_.P2Mf6bd8d28 renaming h386 → _Paq
open _root_.P2Mf6bd8d28 renaming h515 → _Peb
open _root_.P2Mf6bd8d28 renaming h516 → _Pec
open _root_.P2Mf6bd8d28 renaming h517 → _Ped
open _root_.P2Mf6bd8d28 renaming h518 → _Pee
open _root_.P2Mf6bd8d28 renaming h519 → _Pef
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
namespace BooleanOp
theorem _root_.P2Mf6bd8d28.h140 {total : ℕ} (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (target : Fin total) :
    (op.toGate target).target = target := by
  cases op <;> simp only [_root_.InfoLossLAR.WorstCase.BooleanOp.toGate] <;> (try split_ifs) <;> rfl
open _root_.P2Mf6bd8d28 renaming h140 → _P3w
theorem _root_.P2Mf6bd8d28.h141 {total : ℕ} (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).value (fun i => s i.val) = op.eval s := by
  cases op <;> simp_all [_root_.InfoLossLAR.WorstCase.BooleanOp.Valid, _root_.InfoLossLAR.WorstCase.BooleanOp.sources, _root_.InfoLossLAR.WorstCase.BooleanOp.toGate, _root_.InfoLossLAR.WorstCase.BooleanGate.value, _root_.InfoLossLAR.WorstCase.BooleanOp.eval]
open _root_.P2Mf6bd8d28 renaming h141 → _P3x
theorem _root_.P2Mf6bd8d28.h139 {total : ℕ} (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).assign (fun i => s i.val) = fun i => op.assign target.val s i.val := by
  funext i
  rw [_root_.InfoLossLAR.WorstCase.BooleanGate.assign, _P3w, _P3x op target hv]
  by_cases hi : i = target
  · subst i; simp [_root_.InfoLossLAR.WorstCase.BooleanOp.assign]
  · have hval : i.val ≠ target.val := fun h => hi (Fin.ext h)
    simp [_root_.InfoLossLAR.WorstCase.BooleanOp.assign, Function.update_of_ne hi, Function.update_of_ne hval]
open _root_.P2Mf6bd8d28 renaming h139 → _P3v
end BooleanOp
open _root_.P2Mf6bd8d28 renaming h139 → _P3v
open _root_.P2Mf6bd8d28 renaming h140 → _P3w
open _root_.P2Mf6bd8d28 renaming h141 → _P3x
namespace BooleanProgram
theorem _root_.P2Mf6bd8d28.h153 {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) (g : _root_.InfoLossLAR.WorstCase.BooleanGate total) (hg : g ∈ _root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h) :
    start ≤ g.target.val ∧ g.target.val < start + ops.length := by
  induction ops generalizing start with
  | nil => simp [_root_.InfoLossLAR.WorstCase.BooleanProgram.gates] at hg
  | cons op rest ih =>
    simp only [_root_.InfoLossLAR.WorstCase.BooleanProgram.gates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [_P3w, List.length_cons]; omega
    · have hh := ih (start := start + 1) _ hg
      simp only [List.length_cons]; omega
open _root_.P2Mf6bd8d28 renaming h153 → _P49
theorem _root_.P2Mf6bd8d28.h144 {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) : _root_.InfoLossLAR.WorstCase.BooleanFresh (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h) := by
  induction ops generalizing start with
  | nil => exact List.Pairwise.nil
  | cons op rest ih =>
    apply List.pairwise_cons.2
    constructor
    · intro g hg heq
      have hh := (_P49 rest _ g hg).1
      rw [_P3w] at heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
    · exact ih _
open _root_.P2Mf6bd8d28 renaming h144 → _P40
theorem _root_.P2Mf6bd8d28.h151 (start : ℕ) (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp) (s : ℕ → Bool)
    (i : ℕ) (hi : i < start) : _root_.InfoLossLAR.WorstCase.BooleanProgram.run start ops s i = s i := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    rw [_root_.InfoLossLAR.WorstCase.BooleanProgram.run, ih (start + 1) (op.assign start s) (by omega)]
    exact Function.update_of_ne (by omega) _ _
open _root_.P2Mf6bd8d28 renaming h151 → _P47
theorem _root_.P2Mf6bd8d28.h150 (start : ℕ) (a b : List _root_.InfoLossLAR.WorstCase.BooleanOp) (s : ℕ → Bool) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (a ++ b) s = _root_.InfoLossLAR.WorstCase.BooleanProgram.run (start + a.length) b (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start a s) := by
  induction a generalizing start s with
  | nil => simp [_root_.InfoLossLAR.WorstCase.BooleanProgram.run]
  | cons op a ih =>
    simp only [List.cons_append, _root_.InfoLossLAR.WorstCase.BooleanProgram.run, ih, List.length_cons]
    rw [show start + 1 + a.length = start + (a.length + 1) by omega]
open _root_.P2Mf6bd8d28 renaming h150 → _P46
theorem _root_.P2Mf6bd8d28.h152 {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) (hv : _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start ops) (s : ℕ → Bool) :
    _root_.InfoLossLAR.WorstCase.booleanRun (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h) (fun i => s i.val) = fun i => _root_.InfoLossLAR.WorstCase.BooleanProgram.run start ops s i.val := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    change _root_.InfoLossLAR.WorstCase.booleanRun (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates (start + 1) rest _) ((op.toGate _).assign (fun i => s i.val)) = _
    rw [_P3v op _ hv.1, ih _ hv.2]
    rfl
open _root_.P2Mf6bd8d28 renaming h152 → _P48
theorem _root_.P2Mf6bd8d28.h148 {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) (hv : _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    _root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h)) (fun i => s i.val) =
      fun i => _root_.InfoLossLAR.WorstCase.BooleanProgram.run start ops s i.val := by
  rw [_P9o _ (_P40 ops h)]
  · exact _P48 ops h hv s
  · intro g hg
    obtain ⟨hl, hu⟩ := _P49 ops h g hg
    exact hz _ hl hu
open _root_.P2Mf6bd8d28 renaming h148 → _P44
theorem _root_.P2Mf6bd8d28.h142 {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) (hv : _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h)))
      (fun x => if x = (fun i => s i.val) then (1 : ℂ) else 0) =
        fun x => if x = (fun i => _root_.InfoLossLAR.WorstCase.BooleanProgram.run start ops s i.val) then 1 else 0 := by
  rw [_Pau, _P44 ops h hv s hz]
open _root_.P2Mf6bd8d28 renaming h142 → _P3y
theorem _root_.P2Mf6bd8d28.h143 {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) :
    depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h))) ≤ 74 * ops.length := by
  simpa only [_root_.InfoLossLAR.WorstCase.BooleanProgram.gates_length] using _P9m (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h)
open _root_.P2Mf6bd8d28 renaming h143 → _P3z
end BooleanProgram
open _root_.P2Mf6bd8d28 renaming h142 → _P3y
open _root_.P2Mf6bd8d28 renaming h143 → _P3z
open _root_.P2Mf6bd8d28 renaming h144 → _P40
open _root_.P2Mf6bd8d28 renaming h148 → _P44
open _root_.P2Mf6bd8d28 renaming h150 → _P46
open _root_.P2Mf6bd8d28 renaming h151 → _P47
open _root_.P2Mf6bd8d28 renaming h152 → _P48
open _root_.P2Mf6bd8d28 renaming h153 → _P49
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h139 → _P3v
open _root_.P2Mf6bd8d28 renaming h140 → _P3w
open _root_.P2Mf6bd8d28 renaming h141 → _P3x
open _root_.P2Mf6bd8d28 renaming h142 → _P3y
open _root_.P2Mf6bd8d28 renaming h143 → _P3z
open _root_.P2Mf6bd8d28 renaming h144 → _P40
open _root_.P2Mf6bd8d28 renaming h148 → _P44
open _root_.P2Mf6bd8d28 renaming h150 → _P46
open _root_.P2Mf6bd8d28 renaming h151 → _P47
open _root_.P2Mf6bd8d28 renaming h152 → _P48
open _root_.P2Mf6bd8d28 renaming h153 → _P49
end
open _root_.P2Mf6bd8d28 renaming h139 → _P3v
open _root_.P2Mf6bd8d28 renaming h140 → _P3w
open _root_.P2Mf6bd8d28 renaming h141 → _P3x
open _root_.P2Mf6bd8d28 renaming h142 → _P3y
open _root_.P2Mf6bd8d28 renaming h143 → _P3z
open _root_.P2Mf6bd8d28 renaming h144 → _P40
open _root_.P2Mf6bd8d28 renaming h148 → _P44
open _root_.P2Mf6bd8d28 renaming h150 → _P46
open _root_.P2Mf6bd8d28 renaming h151 → _P47
open _root_.P2Mf6bd8d28 renaming h152 → _P48
open _root_.P2Mf6bd8d28 renaming h153 → _P49
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
namespace BooleanExpr
theorem _root_.P2Mf6bd8d28.h129 {bound : ℕ} (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (hv : e.Valid bound)
    {s t : ℕ → Bool} (h : ∀ i, i < bound → s i = t i) : e.eval s = e.eval t := by
  induction e with
  | input i => exact h i hv
  | constant b => rfl
  | negate a ih => exact congrArg Bool.not (ih hv)
  | xor a b ia ib => exact congrArg₂ Bool.xor (ia hv.1) (ib hv.2)
  | and a b ia ib => exact congrArg₂ Bool.and (ia hv.1) (ib hv.2)
open _root_.P2Mf6bd8d28 renaming h129 → InfoLossLAR.WorstCase.BooleanExpr.eval_congr
open _root_.P2Mf6bd8d28 renaming h129 → _P3l
private theorem _root_.P2Mf6bd8d28.h902 (start : ℕ) (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (s : ℕ → Bool) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start [op] s start = op.eval s := by
  simp [_root_.InfoLossLAR.WorstCase.BooleanProgram.run, _root_.InfoLossLAR.WorstCase.BooleanOp.assign]
open _root_.P2Mf6bd8d28 renaming h902 → _Pp2
private theorem _root_.P2Mf6bd8d28.h901 (start : ℕ) (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp) (op : _root_.InfoLossLAR.WorstCase.BooleanOp)
    (s : ℕ → Bool) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (ops ++ [op]) s (start + ops.length) =
      op.eval (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start ops s) := by
  rw [_P46, _Pp2]
open _root_.P2Mf6bd8d28 renaming h901 → _Pp1
theorem _root_.P2Mf6bd8d28.h128 (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (start : ℕ) (hv : e.Valid start) (s : ℕ → Bool) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (e.compile start).1 s (e.compile start).2 = e.eval s := by
  induction e generalizing start s with
  | input i => rfl
  | constant b => exact _Pp2 start (.constant b) s
  | negate a ih =>
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _Pp1, _root_.InfoLossLAR.WorstCase.BooleanOp.eval, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval]
    rw [ih start hv]
  | xor a b ia ib | and a b ia ib =>
    have hca := (a.compile_valid start hv.1).2
    have hcb := b.valid_mono hv.2 (Nat.le_add_right start a.size)
    have hb := ib (start + a.size) hcb (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (a.compile start).1 s)
    have heq : b.eval (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (a.compile start).1 s) = b.eval s :=
      b.eval_congr hv.2 (fun i hi => _P47 _ _ _ i hi)
    rw [heq] at hb
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length]
    rw [show start + a.size + b.size = start +
      ((a.compile start).1 ++ (b.compile (start + a.size)).1).length by simp; omega,
      _Pp1, _P46]
    simp only [_root_.InfoLossLAR.WorstCase.BooleanOp.eval, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval]
    rw [_P47 _ _ _ _ hca, ia start hv.1, hb]
open _root_.P2Mf6bd8d28 renaming h128 → InfoLossLAR.WorstCase.BooleanExpr.compile_eval
open _root_.P2Mf6bd8d28 renaming h128 → _P3k
end BooleanExpr
open _root_.P2Mf6bd8d28 renaming h128 → InfoLossLAR.WorstCase.BooleanExpr.compile_eval
open _root_.P2Mf6bd8d28 renaming h128 → _P3k
open _root_.P2Mf6bd8d28 renaming h129 → InfoLossLAR.WorstCase.BooleanExpr.eval_congr
open _root_.P2Mf6bd8d28 renaming h129 → _P3l
open _root_.P2Mf6bd8d28 renaming h901 → _Pp1
open _root_.P2Mf6bd8d28 renaming h902 → _Pp2
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h128 → InfoLossLAR.WorstCase.BooleanExpr.compile_eval
open _root_.P2Mf6bd8d28 renaming h128 → _P3k
open _root_.P2Mf6bd8d28 renaming h129 → InfoLossLAR.WorstCase.BooleanExpr.eval_congr
open _root_.P2Mf6bd8d28 renaming h129 → _P3l
open _root_.P2Mf6bd8d28 renaming h901 → _Pp1
open _root_.P2Mf6bd8d28 renaming h902 → _Pp2
end
open _root_.P2Mf6bd8d28 renaming h128 → InfoLossLAR.WorstCase.BooleanExpr.compile_eval
open _root_.P2Mf6bd8d28 renaming h128 → _P3k
open _root_.P2Mf6bd8d28 renaming h129 → InfoLossLAR.WorstCase.BooleanExpr.eval_congr
open _root_.P2Mf6bd8d28 renaming h129 → _P3l
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
namespace BooleanExpr
theorem _root_.P2Mf6bd8d28.h130 {α : Type} [Fintype α] [DecidableEq α]
    (table : α → Bool) (inputs : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (inputs a).eval s = decide (a = actual)) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup table inputs).eval s = table actual := by
  rw [Bool.eq_iff_iff]
  simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_any_true, List.mem_map, List.mem_filter,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
    have heq : a = actual := by simpa only [h, decide_eq_true_eq] using he
    simpa only [heq] using ha
  · intro ha
    exact ⟨inputs actual, ⟨actual, ha, rfl⟩, by simp [h]⟩
open _root_.P2Mf6bd8d28 renaming h130 → _P3m
theorem _root_.P2Mf6bd8d28.h127 (start : ℕ) (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) (s : ℕ → Bool) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start es).2.map (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start es).1 s) =
      es.map (fun e => e.eval s) := by
  induction es generalizing start s with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hout := (e.compile_valid start he).2
    have ht := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (e.compile start).1 s)
    have href : es.map (fun a => a.eval (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (e.compile start).1 s)) =
        es.map (fun a => a.eval s) := by
      apply List.map_congr_left
      intro a ha
      exact a.eval_congr (h a (by simp [ha])) (fun i hi => _P47 _ _ _ i hi)
    rw [href] at ht
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, List.map_cons, _P46]
    rw [_P47 _ _ _ _ hout, e.compile_eval start he, ht]
open _root_.P2Mf6bd8d28 renaming h127 → _P3j
theorem _root_.P2Mf6bd8d28.h131 {α : Type} [Fintype α] [DecidableEq α]
    (control payload : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (control a).eval s = decide (a = actual)) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex control payload).eval s = (payload actual).eval s := by
  rw [Bool.eq_iff_iff]
  simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_any_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, he⟩
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.eval, Bool.and_eq_true, h, decide_eq_true_eq] at he
    simpa only [he.1] using he.2
  · intro hp
    exact ⟨.and (control actual) (payload actual), ⟨actual, rfl⟩, by simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.eval, h, hp]⟩
open _root_.P2Mf6bd8d28 renaming h131 → _P3n
end BooleanExpr
open _root_.P2Mf6bd8d28 renaming h127 → _P3j
open _root_.P2Mf6bd8d28 renaming h130 → _P3m
open _root_.P2Mf6bd8d28 renaming h131 → _P3n
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h127 → _P3j
open _root_.P2Mf6bd8d28 renaming h130 → _P3m
open _root_.P2Mf6bd8d28 renaming h131 → _P3n
end
open _root_.P2Mf6bd8d28 renaming h127 → _P3j
open _root_.P2Mf6bd8d28 renaming h130 → _P3m
open _root_.P2Mf6bd8d28 renaming h131 → _P3n
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
variable {K Λ σ : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]
namespace Symbolic
variable {width : ℕ}
theorem _root_.P2Mf6bd8d28.h280 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (bits : ℕ → Bool) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (f : σ → σ) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (sym.load f) {cfg with var := f cfg.var} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  exact _P3m _ _ _ cfg.var h.state
open _root_.P2Mf6bd8d28 renaming h280 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_encodes
open _root_.P2Mf6bd8d28 renaming h280 → _P7s
theorem _root_.P2Mf6bd8d28.h285 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (bits : ℕ → Bool) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (k : K) (f : σ → Bool) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push, Function.update_self, ↓reduceIte]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte, List.getElem?_cons_zero]
      exact _P3m _ _ _ cfg.var h.state
    · simp only [hi, ↓reduceDIte]
      rw [h.stack]
      congr 1
      have he : i.val = (i.val - 1) + 1 := by omega
      conv_rhs => rw [he]
      simp only [List.getElem?_cons_succ]
  · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b
open _root_.P2Mf6bd8d28 renaming h285 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_encodes
open _root_.P2Mf6bd8d28 renaming h285 → _P7x
theorem _root_.P2Mf6bd8d28.h287 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (bits : ℕ → Bool) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply _P3m _ _ _ (cfg.var, (cfg.stk k).head?)
  intro a
  simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.eval, h.state, h.stack]
  simp [Prod.ext_iff, List.head?_eq_getElem?]
open _root_.P2Mf6bd8d28 renaming h287 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_encodes
open _root_.P2Mf6bd8d28 renaming h287 → _P7z
theorem _root_.P2Mf6bd8d28.h283 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (bits : ℕ → Bool) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (k : K)
    (hsize : (cfg.stk k).length ≤ width) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (sym.pop k) {cfg with stk := Function.update cfg.stk k (cfg.stk k).tail} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop, Function.update_self, ↓reduceIte]
    by_cases hi : i.val + 1 < width
    · simp only [hi, ↓reduceDIte, h.stack]
      congr 1
      simp
    · simp only [hi, ↓reduceDIte, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval]
      have he : (cfg.stk k).tail[i.val]? = none :=
        List.getElem?_eq_none (by simp only [List.length_tail]; omega)
      rw [he]
  · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b
open _root_.P2Mf6bd8d28 renaming h283 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_encodes
open _root_.P2Mf6bd8d28 renaming h283 → _P7v
theorem _root_.P2Mf6bd8d28.h278 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (bits : ℕ → Bool) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (f : σ → Λ) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (sym.jump f) {cfg with l := some (f cfg.var)} bits := by
  refine ⟨?_, h.state, h.stack⟩
  intro l
  exact _P3m _ _ _ cfg.var h.state
open _root_.P2Mf6bd8d28 renaming h278 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_encodes
open _root_.P2Mf6bd8d28 renaming h278 → _P7q
theorem _root_.P2Mf6bd8d28.h276 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (bits : ℕ → Bool) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym.halt {cfg with l := none} bits := ⟨fun _ => rfl, h.state, h.stack⟩
open _root_.P2Mf6bd8d28 renaming h276 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_encodes
open _root_.P2Mf6bd8d28 renaming h276 → _P7o
theorem _root_.P2Mf6bd8d28.h290 (condition : _root_.InfoLossLAR.WorstCase.BooleanExpr) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width)
    (cfgA cfgB : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (bits : ℕ → Bool)
    (ha : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes a cfgA bits) (hb : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes b cfgB bits) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select condition a b) (if condition.eval bits then cfgA else cfgB) bits := by
  cases hc : condition.eval bits
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.label l
    · intro v; simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.state v
    · intro k i b; simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.stack k i b
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_select, hc, ↓reduceIte] using ha.label l
    · intro v; simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_select, hc, ↓reduceIte] using ha.state v
    · intro k i b; simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_select, hc, ↓reduceIte] using ha.stack k i b
open _root_.P2Mf6bd8d28 renaming h290 → _P82
end Symbolic
open _root_.P2Mf6bd8d28 renaming h276 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_encodes
open _root_.P2Mf6bd8d28 renaming h276 → _P7o
open _root_.P2Mf6bd8d28 renaming h278 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_encodes
open _root_.P2Mf6bd8d28 renaming h278 → _P7q
open _root_.P2Mf6bd8d28 renaming h280 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_encodes
open _root_.P2Mf6bd8d28 renaming h280 → _P7s
open _root_.P2Mf6bd8d28 renaming h283 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_encodes
open _root_.P2Mf6bd8d28 renaming h283 → _P7v
open _root_.P2Mf6bd8d28 renaming h285 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_encodes
open _root_.P2Mf6bd8d28 renaming h285 → _P7x
open _root_.P2Mf6bd8d28 renaming h287 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_encodes
open _root_.P2Mf6bd8d28 renaming h287 → _P7z
open _root_.P2Mf6bd8d28 renaming h290 → _P82
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h276 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_encodes
open _root_.P2Mf6bd8d28 renaming h276 → _P7o
open _root_.P2Mf6bd8d28 renaming h278 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_encodes
open _root_.P2Mf6bd8d28 renaming h278 → _P7q
open _root_.P2Mf6bd8d28 renaming h280 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_encodes
open _root_.P2Mf6bd8d28 renaming h280 → _P7s
open _root_.P2Mf6bd8d28 renaming h283 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_encodes
open _root_.P2Mf6bd8d28 renaming h283 → _P7v
open _root_.P2Mf6bd8d28 renaming h285 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_encodes
open _root_.P2Mf6bd8d28 renaming h285 → _P7x
open _root_.P2Mf6bd8d28 renaming h287 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_encodes
open _root_.P2Mf6bd8d28 renaming h287 → _P7z
open _root_.P2Mf6bd8d28 renaming h290 → _P82
end
open _root_.P2Mf6bd8d28 renaming h276 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_encodes
open _root_.P2Mf6bd8d28 renaming h276 → _P7o
open _root_.P2Mf6bd8d28 renaming h278 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_encodes
open _root_.P2Mf6bd8d28 renaming h278 → _P7q
open _root_.P2Mf6bd8d28 renaming h280 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_encodes
open _root_.P2Mf6bd8d28 renaming h280 → _P7s
open _root_.P2Mf6bd8d28 renaming h283 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_encodes
open _root_.P2Mf6bd8d28 renaming h283 → _P7v
open _root_.P2Mf6bd8d28 renaming h285 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_encodes
open _root_.P2Mf6bd8d28 renaming h285 → _P7x
open _root_.P2Mf6bd8d28 renaming h287 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_encodes
open _root_.P2Mf6bd8d28 renaming h287 → _P7z
open _root_.P2Mf6bd8d28 renaming h290 → _P82
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}
theorem _root_.P2Mf6bd8d28.h292 (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (bits : ℕ → Bool)
    (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (hsize : _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk + _root_.Integration9_9.TM2OutputLength.pushBound q ≤ width) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw q sym) (TM2.stepAux q cfg.var cfg.stk) bits := by
  induction q generalizing sym cfg with
  | push k f q ih =>
    have hs : _root_.Integration9_9.TM2OutputLength.stackSize (Function.update cfg.stk k (f cfg.var :: cfg.stk k)) ≤ _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk + 1 :=
      _root_.Integration9_9.TM2OutputLength.stackSize_update_le cfg.stk k _ _ (Nat.le_add_right _ _)
        (by simpa only [List.length_cons] using Nat.succ_le_succ (_root_.Integration9_9.TM2OutputLength.length_le_stackSize cfg.stk k))
    exact ih (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)}
      (sym.push_encodes cfg bits h k f) (by simp only [_root_.Integration9_9.TM2OutputLength.pushBound] at hsize; dsimp only; omega)
  | peek k f q ih =>
    exact ih (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?}
      (sym.read_encodes cfg bits h hw k f) hsize
  | pop k f q ih =>
    have hs : _root_.Integration9_9.TM2OutputLength.stackSize (Function.update cfg.stk k (cfg.stk k).tail) ≤ _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk :=
      _root_.Integration9_9.TM2OutputLength.stackSize_update_le cfg.stk k _ _ le_rfl
        (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (_root_.Integration9_9.TM2OutputLength.length_le_stackSize cfg.stk k))
    have hr := sym.read_encodes cfg bits h hw k f
    have hp := (sym.read hw k f).pop_encodes {cfg with var := f cfg.var (cfg.stk k).head?}
      bits hr k ((_root_.Integration9_9.TM2OutputLength.length_le_stackSize cfg.stk k).trans (by simp only [_root_.Integration9_9.TM2OutputLength.pushBound] at hsize; omega))
    exact ih ((sym.read hw k f).pop k)
      {cfg with var := f cfg.var (cfg.stk k).head?, stk := Function.update cfg.stk k (cfg.stk k).tail}
      hp (by simp only [_root_.Integration9_9.TM2OutputLength.pushBound] at hsize; dsimp only; omega)
  | load f q ih =>
    exact ih (sym.load f) {cfg with var := f cfg.var} (sym.load_encodes cfg bits h f) hsize
  | branch f q r iq ir =>
    have hq := iq sym cfg h (by simp only [_root_.Integration9_9.TM2OutputLength.pushBound] at hsize; have := le_max_left (_root_.Integration9_9.TM2OutputLength.pushBound q) (_root_.Integration9_9.TM2OutputLength.pushBound r); omega)
    have hr := ir sym cfg h (by simp only [_root_.Integration9_9.TM2OutputLength.pushBound] at hsize; have := le_max_right (_root_.Integration9_9.TM2OutputLength.pushBound q) (_root_.Integration9_9.TM2OutputLength.pushBound r); omega)
    have he := _P82 (_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup f sym.state)
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw q sym) (_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw r sym) _ _ bits hq hr
    rw [_P3m f sym.state bits cfg.var h.state] at he
    cases hf : f cfg.var <;> simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary, TM2.stepAux, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte] using he
  | goto f => exact sym.jump_encodes cfg bits h f
  | halt => exact sym.halt_encodes cfg bits h
open _root_.P2Mf6bd8d28 renaming h292 → _P84
theorem _root_.P2Mf6bd8d28.h304 {α : Type} [Fintype α] [DecidableEq α]
    (control : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (choices : α → _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width)
    (bits : ℕ → Bool) (actual : α) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (hc : ∀ a, (control a).eval bits = decide (a = actual))
    (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (choices actual) cfg bits) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (_root_.InfoLossLAR.WorstCase.TM2Boolean.multiplex control choices) cfg bits := by
  constructor
  · intro l
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.multiplex, _P3n control _ bits actual hc]
    exact h.label l
  · intro v
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.multiplex, _P3n control _ bits actual hc]
    exact h.state v
  · intro k i b
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.multiplex, _P3n control _ bits actual hc]
    exact h.stack k i b
open _root_.P2Mf6bd8d28 renaming h304 → _P8g
theorem _root_.P2Mf6bd8d28.h311 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (bits : ℕ → Bool)
    (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (hsize : _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk + _root_.Integration9_9.TM2OutputLength.programPushBound program ≤ width) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym) (_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program cfg) bits := by
  apply _P8g sym.label _ bits cfg.l _ h.label
  cases hl : cfg.l with
  | none => simpa only [hl, Option.elim_none, _root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep] using h
  | some l =>
    have hq : _root_.Integration9_9.TM2OutputLength.pushBound (program l) ≤ _root_.Integration9_9.TM2OutputLength.programPushBound program :=
      Finset.le_sup (f := fun l => _root_.Integration9_9.TM2OutputLength.pushBound (program l)) (Finset.mem_univ l)
    simpa only [hl, Option.elim_some, _root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep] using
      _P84 hw (program l) sym cfg bits h (by omega)
open _root_.P2Mf6bd8d28 renaming h311 → _P8n
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h292 → _P84
open _root_.P2Mf6bd8d28 renaming h304 → _P8g
open _root_.P2Mf6bd8d28 renaming h311 → _P8n
end
open _root_.P2Mf6bd8d28 renaming h292 → _P84
open _root_.P2Mf6bd8d28 renaming h304 → _P8g
open _root_.P2Mf6bd8d28 renaming h311 → _P8n
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InfoLossLAR.WorstCase.BooleanExpr
theorem _root_.P2Mf6bd8d28.h132 (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) (bound : ℕ)
    (h : ∀ e ∈ es, e.size ≤ bound) : (_root_.InfoLossLAR.WorstCase.BooleanExpr.any es).size ≤ (bound + 4) * es.length + 1 := by
  induction es with
  | nil => simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.any, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.any, _root_.InfoLossLAR.WorstCase.BooleanExpr.size_or, List.length_cons]
    nlinarith
open _root_.P2Mf6bd8d28 renaming h132 → _P3o
theorem _root_.P2Mf6bd8d28.h133 {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (bound : ℕ)
    (h : ∀ a, (inputs a).size ≤ bound) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup table inputs).size ≤ (bound + 4) * Fintype.card α + 1 := by
  have he := _P3o ((Finset.univ.toList.filter table).map inputs) bound (by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
    exact h a)
  have hl : (Finset.univ.toList.filter table).length ≤ Fintype.card α := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      List.length_filter_le table (Finset.univ.toList : List α)
  simp only [List.length_map] at he
  simpa only [_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup] using he.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) 1)
open _root_.P2Mf6bd8d28 renaming h133 → _P3p
theorem _root_.P2Mf6bd8d28.h134 {α : Type} [Fintype α]
    (control payload : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (controlBound payloadBound : ℕ)
    (hc : ∀ a, (control a).size ≤ controlBound)
    (hp : ∀ a, (payload a).size ≤ payloadBound) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex control payload).size ≤
      (controlBound + payloadBound + 5) * Fintype.card α + 1 := by
  have he := _P3o (Finset.univ.toList.map (fun a => and (control a) (payload a)))
    (controlBound + payloadBound + 1) (by
      intro e he
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
      simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.size]
      have := hc a
      have := hp a
      omega)
  simpa only [_root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex, List.length_map, Finset.length_toList, Finset.card_univ, Nat.add_assoc]
    using he
open _root_.P2Mf6bd8d28 renaming h134 → _P3q
end InfoLossLAR.WorstCase.BooleanExpr
open _root_.P2Mf6bd8d28 renaming h132 → _P3o
open _root_.P2Mf6bd8d28 renaming h133 → _P3p
open _root_.P2Mf6bd8d28 renaming h134 → _P3q
end
open _root_.P2Mf6bd8d28 renaming h132 → _P3o
open _root_.P2Mf6bd8d28 renaming h133 → _P3p
open _root_.P2Mf6bd8d28 renaming h134 → _P3q
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}
namespace Symbolic
end Symbolic
namespace Symbolic
theorem _root_.P2Mf6bd8d28.h281 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (bits : ℕ → Bool) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (sym.compiled start).1 bits (sym.output start i) = (sym.get i).eval bits := by
  have he := _P3j start sym.formulas (sym.formulas_valid h) bits
  have hi := congrArg (fun xs : List Bool => xs[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width i).val]?) he
  simp only [List.getElem?_map] at hi
  have ho : (sym.compiled start).2[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width i).val]? = some (sym.output start i) :=
    List.getElem?_eq_getElem _
  change (sym.compiled start).2[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width i).val]?.map
    (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (sym.compiled start).1 bits) = _ at hi
  rw [ho] at hi
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas, List.getElem?_ofFn, dif_pos (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width i).isLt,
    Fin.eta, Equiv.symm_apply_apply, Option.map_some, Option.some.injEq] at hi
  exact hi
open _root_.P2Mf6bd8d28 renaming h281 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.output_eval
open _root_.P2Mf6bd8d28 renaming h281 → _P7t
theorem _root_.P2Mf6bd8d28.h288 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (bits : ℕ → Bool) (he : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (sym.rebound start) cfg (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (sym.compiled start).1 bits) := by
  constructor
  · intro l
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.ofSlots, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, _P7t sym start h bits (.inl l)]
    exact he.label l
  · intro v
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.ofSlots, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, _P7t sym start h bits (.inr (.inl v))]
    exact he.state v
  · intro k i b
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.ofSlots, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, _P7t sym start h bits (.inr (.inr (k, i, b)))]
    exact he.stack k i b
open _root_.P2Mf6bd8d28 renaming h288 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound_encodes
open _root_.P2Mf6bd8d28 renaming h288 → _P80
end Symbolic
open _root_.P2Mf6bd8d28 renaming h281 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.output_eval
open _root_.P2Mf6bd8d28 renaming h281 → _P7t
open _root_.P2Mf6bd8d28 renaming h288 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound_encodes
open _root_.P2Mf6bd8d28 renaming h288 → _P80
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h281 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.output_eval
open _root_.P2Mf6bd8d28 renaming h281 → _P7t
open _root_.P2Mf6bd8d28 renaming h288 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound_encodes
open _root_.P2Mf6bd8d28 renaming h288 → _P80
end
open _root_.P2Mf6bd8d28 renaming h281 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.output_eval
open _root_.P2Mf6bd8d28 renaming h281 → _P7t
open _root_.P2Mf6bd8d28 renaming h288 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound_encodes
open _root_.P2Mf6bd8d28 renaming h288 → _P80
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
@[fun_prop] theorem _root_.P2Mf6bd8d28.h271 : Poly (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State × _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit
  fun_prop
open _root_.P2Mf6bd8d28 renaming h271 → _P7j
end InfoLossLAR.WorstCase.TM2Boolean.RPN
open _root_.P2Mf6bd8d28 renaming h271 → _P7j
end
open _root_.P2Mf6bd8d28 renaming h271 → _P7j
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open Polynomial
theorem _root_.P2Mf6bd8d28.h242 {N M : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s) (hm : N ≤ M) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded M s := by
  exact ⟨h.slots.trans hm, h.operands.trans hm, h.nodes.trans hm,
    fun x hx => (h.refs x hx).trans hm,
    fun x hx => ⟨(h.code x hx).1.trans hm, (h.code x hx).2.1.trans hm,
      (h.code x hx).2.2.trans hm⟩⟩
open _root_.P2Mf6bd8d28 renaming h242 → InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h242 → _P6q
theorem _root_.P2Mf6bd8d28.h263 (xs : List ℕ) (i N : ℕ) (h : ∀ x ∈ xs, x.bits.length ≤ N) :
    ((xs[i]?).getD 0).bits.length ≤ N := by
  by_cases hi : i < xs.length
  · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (show xs.length ≤ i by omega)]
    simp
open _root_.P2Mf6bd8d28 renaming h263 → _P7b
theorem _root_.P2Mf6bd8d28.h260 {N : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node)
    (hx : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.NodeBound (N+1) x) (rest : List ℕ) (hl : rest.length ≤ N)
    (hr : ∀ a ∈ rest, a.bits.length ≤ N+1) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded (N+1) (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit s x rest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit] using Nat.add_le_add_right h.slots 1
  · simpa [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit] using Nat.add_le_add_right hl 1
  · simpa [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit] using Nat.add_le_add_right h.nodes 1
  · intro a ha
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (Nat.add_le_add_right h.slots 1)
    · exact hr a ha
  · intro a ha
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (h.mono (Nat.le_succ N)).code a ha
    · exact hx
open _root_.P2Mf6bd8d28 renaming h260 → _P78
theorem _root_.P2Mf6bd8d28.h270 {N : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s) (hN : 3 ≤ N)
    (token : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) (ht : token.2.bits.length ≤ N+1) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded (N+1) (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step s token) := by
  have hh := h.mono (Nat.le_succ N)
  have h0 := _P7b s.2.1 0 (N+1) hh.refs
  have h1 := _P7b s.2.1 1 (N+1) hh.refs
  have tailLen : s.2.1.tail.length ≤ N := by rw [List.length_tail]; exact (Nat.sub_le _ _).trans h.operands
  have tailTailLen : s.2.1.tail.tail.length ≤ N :=
    by rw [List.length_tail]; omega
  have tailRefs : ∀ a ∈ s.2.1.tail, a.bits.length ≤ N+1 :=
    fun a ha => hh.refs a (List.mem_of_mem_tail ha)
  have tailTailRefs : ∀ a ∈ s.2.1.tail.tail, a.bits.length ≤ N+1 :=
    fun a ha => tailRefs a (List.mem_of_mem_tail ha)
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step
  split
  · refine ⟨hh.slots, ?_, hh.nodes, ?_, hh.code⟩
    · simpa using Nat.add_le_add_right h.operands 1
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hh.refs x hx
  · split
    · apply _P78 h _ _ _ h.operands hh.refs
      norm_num [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.NodeBound]
    · split
      · apply _P78 h _ _ _ h.operands hh.refs
        norm_num [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.NodeBound]
      · split
        · apply _P78 h _ _ _ tailLen tailRefs
          change (3:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ 0 ≤ N+1
          rw [show (3:ℕ).bits.length = 2 by decide]
          exact ⟨by omega, h0, Nat.zero_le _⟩
        · split
          · apply _P78 h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩
          · apply _P78 h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩
open _root_.P2Mf6bd8d28 renaming h270 → _P7i
theorem _root_.P2Mf6bd8d28.h267 (tokens : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) {N : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s)
    (hN : 3 ≤ N) (ht : ∀ t ∈ tokens, t.2.bits.length ≤ N) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded (N+tokens.length) (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run tokens s) := by
  induction tokens generalizing N s with
  | nil => simpa [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run] using h
  | cons t ts ih =>
    have hs := _P7i h hN t ((ht t (by simp)).trans (Nat.le_succ N))
    have hh := ih hs (by omega) (fun u hu => (ht u (by simp [hu])).trans (Nat.le_succ N))
    simpa [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
open _root_.P2Mf6bd8d28 renaming h267 → _P7f
theorem _root_.P2Mf6bd8d28.h261 (xs : List Unit) : (enc xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (encodeList (fun _ : Unit => []) (x::xs)).length = _
    rw [EncodedList.cons_length]
    change (encodeList (fun _ : Unit => []) xs).length = xs.length at ih
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.length_cons]
    omega
open _root_.P2Mf6bd8d28 renaming h261 → _P79
theorem _root_.P2Mf6bd8d28.h255 (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded (enc s).length s := by
  have hs := _P79 s.1
  have ho := EncodedList.length_le Nat.bits s.2.1
  have hn := EncodedList.length_le (enc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node → List Bool) s.2.2
  have he : (enc s).length = 2*(enc s.1).length+1+2*(enc s.2.1).length+1+(enc s.2.2).length := by
    simp only [enc, Coding.encode, encodePair_length]; omega
  change s.2.1.length ≤ (enc s.2.1).length at ho
  change s.2.2.length ≤ (enc s.2.2).length at hn
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro x hx
    have hh := EncodedList.member_length Nat.bits s.2.1 x hx
    change x.bits.length ≤ (enc s.2.1).length at hh
    omega
  · intro x hx
    have hh := EncodedList.member_length (enc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node → List Bool) s.2.2 x hx
    change (enc x).length ≤ (enc s.2.2).length at hh
    have he' : (enc x).length = 2*x.1.bits.length+1+2*x.2.1.bits.length+1+x.2.2.bits.length := by
      simp only [enc, Coding.encode, encodePair_length]; omega
    exact ⟨by omega, by omega, by omega⟩
open _root_.P2Mf6bd8d28 renaming h255 → _P73
theorem _root_.P2Mf6bd8d28.h262 {N : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s) :
    (enc s).length ≤ 20*(N+1)^2 := by
  have hs := _P79 s.1
  have ho := EncodedList.length_bound Nat.bits s.2.1 N h.refs
  have hn := EncodedList.length_bound (enc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node → List Bool) s.2.2 (5*N+2) (by
    intro x hx
    have hb := h.code x hx
    rcases hb with ⟨hb1, hb2, hb3⟩
    change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) x).length ≤ _
    simp only [encodePair_length]
    omega)
  have ho' : (enc s.2.1).length ≤ N*(2*N+1) := ho.trans (Nat.mul_le_mul_right _ h.operands)
  have hn' : (enc s.2.2).length ≤ N*(2*(5*N+2)+1) := hn.trans (Nat.mul_le_mul_right _ h.nodes)
  change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) s).length ≤ _
  simp only [encodePair_length]
  nlinarith [h.slots]
open _root_.P2Mf6bd8d28 renaming h262 → _P7a
theorem _root_.P2Mf6bd8d28.h268 (tokens : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) (pre suf : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token)
    (he : tokens = pre ++ suf) :
    (enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2 := by
  let L := (enc (tokens,s)).length
  have heL : L = 2*(enc tokens).length+1+(enc s).length := encodePair_length _ _ _
  have hpenc : (enc pre).length ≤ (enc tokens).length := by
    change (encodeList enc pre).length ≤ (encodeList enc tokens).length
    rw [he, EncodedList.append, List.length_append]; omega
  have hplen : pre.length ≤ L := by
    have hh := EncodedList.length_le (enc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token → List Bool) pre
    change pre.length ≤ (enc pre).length at hh
    omega
  have hs := (_P73 s).mono (show (enc s).length ≤ L+3 by omega)
  have ht : ∀ t ∈ pre, t.2.bits.length ≤ L+3 := by
    intro t ht
    have hh := EncodedList.member_length (enc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token → List Bool) pre t ht
    change (enc t).length ≤ (enc pre).length at hh
    have hte : (enc t).length = 2*t.1.bits.length+1+t.2.bits.length := encodePair_length _ _ _
    omega
  have hb := _P7f pre hs (by omega) ht
  have hb' := hb.mono (show L+3+pre.length ≤ 2*L+3 by omega)
  have hh := _P7a hb'
  simpa [L, Nat.add_assoc] using hh
open _root_.P2Mf6bd8d28 renaming h268 → _P7g
@[fun_prop] theorem _root_.P2Mf6bd8d28.h269 : Poly (fun x : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token × _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run x.1 x.2) := by
  apply Poly.of_program
  exact _P7j.program.listFold (0,0) (20*(2*X+4)^2) (by
    intro tokens s pre suf he
    simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X]
    change (enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2
    exact _P7g tokens s pre suf he)
open _root_.P2Mf6bd8d28 renaming h269 → _P7h
end InfoLossLAR.WorstCase.TM2Boolean.RPN
open _root_.P2Mf6bd8d28 renaming h242 → InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h242 → _P6q
open _root_.P2Mf6bd8d28 renaming h255 → _P73
open _root_.P2Mf6bd8d28 renaming h260 → _P78
open _root_.P2Mf6bd8d28 renaming h261 → _P79
open _root_.P2Mf6bd8d28 renaming h262 → _P7a
open _root_.P2Mf6bd8d28 renaming h263 → _P7b
open _root_.P2Mf6bd8d28 renaming h267 → _P7f
open _root_.P2Mf6bd8d28 renaming h268 → _P7g
open _root_.P2Mf6bd8d28 renaming h269 → _P7h
open _root_.P2Mf6bd8d28 renaming h270 → _P7i
end
open _root_.P2Mf6bd8d28 renaming h242 → InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h242 → _P6q
open _root_.P2Mf6bd8d28 renaming h255 → _P73
open _root_.P2Mf6bd8d28 renaming h260 → _P78
open _root_.P2Mf6bd8d28 renaming h261 → _P79
open _root_.P2Mf6bd8d28 renaming h262 → _P7a
open _root_.P2Mf6bd8d28 renaming h263 → _P7b
open _root_.P2Mf6bd8d28 renaming h267 → _P7f
open _root_.P2Mf6bd8d28 renaming h268 → _P7g
open _root_.P2Mf6bd8d28 renaming h269 → _P7h
open _root_.P2Mf6bd8d28 renaming h270 → _P7i
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
namespace CodePoly
variable {α β : Type} [Coding α] [Coding β]
theorem _root_.P2Mf6bd8d28.h245 {f : β → _root_.InfoLossLAR.WorstCase.BooleanExpr} {g : α → β} (hf : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly f) (hg : Poly g) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => f (g a)) := Automatic.Poly.comp (f := fun b => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (f b)) (g := g) hf hg
open _root_.P2Mf6bd8d28 renaming h245 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.comp
open _root_.P2Mf6bd8d28 renaming h245 → _P6t
theorem _root_.P2Mf6bd8d28.h247 {f : α → ℕ} (hf : Poly f) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => .input (f a)) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code
  fun_prop
open _root_.P2Mf6bd8d28 renaming h247 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.input
open _root_.P2Mf6bd8d28 renaming h247 → _P6v
theorem _root_.P2Mf6bd8d28.h246 (b : Bool) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun _ : α => .constant b) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly
  exact Automatic.Poly.const _
open _root_.P2Mf6bd8d28 renaming h246 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.constant
open _root_.P2Mf6bd8d28 renaming h246 → _P6u
theorem _root_.P2Mf6bd8d28.h251 {f : α → _root_.InfoLossLAR.WorstCase.BooleanExpr} (hf : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly f) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => .negate (f a)) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly at hf ⊢
  change Poly (fun a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (f a) ++ [(3,0)])
  fun_prop
open _root_.P2Mf6bd8d28 renaming h251 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.negate
open _root_.P2Mf6bd8d28 renaming h251 → _P6z
theorem _root_.P2Mf6bd8d28.h243 {f g : α → _root_.InfoLossLAR.WorstCase.BooleanExpr} (hf : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly f) (hg : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly g) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => .and (f a) (g a)) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly at hf hg ⊢
  change Poly (fun a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (f a) ++ _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (g a) ++ [(5,0)])
  fun_prop
open _root_.P2Mf6bd8d28 renaming h243 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.and
open _root_.P2Mf6bd8d28 renaming h243 → _P6r
theorem _root_.P2Mf6bd8d28.h252 {f g : α → _root_.InfoLossLAR.WorstCase.BooleanExpr} (hf : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly f) (hg : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly g) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.or (f a) (g a)) := by
  exact (hf.negate.and hg.negate).negate
open _root_.P2Mf6bd8d28 renaming h252 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.or
open _root_.P2Mf6bd8d28 renaming h252 → _P70
theorem _root_.P2Mf6bd8d28.h253 {f g h : α → _root_.InfoLossLAR.WorstCase.BooleanExpr} (hf : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly f) (hg : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly g) (hh : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly h) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.select (f a) (g a) (h a)) := by
  exact (hf.and hg).or (hf.negate.and hh)
open _root_.P2Mf6bd8d28 renaming h253 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.select
open _root_.P2Mf6bd8d28 renaming h253 → _P71
theorem _root_.P2Mf6bd8d28.h248 {p : α → Bool} {f g : α → _root_.InfoLossLAR.WorstCase.BooleanExpr} (hp : Poly p)
    (hf : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly f) (hg : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly g) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => if p a then f a else g a) := by
  change Poly (fun a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (if p a then f a else g a))
  have he : (fun a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (if p a then f a else g a)) =
      (fun a => if p a then _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (f a) else _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (g a)) := by funext a; split <;> rfl
  rw [he]
  exact Poly.ite hp hf hg
open _root_.P2Mf6bd8d28 renaming h248 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.ite
open _root_.P2Mf6bd8d28 renaming h248 → _P6w
theorem _root_.P2Mf6bd8d28.h244 {ι : Type} (indices : List ι) (f : ι → α → _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (hf : ∀ i ∈ indices, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (f i)) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.any (indices.map (fun i => f i a))) := by
  induction indices with
  | nil => exact _P6u false
  | cons i is ih =>
    exact (hf i (by simp)).or (ih (fun j hj => hf j (by simp [hj])))
open _root_.P2Mf6bd8d28 renaming h244 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.any
open _root_.P2Mf6bd8d28 renaming h244 → _P6s
theorem _root_.P2Mf6bd8d28.h249 {ι : Type} [Fintype ι] (table : ι → Bool) (f : ι → α → _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (hf : ∀ i, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (f i)) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup table (fun i => f i a)) :=
  _P6s _ f (fun i _ => hf i)
open _root_.P2Mf6bd8d28 renaming h249 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.lookup
open _root_.P2Mf6bd8d28 renaming h249 → _P6x
theorem _root_.P2Mf6bd8d28.h250 {ι : Type} [Fintype ι] (f g : ι → α → _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (hf : ∀ i, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (f i)) (hg : ∀ i, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (g i)) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex (fun i => f i a) (fun i => g i a)) :=
  _P6s _ _ (fun i _ => (hf i).and (hg i))
open _root_.P2Mf6bd8d28 renaming h250 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.multiplex
open _root_.P2Mf6bd8d28 renaming h250 → _P6y
end CodePoly
open _root_.P2Mf6bd8d28 renaming h243 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.and
open _root_.P2Mf6bd8d28 renaming h243 → _P6r
open _root_.P2Mf6bd8d28 renaming h244 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.any
open _root_.P2Mf6bd8d28 renaming h244 → _P6s
open _root_.P2Mf6bd8d28 renaming h245 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.comp
open _root_.P2Mf6bd8d28 renaming h245 → _P6t
open _root_.P2Mf6bd8d28 renaming h246 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.constant
open _root_.P2Mf6bd8d28 renaming h246 → _P6u
open _root_.P2Mf6bd8d28 renaming h247 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.input
open _root_.P2Mf6bd8d28 renaming h247 → _P6v
open _root_.P2Mf6bd8d28 renaming h248 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.ite
open _root_.P2Mf6bd8d28 renaming h248 → _P6w
open _root_.P2Mf6bd8d28 renaming h249 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.lookup
open _root_.P2Mf6bd8d28 renaming h249 → _P6x
open _root_.P2Mf6bd8d28 renaming h250 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.multiplex
open _root_.P2Mf6bd8d28 renaming h250 → _P6y
open _root_.P2Mf6bd8d28 renaming h251 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.negate
open _root_.P2Mf6bd8d28 renaming h251 → _P6z
open _root_.P2Mf6bd8d28 renaming h252 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.or
open _root_.P2Mf6bd8d28 renaming h252 → _P70
open _root_.P2Mf6bd8d28 renaming h253 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.select
open _root_.P2Mf6bd8d28 renaming h253 → _P71
@[fun_prop] theorem _root_.P2Mf6bd8d28.h259 :
    Poly (fun x : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token × List Unit => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.compileTokens x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.compileTokens
  fun_prop
open _root_.P2Mf6bd8d28 renaming h259 → _P77
end InfoLossLAR.WorstCase.TM2Boolean.RPN
open _root_.P2Mf6bd8d28 renaming h243 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.and
open _root_.P2Mf6bd8d28 renaming h243 → _P6r
open _root_.P2Mf6bd8d28 renaming h244 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.any
open _root_.P2Mf6bd8d28 renaming h244 → _P6s
open _root_.P2Mf6bd8d28 renaming h245 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.comp
open _root_.P2Mf6bd8d28 renaming h245 → _P6t
open _root_.P2Mf6bd8d28 renaming h246 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.constant
open _root_.P2Mf6bd8d28 renaming h246 → _P6u
open _root_.P2Mf6bd8d28 renaming h247 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.input
open _root_.P2Mf6bd8d28 renaming h247 → _P6v
open _root_.P2Mf6bd8d28 renaming h248 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.ite
open _root_.P2Mf6bd8d28 renaming h248 → _P6w
open _root_.P2Mf6bd8d28 renaming h249 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.lookup
open _root_.P2Mf6bd8d28 renaming h249 → _P6x
open _root_.P2Mf6bd8d28 renaming h250 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.multiplex
open _root_.P2Mf6bd8d28 renaming h250 → _P6y
open _root_.P2Mf6bd8d28 renaming h251 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.negate
open _root_.P2Mf6bd8d28 renaming h251 → _P6z
open _root_.P2Mf6bd8d28 renaming h252 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.or
open _root_.P2Mf6bd8d28 renaming h252 → _P70
open _root_.P2Mf6bd8d28 renaming h253 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.select
open _root_.P2Mf6bd8d28 renaming h253 → _P71
open _root_.P2Mf6bd8d28 renaming h259 → _P77
end
open _root_.P2Mf6bd8d28 renaming h243 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.and
open _root_.P2Mf6bd8d28 renaming h243 → _P6r
open _root_.P2Mf6bd8d28 renaming h244 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.any
open _root_.P2Mf6bd8d28 renaming h244 → _P6s
open _root_.P2Mf6bd8d28 renaming h245 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.comp
open _root_.P2Mf6bd8d28 renaming h245 → _P6t
open _root_.P2Mf6bd8d28 renaming h246 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.constant
open _root_.P2Mf6bd8d28 renaming h246 → _P6u
open _root_.P2Mf6bd8d28 renaming h247 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.input
open _root_.P2Mf6bd8d28 renaming h247 → _P6v
open _root_.P2Mf6bd8d28 renaming h248 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.ite
open _root_.P2Mf6bd8d28 renaming h248 → _P6w
open _root_.P2Mf6bd8d28 renaming h249 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.lookup
open _root_.P2Mf6bd8d28 renaming h249 → _P6x
open _root_.P2Mf6bd8d28 renaming h250 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.multiplex
open _root_.P2Mf6bd8d28 renaming h250 → _P6y
open _root_.P2Mf6bd8d28 renaming h251 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.negate
open _root_.P2Mf6bd8d28 renaming h251 → _P6z
open _root_.P2Mf6bd8d28 renaming h252 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.or
open _root_.P2Mf6bd8d28 renaming h252 → _P70
open _root_.P2Mf6bd8d28 renaming h253 → InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly.select
open _root_.P2Mf6bd8d28 renaming h253 → _P71
open _root_.P2Mf6bd8d28 renaming h259 → _P77
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ α : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]
namespace CodeFamily
variable [Coding α]
theorem _root_.P2Mf6bd8d28.h194 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → σ) : (sym.load f).IsPoly :=
  ⟨h.label, fun v => _P6x _ sym.state h.state, h.stack⟩
open _root_.P2Mf6bd8d28 renaming h194 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.load_poly
open _root_.P2Mf6bd8d28 renaming h194 → _P5e
theorem _root_.P2Mf6bd8d28.h197 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Bool) :
    (sym.push k f).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2 = 0)) := by fun_prop
    have hf := _P6x (fun v => decide (b = some (f v)))
      (fun v (x : α × ℕ) => sym.state v x.1) (fun v => (h.state v).comp (by fun_prop))
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2-1)) by fun_prop)
    simpa only [decide_eq_true_eq] using _P6w hi hf ht
  · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push, hj, ↓reduceIte] using h.stack j b
open _root_.P2Mf6bd8d28 renaming h197 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push_poly
open _root_.P2Mf6bd8d28 renaming h197 → _P5h
theorem _root_.P2Mf6bd8d28.h198 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Option Bool → σ) :
    (sym.read k f).IsPoly := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  change _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2)) (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0))))
  apply _P6x
  intro u
  exact (h.state u.1).and ((h.stack k u.2).comp (by fun_prop))
open _root_.P2Mf6bd8d28 renaming h198 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.read_poly
open _root_.P2Mf6bd8d28 renaming h198 → _P5i
theorem _root_.P2Mf6bd8d28.h196 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) (width : α → ℕ)
    (hw : Poly width) (k : K) : (sym.pop width k).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2+1 < width x.1)) := by fun_prop
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2+1)) by fun_prop)
    simpa only [decide_eq_true_eq] using _P6w hi ht (_P6u (decide (b=none)))
  · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop, hj, ↓reduceIte] using h.stack j b
open _root_.P2Mf6bd8d28 renaming h196 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop_poly
open _root_.P2Mf6bd8d28 renaming h196 → _P5g
theorem _root_.P2Mf6bd8d28.h193 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → Λ) : (sym.jump f).IsPoly :=
  ⟨fun l => _P6x _ sym.state h.state, h.state, h.stack⟩
open _root_.P2Mf6bd8d28 renaming h193 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.jump_poly
open _root_.P2Mf6bd8d28 renaming h193 → _P5d
theorem _root_.P2Mf6bd8d28.h191 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) : sym.halt.IsPoly :=
  ⟨fun l => _P6u (decide (l=none)), h.state, h.stack⟩
open _root_.P2Mf6bd8d28 renaming h191 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.halt_poly
open _root_.P2Mf6bd8d28 renaming h191 → _P5b
theorem _root_.P2Mf6bd8d28.h200 (condition : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α)
    (hc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly condition) (ha : a.IsPoly) (hb : b.IsPoly) : (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.select condition a b).IsPoly :=
  ⟨fun l => hc.select (ha.label l) (hb.label l),
    fun v => hc.select (ha.state v) (hb.state v),
    fun k v => (hc.comp (by fun_prop)).select (ha.stack k v) (hb.stack k v)⟩
open _root_.P2Mf6bd8d28 renaming h200 → _P5k
end CodeFamily
open _root_.P2Mf6bd8d28 renaming h191 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.halt_poly
open _root_.P2Mf6bd8d28 renaming h191 → _P5b
open _root_.P2Mf6bd8d28 renaming h193 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.jump_poly
open _root_.P2Mf6bd8d28 renaming h193 → _P5d
open _root_.P2Mf6bd8d28 renaming h194 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.load_poly
open _root_.P2Mf6bd8d28 renaming h194 → _P5e
open _root_.P2Mf6bd8d28 renaming h196 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop_poly
open _root_.P2Mf6bd8d28 renaming h196 → _P5g
open _root_.P2Mf6bd8d28 renaming h197 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push_poly
open _root_.P2Mf6bd8d28 renaming h197 → _P5h
open _root_.P2Mf6bd8d28 renaming h198 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.read_poly
open _root_.P2Mf6bd8d28 renaming h198 → _P5i
open _root_.P2Mf6bd8d28 renaming h200 → _P5k
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h191 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.halt_poly
open _root_.P2Mf6bd8d28 renaming h191 → _P5b
open _root_.P2Mf6bd8d28 renaming h193 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.jump_poly
open _root_.P2Mf6bd8d28 renaming h193 → _P5d
open _root_.P2Mf6bd8d28 renaming h194 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.load_poly
open _root_.P2Mf6bd8d28 renaming h194 → _P5e
open _root_.P2Mf6bd8d28 renaming h196 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop_poly
open _root_.P2Mf6bd8d28 renaming h196 → _P5g
open _root_.P2Mf6bd8d28 renaming h197 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push_poly
open _root_.P2Mf6bd8d28 renaming h197 → _P5h
open _root_.P2Mf6bd8d28 renaming h198 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.read_poly
open _root_.P2Mf6bd8d28 renaming h198 → _P5i
open _root_.P2Mf6bd8d28 renaming h200 → _P5k
end
open _root_.P2Mf6bd8d28 renaming h191 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.halt_poly
open _root_.P2Mf6bd8d28 renaming h191 → _P5b
open _root_.P2Mf6bd8d28 renaming h193 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.jump_poly
open _root_.P2Mf6bd8d28 renaming h193 → _P5d
open _root_.P2Mf6bd8d28 renaming h194 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.load_poly
open _root_.P2Mf6bd8d28 renaming h194 → _P5e
open _root_.P2Mf6bd8d28 renaming h196 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop_poly
open _root_.P2Mf6bd8d28 renaming h196 → _P5g
open _root_.P2Mf6bd8d28 renaming h197 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push_poly
open _root_.P2Mf6bd8d28 renaming h197 → _P5h
open _root_.P2Mf6bd8d28 renaming h198 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.read_poly
open _root_.P2Mf6bd8d28 renaming h198 → _P5i
open _root_.P2Mf6bd8d28 renaming h200 → _P5k
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.CodeFamily
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable [Coding α]
theorem _root_.P2Mf6bd8d28.h188 (width : α → ℕ) (hw : Poly width)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode width q sym).IsPoly := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_poly h k f)
  | peek k f q ih => exact ih _ (sym.read_poly h k f)
  | pop k f q ih => exact ih _ ((sym.read k f).pop_poly (sym.read_poly h k f) width hw k)
  | load f q ih => exact ih _ (sym.load_poly h f)
  | branch f q r iq ir =>
    exact _P5k _ _ _ (_P6x f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_poly h f
  | halt => exact sym.halt_poly h
open _root_.P2Mf6bd8d28 renaming h188 → _P58
theorem _root_.P2Mf6bd8d28.h195 {ι : Type} [Fintype ι]
    (control : ι → α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (choices : ι → _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α)
    (hc : ∀ i, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (control i)) (hp : ∀ i, (choices i).IsPoly) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.multiplexCode control choices).IsPoly :=
  ⟨fun l => _P6y _ _ hc (fun i => (hp i).label l),
    fun v => _P6y _ _ hc (fun i => (hp i).state v),
    fun k b => _P6y _ _ (fun i => (hc i).comp (by fun_prop)) (fun i => (hp i).stack k b)⟩
open _root_.P2Mf6bd8d28 renaming h195 → _P5f
theorem _root_.P2Mf6bd8d28.h201 (width : α → ℕ) (hw : Poly width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.transitionCode width program sym).IsPoly := by
  apply _P5f _ _ h.label
  intro l
  cases l with
  | none => exact h
  | some l => exact _P58 width hw (program l) sym h
open _root_.P2Mf6bd8d28 renaming h201 → _P5l
end InfoLossLAR.WorstCase.TM2Boolean.CodeFamily
open _root_.P2Mf6bd8d28 renaming h188 → _P58
open _root_.P2Mf6bd8d28 renaming h195 → _P5f
open _root_.P2Mf6bd8d28 renaming h201 → _P5l
end
open _root_.P2Mf6bd8d28 renaming h188 → _P58
open _root_.P2Mf6bd8d28 renaming h195 → _P5f
open _root_.P2Mf6bd8d28 renaming h201 → _P5l
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
theorem _root_.P2Mf6bd8d28.h296 {α β ι : Type} [Coding α] [Coding β] [Inhabited β]
    (indices : List ι) (f : ι → α → List β) (hf : ∀ i ∈ indices, Poly (f i)) :
    Poly (fun a => indices.flatMap (fun i => f i a)) := by
  induction indices with
  | nil => exact Automatic.Poly.const []
  | cons i is ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun a => f i a ++ is.flatMap (fun j => f j a))
    fun_prop
open _root_.P2Mf6bd8d28 renaming h296 → _P88
namespace CodeFamily
variable {K Λ σ α : Type} [Fintype K] [Fintype Λ] [Fintype σ]
theorem _root_.P2Mf6bd8d28.h189 [Coding α] (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width : α → List Unit) (hw : Poly width) : Poly (sym.codes width) := by
  have hlabel := _P88 (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Λ)))
    (fun l a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.label l a)) (fun l _ => h.label l)
  have hstate := _P88 (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin σ))
    (fun v a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.state v a)) (fun v _ => h.state v)
  have hstack : ∀ k, Poly (fun a : α =>
      (List.range (width a).length).flatMap (fun i =>
        (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.stack k b (a,i))))) := by
    intro k
    have hcell := _P88 (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Bool)))
      (fun b (x : α × ℕ) => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.stack k b x)) (fun b _ => h.stack k b)
    apply Automatic.Poly.list_flatMap hcell
    exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := width) Automatic.Poly.list_indices hw
  have hstackAll := _P88 (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin K)) _ (fun k _ => hstack k)
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes
  fun_prop
open _root_.P2Mf6bd8d28 renaming h189 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes_poly
open _root_.P2Mf6bd8d28 renaming h189 → _P59
theorem _root_.P2Mf6bd8d28.h190 [Coding α] (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width slots : α → List Unit) (hw : Poly width) (hs : Poly slots) : Poly (sym.compile width slots) := by
  have hc := sym.codes_poly h width hw
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.compile
  fun_prop
open _root_.P2Mf6bd8d28 renaming h190 → _P5a
end CodeFamily
open _root_.P2Mf6bd8d28 renaming h189 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes_poly
open _root_.P2Mf6bd8d28 renaming h189 → _P59
open _root_.P2Mf6bd8d28 renaming h190 → _P5a
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h189 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes_poly
open _root_.P2Mf6bd8d28 renaming h189 → _P59
open _root_.P2Mf6bd8d28 renaming h190 → _P5a
open _root_.P2Mf6bd8d28 renaming h296 → _P88
end
open _root_.P2Mf6bd8d28 renaming h189 → InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes_poly
open _root_.P2Mf6bd8d28 renaming h189 → _P59
open _root_.P2Mf6bd8d28 renaming h190 → _P5a
open _root_.P2Mf6bd8d28 renaming h296 → _P88
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing StateTransition
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}
theorem _root_.P2Mf6bd8d28.h307 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) :
    _root_.Integration9_9.TM2OutputLength.stackSize (_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program cfg).stk ≤ _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk + _root_.Integration9_9.TM2OutputLength.programPushBound program := by
  cases hl : cfg.l with
  | none => simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep, hl, Option.elim_none] using Nat.le_add_right (_root_.Integration9_9.TM2OutputLength.stackSize cfg.stk) _
  | some l =>
    have hc := _root_.Integration9_9.TM2OutputLength.stepAux_stackSize_le (program l) cfg.var cfg.stk
    have hb : _root_.Integration9_9.TM2OutputLength.pushBound (program l) ≤ _root_.Integration9_9.TM2OutputLength.programPushBound program :=
      Finset.le_sup (f := fun l => _root_.Integration9_9.TM2OutputLength.pushBound (program l)) (Finset.mem_univ l)
    simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep, hl, Option.elim_some] using hc.trans (Nat.add_le_add_left hb _)
open _root_.P2Mf6bd8d28 renaming h307 → _P8j
theorem _root_.P2Mf6bd8d28.h293 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (bits : ℕ → Bool)
    (hv : sym.Valid start) (he : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits)
    (hsize : _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk + _root_.Integration9_9.TM2OutputLength.programPushBound program * ticks ≤ width) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).2 ((_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program)^[ticks] cfg)
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).1 bits) := by
  induction ticks generalizing start sym cfg bits with
  | zero => exact he
  | succ ticks ih =>
    have ht := _root_.InfoLossLAR.WorstCase.TM2Boolean.transition_valid hw program sym hv
    have hcap : _root_.Integration9_9.TM2OutputLength.stackSize cfg.stk + _root_.Integration9_9.TM2OutputLength.programPushBound program ≤ width := by nlinarith
    have hs := _P8n hw program sym cfg bits he hcap
    have hf := (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).rebound_encodes start ht _ bits hs
    have hv' := (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).rebound_valid start ht
    have hg := _P8j program cfg
    have hremaining : _root_.Integration9_9.TM2OutputLength.stackSize (_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program cfg).stk + _root_.Integration9_9.TM2OutputLength.programPushBound program * ticks ≤ width := by
      nlinarith
    have hh := ih _ _ _ _ hv' hf hremaining
    simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun, _P46, Function.iterate_succ_apply] using hh
open _root_.P2Mf6bd8d28 renaming h293 → _P85
theorem _root_.P2Mf6bd8d28.h306 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (h : TM2.step program a = some b) : _root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program a = b := by
  rcases a with ⟨l, v, stackStore⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa only [TM2.step, Option.some.injEq, _root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep, Option.elim_some] using h
open _root_.P2Mf6bd8d28 renaming h306 → _P8i
theorem _root_.P2Mf6bd8d28.h305 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (h : a.l = none) : _root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program a = a := by
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep, h, Option.elim_none]
open _root_.P2Mf6bd8d28 renaming h305 → _P8h
private theorem _root_.P2Mf6bd8d28.h908 {α : Type} (step : α → Option α) (n : ℕ) :
    ((fun c : Option α => c.bind step)^[n]) none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih
open _root_.P2Mf6bd8d28 renaming h908 → _Pp8
theorem _root_.P2Mf6bd8d28.h309 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (steps : ℕ) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ)
    (h : ((fun c : Option (_root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) => c.bind (TM2.step program))^[steps]) (some a) = some b) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program)^[steps] a = b := by
  induction steps generalizing a with
  | zero => simpa using h
  | succ steps ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : TM2.step program a with
    | none => simp only [Option.bind_some, hs, _Pp8] at h; contradiction
    | some next =>
      simp only [Option.bind_some, hs] at h
      rw [Function.iterate_succ_apply, _P8i program a next hs]
      exact ih next h
open _root_.P2Mf6bd8d28 renaming h309 → _P8l
theorem _root_.P2Mf6bd8d28.h308 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (ticks : ℕ)
    (h : EvalsToInTime (TM2.step program) a (some b) ticks) (hb : b.l = none) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program)^[ticks] a = b := by
  have hs := _P8l program h.steps a b h.evals_in_steps
  have he : ticks = (ticks - h.steps) + h.steps := by have := h.steps_le_m; omega
  rw [he, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (_P8h program b hb) _
open _root_.P2Mf6bd8d28 renaming h308 → _P8k
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h293 → _P85
open _root_.P2Mf6bd8d28 renaming h305 → _P8h
open _root_.P2Mf6bd8d28 renaming h306 → _P8i
open _root_.P2Mf6bd8d28 renaming h307 → _P8j
open _root_.P2Mf6bd8d28 renaming h308 → _P8k
open _root_.P2Mf6bd8d28 renaming h309 → _P8l
open _root_.P2Mf6bd8d28 renaming h908 → _Pp8
end
open _root_.P2Mf6bd8d28 renaming h293 → _P85
open _root_.P2Mf6bd8d28 renaming h305 → _P8h
open _root_.P2Mf6bd8d28 renaming h306 → _P8i
open _root_.P2Mf6bd8d28 renaming h307 → _P8j
open _root_.P2Mf6bd8d28 renaming h308 → _P8k
open _root_.P2Mf6bd8d28 renaming h309 → _P8l
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}
namespace Symbolic
theorem _root_.P2Mf6bd8d28.h273 {small big : ℕ} {sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width}
    (h : sym.Bounded small) (hle : small ≤ big) : sym.Bounded big :=
  ⟨fun l => (h.label l).trans hle, fun v => (h.state v).trans hle,
    fun k i b => (h.stack k i b).trans hle⟩
open _root_.P2Mf6bd8d28 renaming h273 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h273 → _P7l
private theorem _root_.P2Mf6bd8d28.h910 (bound : ℕ) : bound ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound; omega
open _root_.P2Mf6bd8d28 renaming h910 → _Ppa
private theorem _root_.P2Mf6bd8d28.h909 (bound : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.lookupBound σ bound ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound; omega
open _root_.P2Mf6bd8d28 renaming h909 → _Pp9
private theorem _root_.P2Mf6bd8d28.h911 (bound : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.readBound σ bound ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound; omega
open _root_.P2Mf6bd8d28 renaming h911 → _Ppb
theorem _root_.P2Mf6bd8d28.h279 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → σ) :
    (sym.load f).Bounded (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (_Ppa bound), ?_,
    fun k i b => (h.stack k i b).trans (_Ppa bound)⟩
  intro v
  exact (_P3p _ _ bound h.state).trans (_Pp9 bound)
open _root_.P2Mf6bd8d28 renaming h279 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_bounded
open _root_.P2Mf6bd8d28 renaming h279 → _P7r
theorem _root_.P2Mf6bd8d28.h284 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Bounded (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (_Ppa bound),
    fun v => (h.state v).trans (_Ppa bound), ?_⟩
  intro j i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push]
  split_ifs
  · exact (_P3p _ _ bound h.state).trans (_Pp9 bound)
  · exact (h.stack _ _ _).trans (_Ppa bound)
  · exact (h.stack _ _ _).trans (_Ppa bound)
open _root_.P2Mf6bd8d28 renaming h284 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_bounded
open _root_.P2Mf6bd8d28 renaming h284 → _P7w
theorem _root_.P2Mf6bd8d28.h286 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) :
    (sym.read hw k f).Bounded (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (_Ppa bound), ?_,
    fun k i b => (h.stack k i b).trans (_Ppa bound)⟩
  intro v
  have hi : ∀ a : σ × Option Bool,
      (BooleanExpr.and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2)).size ≤ 2 * bound + 1 := by
    intro a
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.size]
    have := h.state a.1
    have := h.stack k ⟨0, hw⟩ a.2
    omega
  have ht := _P3p (fun a : σ × Option Bool => decide (v = f a.1 a.2)) _
    (2 * bound + 1) hi
  have hb : ((sym.read hw k f).state v).size ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.readBound σ bound := by
    simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.readBound, Nat.add_assoc] using ht
  exact hb.trans (_Ppb bound)
open _root_.P2Mf6bd8d28 renaming h286 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_bounded
open _root_.P2Mf6bd8d28 renaming h286 → _P7y
theorem _root_.P2Mf6bd8d28.h282 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hb : 1 ≤ bound) (k : K) : (sym.pop k).Bounded bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop]
  split_ifs
  · exact h.stack _ _ _
  · exact hb
  · exact h.stack _ _ _
open _root_.P2Mf6bd8d28 renaming h282 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_bounded
open _root_.P2Mf6bd8d28 renaming h282 → _P7u
theorem _root_.P2Mf6bd8d28.h277 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → Λ) :
    (sym.jump f).Bounded (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ bound) := by
  refine ⟨?_, fun v => (h.state v).trans (_Ppa bound),
    fun k i b => (h.stack k i b).trans (_Ppa bound)⟩
  intro l
  exact (_P3p _ _ bound h.state).trans (_Pp9 bound)
open _root_.P2Mf6bd8d28 renaming h277 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_bounded
open _root_.P2Mf6bd8d28 renaming h277 → _P7p
theorem _root_.P2Mf6bd8d28.h275 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) :
    sym.halt.Bounded (bound + 1) :=
  ⟨fun _ => by simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]; omega,
    fun v => (h.state v).trans (Nat.le_add_right _ _),
    fun k i b => (h.stack k i b).trans (Nat.le_add_right _ _)⟩
open _root_.P2Mf6bd8d28 renaming h275 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_bounded
open _root_.P2Mf6bd8d28 renaming h275 → _P7n
theorem _root_.P2Mf6bd8d28.h289 (condition : _root_.InfoLossLAR.WorstCase.BooleanExpr) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width)
    (conditionBound firstBound secondBound : ℕ)
    (hc : condition.size ≤ conditionBound) (ha : a.Bounded firstBound) (hb : b.Bounded secondBound) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select condition a b).Bounded (2 * conditionBound + firstBound + secondBound + 7) := by
  have hh (e f : _root_.InfoLossLAR.WorstCase.BooleanExpr) (he : e.size ≤ firstBound) (hf : f.size ≤ secondBound) :
      (_root_.InfoLossLAR.WorstCase.BooleanExpr.select condition e f).size ≤ 2 * conditionBound + firstBound + secondBound + 7 := by
    rw [_root_.InfoLossLAR.WorstCase.BooleanExpr.size_select]; omega
  exact ⟨fun l => hh _ _ (ha.label l) (hb.label l),
    fun v => hh _ _ (ha.state v) (hb.state v),
    fun k i b => hh _ _ (ha.stack k i b) (hb.stack k i b)⟩
open _root_.P2Mf6bd8d28 renaming h289 → _P81
theorem _root_.P2Mf6bd8d28.h274 (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start bound : ℕ) (h : sym.Bounded bound) :
    (sym.compiled start).1.length ≤ bound * Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_length]
  have hh : ∀ e ∈ sym.formulas, e.size ≤ bound := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    generalize (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width).symm i = slot
    rcases slot with l | v | ⟨k, i, b⟩
    · exact h.label l
    · exact h.state v
    · exact h.stack k i b
  have sumBound : ∀ es : List _root_.InfoLossLAR.WorstCase.BooleanExpr, (∀ e ∈ es, e.size ≤ bound) →
      (es.map _root_.InfoLossLAR.WorstCase.BooleanExpr.size).sum ≤ es.length * bound := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      intro hx
      have he := hx e (by simp)
      have ht := ih (fun a ha => hx a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hl := sumBound sym.formulas hh
  simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas_length, Nat.mul_comm] using hl
open _root_.P2Mf6bd8d28 renaming h274 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled_length_le
open _root_.P2Mf6bd8d28 renaming h274 → _P7m
end Symbolic
open _root_.P2Mf6bd8d28 renaming h273 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h273 → _P7l
open _root_.P2Mf6bd8d28 renaming h274 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled_length_le
open _root_.P2Mf6bd8d28 renaming h274 → _P7m
open _root_.P2Mf6bd8d28 renaming h275 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_bounded
open _root_.P2Mf6bd8d28 renaming h275 → _P7n
open _root_.P2Mf6bd8d28 renaming h277 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_bounded
open _root_.P2Mf6bd8d28 renaming h277 → _P7p
open _root_.P2Mf6bd8d28 renaming h279 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_bounded
open _root_.P2Mf6bd8d28 renaming h279 → _P7r
open _root_.P2Mf6bd8d28 renaming h282 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_bounded
open _root_.P2Mf6bd8d28 renaming h282 → _P7u
open _root_.P2Mf6bd8d28 renaming h284 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_bounded
open _root_.P2Mf6bd8d28 renaming h284 → _P7w
open _root_.P2Mf6bd8d28 renaming h286 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_bounded
open _root_.P2Mf6bd8d28 renaming h286 → _P7y
open _root_.P2Mf6bd8d28 renaming h289 → _P81
open _root_.P2Mf6bd8d28 renaming h909 → _Pp9
open _root_.P2Mf6bd8d28 renaming h910 → _Ppa
open _root_.P2Mf6bd8d28 renaming h911 → _Ppb
theorem _root_.P2Mf6bd8d28.h291 (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw q sym).Bounded (_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliaryBound q bound) := by
  induction q generalizing sym bound with
  | push k f q ih => exact ih _ _ (sym.push_bounded h k f)
  | peek k f q ih => exact ih _ _ (sym.read_bounded h hw k f)
  | pop k f q ih =>
    exact ih _ _ ((sym.read hw k f).pop_bounded (sym.read_bounded h hw k f)
      (by simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.lookupBound, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.readBound]; omega) k)
  | load f q ih => exact ih _ _ (sym.load_bounded h f)
  | branch f q r iq ir =>
    exact _P81 _ _ _ _ _ _ (_P3p f sym.state bound h.state)
      (iq _ _ h) (ir _ _ h)
  | goto f => exact sym.jump_bounded h f
  | halt => exact sym.halt_bounded h
open _root_.P2Mf6bd8d28 renaming h291 → _P83
theorem _root_.P2Mf6bd8d28.h310 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).Bounded (_root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program bound) := by
  have hh : ∀ l : Option Λ,
      (l.elim sym (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw (program l) sym)).Bounded
        (bound + Finset.univ.sup (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliaryBound (program l) bound)) := by
    intro l
    cases l with
    | none => exact h.mono (Nat.le_add_right _ _)
    | some l =>
      exact (_P83 hw (program l) sym bound h).mono
        ((Finset.le_sup (f := fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliaryBound (program l) bound) (Finset.mem_univ l)).trans
          (Nat.le_add_left _ _))
  exact ⟨fun l => _P3q _ _ _ _ h.label (fun a => (hh a).label l),
    fun v => _P3q _ _ _ _ h.label (fun a => (hh a).state v),
    fun k i b => _P3q _ _ _ _ h.label (fun a => (hh a).stack k i b)⟩
open _root_.P2Mf6bd8d28 renaming h310 → _P8m
theorem _root_.P2Mf6bd8d28.h294 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).1.length ≤
      ticks * (_root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program 0 * Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width)) := by
  induction ticks generalizing start sym with
  | zero => simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun]
  | succ ticks ih =>
    have hf := (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).compiled_length_le start _ (_P8m hw program sym 0 h)
    have hr := ih (start + ((_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).compiled start).1.length) _
      ((_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).rebound_bounded_zero start)
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun, List.length_append]
    nlinarith
open _root_.P2Mf6bd8d28 renaming h294 → _P86
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h273 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h273 → _P7l
open _root_.P2Mf6bd8d28 renaming h274 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled_length_le
open _root_.P2Mf6bd8d28 renaming h274 → _P7m
open _root_.P2Mf6bd8d28 renaming h275 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_bounded
open _root_.P2Mf6bd8d28 renaming h275 → _P7n
open _root_.P2Mf6bd8d28 renaming h277 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_bounded
open _root_.P2Mf6bd8d28 renaming h277 → _P7p
open _root_.P2Mf6bd8d28 renaming h279 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_bounded
open _root_.P2Mf6bd8d28 renaming h279 → _P7r
open _root_.P2Mf6bd8d28 renaming h282 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_bounded
open _root_.P2Mf6bd8d28 renaming h282 → _P7u
open _root_.P2Mf6bd8d28 renaming h284 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_bounded
open _root_.P2Mf6bd8d28 renaming h284 → _P7w
open _root_.P2Mf6bd8d28 renaming h286 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_bounded
open _root_.P2Mf6bd8d28 renaming h286 → _P7y
open _root_.P2Mf6bd8d28 renaming h289 → _P81
open _root_.P2Mf6bd8d28 renaming h291 → _P83
open _root_.P2Mf6bd8d28 renaming h294 → _P86
open _root_.P2Mf6bd8d28 renaming h310 → _P8m
open _root_.P2Mf6bd8d28 renaming h909 → _Pp9
open _root_.P2Mf6bd8d28 renaming h910 → _Ppa
open _root_.P2Mf6bd8d28 renaming h911 → _Ppb
end
open _root_.P2Mf6bd8d28 renaming h273 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.Bounded.mono
open _root_.P2Mf6bd8d28 renaming h273 → _P7l
open _root_.P2Mf6bd8d28 renaming h274 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled_length_le
open _root_.P2Mf6bd8d28 renaming h274 → _P7m
open _root_.P2Mf6bd8d28 renaming h275 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.halt_bounded
open _root_.P2Mf6bd8d28 renaming h275 → _P7n
open _root_.P2Mf6bd8d28 renaming h277 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.jump_bounded
open _root_.P2Mf6bd8d28 renaming h277 → _P7p
open _root_.P2Mf6bd8d28 renaming h279 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.load_bounded
open _root_.P2Mf6bd8d28 renaming h279 → _P7r
open _root_.P2Mf6bd8d28 renaming h282 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop_bounded
open _root_.P2Mf6bd8d28 renaming h282 → _P7u
open _root_.P2Mf6bd8d28 renaming h284 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push_bounded
open _root_.P2Mf6bd8d28 renaming h284 → _P7w
open _root_.P2Mf6bd8d28 renaming h286 → InfoLossLAR.WorstCase.TM2Boolean.Symbolic.read_bounded
open _root_.P2Mf6bd8d28 renaming h286 → _P7y
open _root_.P2Mf6bd8d28 renaming h289 → _P81
open _root_.P2Mf6bd8d28 renaming h291 → _P83
open _root_.P2Mf6bd8d28 renaming h294 → _P86
open _root_.P2Mf6bd8d28 renaming h310 → _P8m
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
theorem _root_.P2Mf6bd8d28.h300 (wire : ℕ) (b : Option Bool) (bits : ℕ → Bool) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.inputCell wire b).eval bits = decide (b = some (bits wire)) := by
  cases b with
  | none => rfl
  | some b => cases b <;> cases h : bits wire <;> simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.inputCell, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, h]
open _root_.P2Mf6bd8d28 renaming h300 → _P8c
theorem _root_.P2Mf6bd8d28.h297 (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState length width).Bounded 1 := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro k i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.initial]
  split_ifs
  · cases b with
    | none => exact le_rfl
    | some b => cases b <;> simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.inputCell, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
  · exact le_rfl
open _root_.P2Mf6bd8d28 renaming h297 → _P89
theorem _root_.P2Mf6bd8d28.h298 (input : K) (main : Λ) (initialState : σ) (width : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i]) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes (_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState word.length width)
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration input main initialState word) bits := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro k i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.initial, _root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration]
  by_cases hk : k = input
  · simp only [hk, ↓reduceIte, true_and]
    by_cases hi : i.val < word.length
    · simp only [hi, ↓reduceIte, _P8c, hbits i.val hi, List.getElem?_eq_getElem hi]
    · simp only [hi, ↓reduceIte, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, List.getElem?_eq_none (by omega : word.length ≤ i.val)]
  · simp [hk, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval]
open _root_.P2Mf6bd8d28 renaming h298 → _P8a
theorem _root_.P2Mf6bd8d28.h299 (input : K) (main : Λ) (initialState : σ) (word : List Bool) :
    _root_.Integration9_9.TM2OutputLength.stackSize (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration input main initialState word).stk ≤ word.length := by
  apply Finset.sup_le
  intro k hk
  by_cases he : k = input
  · simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration, he]
  · simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration, he]
open _root_.P2Mf6bd8d28 renaming h299 → _P8b
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h297 → _P89
open _root_.P2Mf6bd8d28 renaming h298 → _P8a
open _root_.P2Mf6bd8d28 renaming h299 → _P8b
open _root_.P2Mf6bd8d28 renaming h300 → _P8c
end
open _root_.P2Mf6bd8d28 renaming h297 → _P89
open _root_.P2Mf6bd8d28 renaming h298 → _P8a
open _root_.P2Mf6bd8d28 renaming h299 → _P8b
open _root_.P2Mf6bd8d28 renaming h300 → _P8c
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
namespace CodeFamily
theorem _root_.P2Mf6bd8d28.h192 [Coding α] (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (hl : Poly length) : (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.initialCode input main initialState length).IsPoly := by
  refine ⟨fun l => _P6u _, fun v => _P6u _, ?_⟩
  intro k b
  have hc : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (fun x : α × ℕ => _root_.InfoLossLAR.WorstCase.TM2Boolean.inputCell x.2 b) := by
    cases b with
    | none => exact _P6u false
    | some b => cases b
                · exact (_P6v (show Poly (fun x : α × ℕ => x.2) by fun_prop)).negate
                · exact _P6v (by fun_prop)
  by_cases hk : k = input
  · simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.initialCode, hk, true_and]
    have hp : Poly (fun x : α × ℕ => decide (x.2 < length x.1)) := by fun_prop
    simpa only [decide_eq_true_eq] using _P6w hp hc (_P6u (decide (b=none)))
  · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.initialCode, hk, false_and, ↓reduceIte] using
      (_P6u (α := α × ℕ) (decide (b=none)))
open _root_.P2Mf6bd8d28 renaming h192 → _P5c
theorem _root_.P2Mf6bd8d28.h199 [Coding α] (width : α → ℕ) (refs : α → List ℕ)
    (hw : Poly width) (hr : Poly refs) : (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode (K := K) (Λ := Λ) (σ := σ) width refs).IsPoly := by
  constructor
  · intro l
    apply _P6v
    fun_prop
  · intro v
    apply _P6v
    fun_prop
  · intro k b
    apply _P6v
    fun_prop
open _root_.P2Mf6bd8d28 renaming h199 → _P5j
end CodeFamily
open _root_.P2Mf6bd8d28 renaming h192 → _P5c
open _root_.P2Mf6bd8d28 renaming h199 → _P5j
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h192 → _P5c
open _root_.P2Mf6bd8d28 renaming h199 → _P5j
end
open _root_.P2Mf6bd8d28 renaming h192 → _P5c
open _root_.P2Mf6bd8d28 renaming h199 → _P5j
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
theorem _root_.P2Mf6bd8d28.h257 (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) : (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code e).length ≤ 2*e.size+1 := by
  induction e with
  | input i => simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
  | constant b => cases b <;> simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
  | negate a ih => simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, List.length_append, List.length_singleton, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]; omega
  | xor a b ia ib | and a b ia ib =>
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, List.length_append, List.length_singleton, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]; omega
open _root_.P2Mf6bd8d28 renaming h257 → _P75
theorem _root_.P2Mf6bd8d28.h272 (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (N : ℕ) (h : e.Valid (2^N)) :
    ∀ t ∈ _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code e, t.2.bits.length ≤ N := by
  induction e with
  | input i =>
    intro t ht
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, List.mem_singleton] at ht
    subst t
    change i.bits.length ≤ N
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr h
  | constant b => cases b <;> simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code]
  | negate a ih =>
    intro t ht
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih h t ht
    · simp
  | xor a b ia ib | and a b ia ib =>
    intro t ht
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ia h.1 t ht
    · exact ib h.2 t ht
    · simp
open _root_.P2Mf6bd8d28 renaming h272 → _P7k
theorem _root_.P2Mf6bd8d28.h258 (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) (C : ℕ) (h : ∀ e ∈ es, e.size ≤ C) :
    (es.flatMap _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code).length ≤ (2*C+1)*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := (_P75 e).trans (show 2*e.size+1 ≤ 2*C+1 by have := h e (by simp); omega)
    have hh := ih (fun f hf => h f (by simp [hf]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith
open _root_.P2Mf6bd8d28 renaming h258 → _P76
theorem _root_.P2Mf6bd8d28.h266 {N : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N (s.1, s.2.1.reverse, s.2.2) := by
  refine ⟨h.slots, ?_, h.nodes, ?_, h.code⟩
  · simpa only [List.length_reverse] using h.operands
  · intro x hx
    exact h.refs x (List.mem_reverse.mp hx)
open _root_.P2Mf6bd8d28 renaming h266 → _P7e
theorem _root_.P2Mf6bd8d28.h256 {N : ℕ} {s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N s) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N (s.1, [], s.2.2) := ⟨h.slots, Nat.zero_le _, h.nodes, by simp, h.code⟩
open _root_.P2Mf6bd8d28 renaming h256 → _P74
end InfoLossLAR.WorstCase.TM2Boolean.RPN
open _root_.P2Mf6bd8d28 renaming h256 → _P74
open _root_.P2Mf6bd8d28 renaming h257 → _P75
open _root_.P2Mf6bd8d28 renaming h258 → _P76
open _root_.P2Mf6bd8d28 renaming h266 → _P7e
open _root_.P2Mf6bd8d28 renaming h272 → _P7k
end
open _root_.P2Mf6bd8d28 renaming h256 → _P74
open _root_.P2Mf6bd8d28 renaming h257 → _P75
open _root_.P2Mf6bd8d28 renaming h258 → _P76
open _root_.P2Mf6bd8d28 renaming h266 → _P7e
open _root_.P2Mf6bd8d28 renaming h272 → _P7k
namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
theorem _root_.P2Mf6bd8d28.h210 : (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers (K := K) (Λ := Λ) (σ := σ)).IsPoly :=
  _P5j _ _ (by fun_prop) (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h210 → _P5u
theorem _root_.P2Mf6bd8d28.h209 (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) :
    ((_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Bounded 0 := by
  exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩
open _root_.P2Mf6bd8d28 renaming h209 → _P5t
theorem _root_.P2Mf6bd8d28.h211 (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ((_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Valid (2^N) := by
  have hb : ∀ i : ℕ, ((x.2.2.1[i]?).getD 0) < 2^N := by
    intro i
    have hi := _P7b x.2.2.1 i N h
    rw [Nat.size_eq_bits_len] at hi
    exact Nat.size_le.mp hi
  exact ⟨fun _ => hb _, fun _ => hb _, fun _ _ _ => hb _⟩
open _root_.P2Mf6bd8d28 renaming h211 → _P5v
@[fun_prop] theorem _root_.P2Mf6bd8d28.h217 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens program) :=
  _P59 _ (_P5l _ (by fun_prop) program _ _P5u) _ (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h217 → _P61
@[fun_prop] theorem _root_.P2Mf6bd8d28.h213 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step
  fun_prop
open _root_.P2Mf6bd8d28 renaming h213 → _P5x
theorem _root_.P2Mf6bd8d28.h216 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input)
    (hw : 0 < x.1.length) : (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens program x).length ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound program x.1.length := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens_eq program x hw]
  have hb := _P8m hw program _ 0 (_P5t (K := K) (Λ := Λ) (σ := σ) x)
  have hh := _P76 (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers.restrict x x.1.length)).formulas
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program 0) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      rcases (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ x.1.length).symm i with l | v | ⟨k,i,b⟩
      · exact hb.label l
      · exact hb.state v
      · exact hb.stack k i b)
  simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas_length, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound] using hh
open _root_.P2Mf6bd8d28 renaming h216 → _P60
theorem _root_.P2Mf6bd8d28.h215 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input)
    (hw : 0 < x.1.length) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ∀ t ∈ _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens program x, t.2.bits.length ≤ N := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens_eq program x hw]
  have hv := _root_.InfoLossLAR.WorstCase.TM2Boolean.transition_valid hw program _ (_P5v (K := K) (Λ := Λ) (σ := σ) x N h)
  intro t ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  exact _P7k e N ((_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers.restrict x x.1.length)).formulas_valid hv e he) t ht
open _root_.P2Mf6bd8d28 renaming h215 → _P5z
theorem _root_.P2Mf6bd8d28.h212 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input)
    (N : ℕ) (hN : 3 ≤ N) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N x.2) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded (N+_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound program x.1.length) (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program x).2 := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step
  split
  · exact h.mono (Nat.le_add_right _ _)
  · rename_i hw
    have hw' : 0 < x.1.length := by
      have hx : x.1 ≠ [] := by simpa only [List.isEmpty_iff] using hw
      exact List.length_pos_iff.mpr hx
    have hb := _P7f (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens program x) (_P74 h) hN (_P5z program x hw' N h.refs)
    exact (_P7e hb).mono (Nat.add_le_add_left (_P60 program x hw') N)
open _root_.P2Mf6bd8d28 renaming h212 → _P5w
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open _root_.P2Mf6bd8d28 renaming h209 → _P5t
open _root_.P2Mf6bd8d28 renaming h210 → _P5u
open _root_.P2Mf6bd8d28 renaming h211 → _P5v
open _root_.P2Mf6bd8d28 renaming h212 → _P5w
open _root_.P2Mf6bd8d28 renaming h213 → _P5x
open _root_.P2Mf6bd8d28 renaming h215 → _P5z
open _root_.P2Mf6bd8d28 renaming h216 → _P60
open _root_.P2Mf6bd8d28 renaming h217 → _P61
end
open _root_.P2Mf6bd8d28 renaming h209 → _P5t
open _root_.P2Mf6bd8d28 renaming h210 → _P5u
open _root_.P2Mf6bd8d28 renaming h211 → _P5v
open _root_.P2Mf6bd8d28 renaming h212 → _P5w
open _root_.P2Mf6bd8d28 renaming h213 → _P5x
open _root_.P2Mf6bd8d28 renaming h215 → _P5z
open _root_.P2Mf6bd8d28 renaming h216 → _P60
open _root_.P2Mf6bd8d28 renaming h217 → _P61
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
theorem _root_.P2Mf6bd8d28.h206 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit)
    (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) (N : ℕ) (hN : 3 ≤ N) (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded N x.2) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Bounded (N+fuel.length*_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound program x.1.length) (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program fuel x).2 := by
  induction fuel generalizing x N with
  | nil => simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode, List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero] using h
  | cons u fuel ih =>
    have hs := _P5w program x N hN h
    have hh := ih (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program x) (N+_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound program x.1.length) (by omega) hs
    simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode, List.foldl_cons, List.length_cons, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step_width, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
open _root_.P2Mf6bd8d28 renaming h206 → _P5q
theorem _root_.P2Mf6bd8d28.h214 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound program width ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenRate program*(width+1) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenRate
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.slot_count]
  have h : Fintype.card Λ+1+Fintype.card σ+Fintype.card K*width*3 ≤
      (Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)*(width+1) := by nlinarith
  have hh := Nat.mul_le_mul_left (2*_root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program 0+1) h
  simpa only [Nat.mul_assoc] using hh
open _root_.P2Mf6bd8d28 renaming h214 → _P5y
theorem _root_.P2Mf6bd8d28.h207 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) (pre suf : List Unit) (he : fuel=pre++suf) :
    (enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program pre x)).length ≤ (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.loopBound program).eval (enc (fuel,x)).length := by
  let L := (enc (fuel,x)).length
  have heL : L = 2*fuel.length+1+2*x.1.length+1+(enc x.2).length := by
    change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) (fuel,x)).length = _
    simp only [encodePair_length, _P79]
    omega
  have hw : x.1.length ≤ L := by omega
  have hp : pre.length ≤ L := by have hh := congrArg List.length he; simp only [List.length_append] at hh; omega
  have hs := (_P73 x.2).mono (show (enc x.2).length ≤ L+3 by omega)
  have hb := _P5q program pre x (L+3) (by omega) hs
  have ht := (_P5y program x.1.length).trans
    (Nat.mul_le_mul_left (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenRate program) (Nat.add_le_add_right hw 1))
  have hm : pre.length * _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenBound program x.1.length ≤ L*_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenRate program*(L+1) := by
    exact (Nat.mul_le_mul hp ht).trans_eq (Nat.mul_assoc _ _ _).symm
  have hb' := hb.mono (Nat.add_le_add_left hm (L+3))
  have hh := _P7a hb'
  have hwidth := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode_width program pre x
  have henc : (enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program pre x)).length = 2*x.1.length+1+(enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program pre x).2).length := by
    change (encodePair (enc : List Unit → List Bool) enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program pre x)).length = _
    rw [encodePair_length, _P79, hwidth]
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.loopBound, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_pow, eval_C]
  change _ ≤ 2*L+1+20*(L+3+L*_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenRate program*(L+1)+1)^2
  omega
open _root_.P2Mf6bd8d28 renaming h207 → _P5r
@[fun_prop] theorem _root_.P2Mf6bd8d28.h208 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Poly (fun x : List Unit × _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input => _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program x.1 x.2) := by
  have hs : Poly (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input × Unit => _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program x.1) := by fun_prop
  apply Automatic.Poly.of_program
  exact hs.program.listFold () (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.loopBound program) (by
    intro fuel x pre suf he
    change (enc (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program pre x)).length ≤ (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.loopBound program).eval (enc (fuel,x)).length
    exact _P5r program fuel x pre suf he)
open _root_.P2Mf6bd8d28 renaming h208 → _P5s
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open _root_.P2Mf6bd8d28 renaming h206 → _P5q
open _root_.P2Mf6bd8d28 renaming h207 → _P5r
open _root_.P2Mf6bd8d28 renaming h208 → _P5s
open _root_.P2Mf6bd8d28 renaming h214 → _P5y
end
open _root_.P2Mf6bd8d28 renaming h206 → _P5q
open _root_.P2Mf6bd8d28 renaming h207 → _P5r
open _root_.P2Mf6bd8d28 renaming h208 → _P5s
open _root_.P2Mf6bd8d28 renaming h214 → _P5y
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}
theorem _root_.P2Mf6bd8d28.h218 {sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width} {cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ}
    {bits : ℕ → Bool} (h : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes sym cfg bits) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) :
    (sym.get i).eval bits = _root_.InfoLossLAR.WorstCase.TM2Boolean.configurationBit cfg i := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b
open _root_.P2Mf6bd8d28 renaming h218 → InfoLossLAR.WorstCase.TM2Boolean.Encodes.get
open _root_.P2Mf6bd8d28 renaming h218 → _P62
theorem _root_.P2Mf6bd8d28.h295 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).2.Bounded 0 := by
  induction ticks generalizing start sym with
  | zero => exact h
  | succ ticks ih => exact ih _ _ ((_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).rebound_bounded_zero start)
open _root_.P2Mf6bd8d28 renaming h295 → _P87
theorem _root_.P2Mf6bd8d28.h302 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks length).ops.length ≤
      (1 + ticks * _root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program 0) * Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) := by
  let init := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState length width
  have hi : init.Bounded 1 := _P89 input main initialState length width
  have hp := init.compiled_length_le length 1 hi
  have hm := _P86 hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  have hz := _P87 hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  let middle := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks (length + (init.compiled length).1.length) (init.rebound length)
  have he := middle.2.compiled_length_le
    (length + (init.compiled length).1.length + middle.1.length) 0 hz
  change ((init.compiled length).1 ++ middle.1 ++
    (middle.2.compiled (length + (init.compiled length).1.length + middle.1.length)).1).length ≤ _
  simp only [List.length_append]
  nlinarith
open _root_.P2Mf6bd8d28 renaming h302 → _P8e
theorem _root_.P2Mf6bd8d28.h303 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i])
    (hsize : word.length + _root_.Integration9_9.TM2OutputLength.programPushBound program * ticks ≤ width) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks word.length).ops bits
      ((_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks word.length).output i) =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.configurationBit ((_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program)^[ticks] (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration input main initialState word)) i := by
  let init := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState word.length width
  have hi : init.Valid word.length := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial_valid input main initialState word.length width
  have he : _root_.InfoLossLAR.WorstCase.TM2Boolean.Encodes init (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration input main initialState word) bits :=
    _P8a input main initialState width word bits hbits
  have hp := init.rebound_encodes word.length hi _ bits he
  have hr := _P85 hw program ticks _ _ _ _
    (init.rebound_valid word.length hi) hp
    ((Nat.add_le_add_right (_P8b input main initialState word) _).trans hsize)
  have hv := (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun_valid hw program ticks _ _ (init.rebound_valid word.length hi)).2
  let middle := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks (word.length + (init.compiled word.length).1.length)
    (init.rebound word.length)
  have ho := middle.2.output_eval _ hv
    (_root_.InfoLossLAR.WorstCase.BooleanProgram.run (word.length + (init.compiled word.length).1.length) middle.1
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length (init.compiled word.length).1 bits)) i
  rw [hr.get i] at ho
  simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram, _P46, List.length_append, Nat.add_assoc, init, middle] using ho
open _root_.P2Mf6bd8d28 renaming h303 → _P8f
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h218 → InfoLossLAR.WorstCase.TM2Boolean.Encodes.get
open _root_.P2Mf6bd8d28 renaming h218 → _P62
open _root_.P2Mf6bd8d28 renaming h295 → _P87
open _root_.P2Mf6bd8d28 renaming h302 → _P8e
open _root_.P2Mf6bd8d28 renaming h303 → _P8f
end
open _root_.P2Mf6bd8d28 renaming h218 → InfoLossLAR.WorstCase.TM2Boolean.Encodes.get
open _root_.P2Mf6bd8d28 renaming h218 → _P62
open _root_.P2Mf6bd8d28 renaming h295 → _P87
open _root_.P2Mf6bd8d28 renaming h302 → _P8e
open _root_.P2Mf6bd8d28 renaming h303 → _P8f
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
@[fun_prop] theorem _root_.P2Mf6bd8d28.h205 (input : K) (main : Λ) (initialState : σ) :
    Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult input main initialState) :=
  _P5a _ (_P5c _ _ _ _ (by fun_prop)) _ _ (by fun_prop) (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h205 → _P5p
@[fun_prop] theorem _root_.P2Mf6bd8d28.h204 (input : K) (main : Λ) (initialState : σ) :
    Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput
  fun_prop
open _root_.P2Mf6bd8d28 renaming h204 → _P5o
@[fun_prop] theorem _root_.P2Mf6bd8d28.h203 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) : Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate
  fun_prop
open _root_.P2Mf6bd8d28 renaming h203 → _P5n
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open _root_.P2Mf6bd8d28 renaming h203 → _P5n
open _root_.P2Mf6bd8d28 renaming h204 → _P5o
open _root_.P2Mf6bd8d28 renaming h205 → _P5p
end
open _root_.P2Mf6bd8d28 renaming h203 → _P5n
open _root_.P2Mf6bd8d28 renaming h204 → _P5o
open _root_.P2Mf6bd8d28 renaming h205 → _P5p
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h254 : Poly (fun x : List Unit × ℕ => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.boundedNat x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.boundedNat
  fun_prop
open _root_.P2Mf6bd8d28 renaming h254 → _P72
@[fun_prop] theorem _root_.P2Mf6bd8d28.h264 :
    Poly (fun x : List Unit × (ℕ × _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWord x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWord
  fun_prop
open _root_.P2Mf6bd8d28 renaming h264 → _P7c
@[fun_prop] theorem _root_.P2Mf6bd8d28.h265 :
    Poly (fun x : List Unit × (ℕ × List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWords x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWords
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node => List.range xs.length)
      (g := fun x : List Unit × (ℕ × List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) => x.2.2) Automatic.Poly.list_indices (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h265 → _P7d
end InfoLossLAR.WorstCase.TM2Boolean.RPN
open _root_.P2Mf6bd8d28 renaming h254 → _P72
open _root_.P2Mf6bd8d28 renaming h264 → _P7c
open _root_.P2Mf6bd8d28 renaming h265 → _P7d
end
open _root_.P2Mf6bd8d28 renaming h254 → _P72
open _root_.P2Mf6bd8d28 renaming h264 → _P7c
open _root_.P2Mf6bd8d28 renaming h265 → _P7d
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
private theorem _root_.P2Mf6bd8d28.h873 {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    _root_.InfoLossLAR.WorstCase.leftRegister (Function.update state (Fin.castAdd m wire) bit)=Function.update (_root_.InfoLossLAR.WorstCase.leftRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [_root_.InfoLossLAR.WorstCase.leftRegister]
  · have he : Fin.castAdd m index ≠ Fin.castAdd m wire := fun hh => h (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) hh))
    simp [_root_.InfoLossLAR.WorstCase.leftRegister,Function.update_of_ne h,Function.update_of_ne he]
open _root_.P2Mf6bd8d28 renaming h873 → _Po9
private theorem _root_.P2Mf6bd8d28.h877 {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    _root_.InfoLossLAR.WorstCase.rightRegister (Function.update state (Fin.castAdd m wire) bit)=_root_.InfoLossLAR.WorstCase.rightRegister state := by
  funext index
  have he : Fin.natAdd n index ≠ Fin.castAdd m wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := wire.isLt
    omega
  simp [_root_.InfoLossLAR.WorstCase.rightRegister,Function.update_of_ne he]
open _root_.P2Mf6bd8d28 renaming h877 → _Pod
private theorem _root_.P2Mf6bd8d28.h874 {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    _root_.InfoLossLAR.WorstCase.leftRegister (Function.update state (Fin.natAdd n wire) bit)=_root_.InfoLossLAR.WorstCase.leftRegister state := by
  funext index
  have he : Fin.castAdd m index ≠ Fin.natAdd n wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := index.isLt
    omega
  simp [_root_.InfoLossLAR.WorstCase.leftRegister,Function.update_of_ne he]
open _root_.P2Mf6bd8d28 renaming h874 → _Poa
private theorem _root_.P2Mf6bd8d28.h878 {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    _root_.InfoLossLAR.WorstCase.rightRegister (Function.update state (Fin.natAdd n wire) bit)=Function.update (_root_.InfoLossLAR.WorstCase.rightRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [_root_.InfoLossLAR.WorstCase.rightRegister]
  · have he : Fin.natAdd n index ≠ Fin.natAdd n wire := by
      intro hh
      exact h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val hh)))
    simp [_root_.InfoLossLAR.WorstCase.rightRegister,Function.update_of_ne h,Function.update_of_ne he]
open _root_.P2Mf6bd8d28 renaming h878 → _Poe
private theorem _root_.P2Mf6bd8d28.h870 {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin n)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.castAdd m wire) (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState (apply1 matrix wire first) second := by
  funext state
  simp only [apply1,_root_.InfoLossLAR.WorstCase.tensorState,_Po9,_Pod]
  change (∑ bit,matrix (_root_.InfoLossLAR.WorstCase.leftRegister state wire) bit*
    (first (Function.update (_root_.InfoLossLAR.WorstCase.leftRegister state) wire bit)*second (_root_.InfoLossLAR.WorstCase.rightRegister state))) =
      (∑ bit,matrix (_root_.InfoLossLAR.WorstCase.leftRegister state wire) bit*first (Function.update (_root_.InfoLossLAR.WorstCase.leftRegister state) wire bit))*
        second (_root_.InfoLossLAR.WorstCase.rightRegister state)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bit _
  ring
open _root_.P2Mf6bd8d28 renaming h870 → _Po6
private theorem _root_.P2Mf6bd8d28.h871 {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin m)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.natAdd n wire) (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState first (apply1 matrix wire second) := by
  funext state
  simp only [apply1,_root_.InfoLossLAR.WorstCase.tensorState,_Poa,_Poe]
  change (∑ bit,matrix (_root_.InfoLossLAR.WorstCase.rightRegister state wire) bit*
    (first (_root_.InfoLossLAR.WorstCase.leftRegister state)*second (Function.update (_root_.InfoLossLAR.WorstCase.rightRegister state) wire bit))) =
      first (_root_.InfoLossLAR.WorstCase.leftRegister state)*
        (∑ bit,matrix (_root_.InfoLossLAR.WorstCase.rightRegister state wire) bit*second (Function.update (_root_.InfoLossLAR.WorstCase.rightRegister state) wire bit))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  ring
open _root_.P2Mf6bd8d28 renaming h871 → _Po7
theorem _root_.P2Mf6bd8d28.h460 {n m : ℕ} (gate : Instr n) (first : QState n) (second : QState m) :
    (_root_.InfoLossLAR.WorstCase.leftInstruction gate).apply (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState (gate.apply first) second := by
  cases gate with
  | h wire => exact _Po6 hMat wire first second
  | s wire => exact _Po6 sMat wire first second
  | t wire => exact _Po6 tMat wire first second
  | x wire => exact _Po6 xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [_root_.InfoLossLAR.WorstCase.leftInstruction,Instr.apply,cnotState,_root_.InfoLossLAR.WorstCase.tensorState,_Po9,_Pod]
    rfl
open _root_.P2Mf6bd8d28 renaming h460 → _Pcs
theorem _root_.P2Mf6bd8d28.h554 {n m : ℕ} (gate : Instr m) (first : QState n) (second : QState m) :
    (_root_.InfoLossLAR.WorstCase.rightInstruction gate).apply (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState first (gate.apply second) := by
  cases gate with
  | h wire => exact _Po7 hMat wire first second
  | s wire => exact _Po7 sMat wire first second
  | t wire => exact _Po7 tMat wire first second
  | x wire => exact _Po7 xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [_root_.InfoLossLAR.WorstCase.rightInstruction,Instr.apply,cnotState,_root_.InfoLossLAR.WorstCase.tensorState,_Poa,_Poe]
    rfl
open _root_.P2Mf6bd8d28 renaming h554 → _Pfe
private theorem _root_.P2Mf6bd8d28.h872 {n m : ℕ} (layer : List (Instr n)) (first : QState n) (second : QState m) :
    runLayer (layer.map _root_.InfoLossLAR.WorstCase.leftInstruction) (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState (runLayer layer first) second := by
  induction layer generalizing first with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [_Pcs]
    exact ih (gate.apply first)
open _root_.P2Mf6bd8d28 renaming h872 → _Po8
private theorem _root_.P2Mf6bd8d28.h876 {n m : ℕ} (layer : List (Instr m)) (first : QState n) (second : QState m) :
    runLayer (layer.map _root_.InfoLossLAR.WorstCase.rightInstruction) (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState first (runLayer layer second) := by
  induction layer generalizing second with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [_Pfe]
    exact ih (gate.apply second)
open _root_.P2Mf6bd8d28 renaming h876 → _Poc
theorem _root_.P2Mf6bd8d28.h458 {n m : ℕ} (circuit : Layered n) (first : QState n) (second : QState m) :
    runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit circuit) (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState (runLayered circuit first) second := by
  induction circuit generalizing first with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [_root_.InfoLossLAR.WorstCase.leftCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [_Po8]
    exact ih (runLayer layer first)
open _root_.P2Mf6bd8d28 renaming h458 → _Pcq
theorem _root_.P2Mf6bd8d28.h552 {n m : ℕ} (circuit : Layered m) (first : QState n) (second : QState m) :
    runLayered (_root_.InfoLossLAR.WorstCase.rightCircuit circuit) (_root_.InfoLossLAR.WorstCase.tensorState first second)=_root_.InfoLossLAR.WorstCase.tensorState first (runLayered circuit second) := by
  induction circuit generalizing second with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [_root_.InfoLossLAR.WorstCase.rightCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [_Poc]
    exact ih (runLayer layer second)
open _root_.P2Mf6bd8d28 renaming h552 → _Pfc
theorem _root_.P2Mf6bd8d28.h414 {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) :
    runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit left++_root_.InfoLossLAR.WorstCase.rightCircuit right) (_root_.InfoLossLAR.WorstCase.tensorState first second)=
      _root_.InfoLossLAR.WorstCase.tensorState (runLayered left first) (runLayered right second) := by
  rw [runLayered,List.foldl_append]
  change runLayered (_root_.InfoLossLAR.WorstCase.rightCircuit right) (runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit left) (_root_.InfoLossLAR.WorstCase.tensorState first second)) = _
  rw [_Pcq,_Pfc]
open _root_.P2Mf6bd8d28 renaming h414 → _Pbi
theorem _root_.P2Mf6bd8d28.h574 {n m : ℕ} (test : Bits n → Bits m → ℝ) :
    (∑ state : Bits (n+m),test (_root_.InfoLossLAR.WorstCase.leftRegister state) (_root_.InfoLossLAR.WorstCase.rightRegister state))=
      ∑ first : Bits n,∑ second : Bits m,test first second := by
  have h := (_root_.Integration9_9.FairBitPadding.splitEquiv n m).sum_comp
    (fun pair : Bits n × Bits m => test pair.1 pair.2)
  change (∑ state : Bits (n+m),test (_root_.InfoLossLAR.WorstCase.leftRegister state) (_root_.InfoLossLAR.WorstCase.rightRegister state))=
    ∑ pair : Bits n × Bits m,test pair.1 pair.2 at h
  simpa only [Fintype.sum_prod_type] using h
open _root_.P2Mf6bd8d28 renaming h574 → _Pfy
theorem _root_.P2Mf6bd8d28.h577 {n m : ℕ} (first : QState n) (second : QState m) :
    (∑ state,‖_root_.InfoLossLAR.WorstCase.tensorState first second state‖^2)=
      (∑ state,‖first state‖^2)*(∑ state,‖second state‖^2) := by
  unfold _root_.InfoLossLAR.WorstCase.tensorState
  rw [_Pfy (fun left right => ‖first left*second right‖^2)]
  simp only [norm_mul,mul_pow,←Finset.mul_sum,←Finset.sum_mul]
open _root_.P2Mf6bd8d28 renaming h577 → _Pg1
theorem _root_.P2Mf6bd8d28.h576 {n m : ℕ} (first : QState n) (second : QState m) (out : Fin n)
    (hsecond : ∑ state,‖second state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.castAdd m out) then ‖_root_.InfoLossLAR.WorstCase.tensorState first second state‖^2 else 0)=
      ∑ state : Bits n,if state out then ‖first state‖^2 else 0 := by
  change (∑ state : Bits (n+m),if _root_.InfoLossLAR.WorstCase.leftRegister state out then
    ‖first (_root_.InfoLossLAR.WorstCase.leftRegister state)*second (_root_.InfoLossLAR.WorstCase.rightRegister state)‖^2 else 0)=_
  rw [_Pfy (fun left right => if left out then ‖first left*second right‖^2 else 0)]
  have hpoint (left : Bits n) (right : Bits m) :
      (if left out then ‖first left*second right‖^2 else 0)=
        (if left out then ‖first left‖^2 else 0)*‖second right‖^2 := by
    cases left out <;> simp [norm_mul,mul_pow]
  simp only [hpoint,←Finset.mul_sum,hsecond,mul_one]
open _root_.P2Mf6bd8d28 renaming h576 → _Pg0
private theorem _root_.P2Mf6bd8d28.h875 {n m : ℕ} (first second : Instr n)
    (h : Disjoint first.support second.support) :
    Disjoint (_root_.InfoLossLAR.WorstCase.leftInstruction (m := m) first).support (_root_.InfoLossLAR.WorstCase.leftInstruction second).support := by
  rw [_root_.InfoLossLAR.WorstCase.leftInstruction_support,_root_.InfoLossLAR.WorstCase.leftInstruction_support]
  apply Finset.disjoint_left.mpr
  intro index hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b=a := Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he)
  subst b
  exact Finset.disjoint_left.mp h ha hb
open _root_.P2Mf6bd8d28 renaming h875 → _Pob
private theorem _root_.P2Mf6bd8d28.h879 {n m : ℕ} (first second : Instr m)
    (h : Disjoint first.support second.support) :
    Disjoint (_root_.InfoLossLAR.WorstCase.rightInstruction (n := n) first).support (_root_.InfoLossLAR.WorstCase.rightInstruction second).support := by
  rw [_root_.InfoLossLAR.WorstCase.rightInstruction_support,_root_.InfoLossLAR.WorstCase.rightInstruction_support]
  apply Finset.disjoint_left.mpr
  intro index hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b=a := Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))
  subst b
  exact Finset.disjoint_left.mp h ha hb
open _root_.P2Mf6bd8d28 renaming h879 → _Pof
theorem _root_.P2Mf6bd8d28.h461 {n m : ℕ} (layer : List (Instr n)) (h : LayerOk layer) :
    LayerOk (layer.map (_root_.InfoLossLAR.WorstCase.leftInstruction (m := m))) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hab => _Pob _ _ hab)
open _root_.P2Mf6bd8d28 renaming h461 → _Pct
theorem _root_.P2Mf6bd8d28.h555 {n m : ℕ} (layer : List (Instr m)) (h : LayerOk layer) :
    LayerOk (layer.map (_root_.InfoLossLAR.WorstCase.rightInstruction (n := n))) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hab => _Pof _ _ hab)
open _root_.P2Mf6bd8d28 renaming h555 → _Pff
theorem _root_.P2Mf6bd8d28.h459 {n m : ℕ} (circuit : Layered n)
    (h : ∀ layer ∈ circuit,LayerOk layer) : ∀ layer ∈ _root_.InfoLossLAR.WorstCase.leftCircuit (m := m) circuit,LayerOk layer := by
  intro layer hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hl
  exact _Pct original (h original ho)
open _root_.P2Mf6bd8d28 renaming h459 → _Pcr
theorem _root_.P2Mf6bd8d28.h553 {n m : ℕ} (circuit : Layered m)
    (h : ∀ layer ∈ circuit,LayerOk layer) : ∀ layer ∈ _root_.InfoLossLAR.WorstCase.rightCircuit (n := n) circuit,LayerOk layer := by
  intro layer hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hl
  exact _Pff original (h original ho)
open _root_.P2Mf6bd8d28 renaming h553 → _Pfd
theorem _root_.P2Mf6bd8d28.h578 {n m : ℕ} (first : QState n) (second : QState m) (out : Fin m)
    (hfirst : ∑ state,‖first state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.natAdd n out) then ‖_root_.InfoLossLAR.WorstCase.tensorState first second state‖^2 else 0)=
      ∑ state : Bits m,if state out then ‖second state‖^2 else 0 := by
  change (∑ state : Bits (n+m),if _root_.InfoLossLAR.WorstCase.rightRegister state out then
    ‖first (_root_.InfoLossLAR.WorstCase.leftRegister state)*second (_root_.InfoLossLAR.WorstCase.rightRegister state)‖^2 else 0)=_
  rw [_Pfy (fun left right => if right out then ‖first left*second right‖^2 else 0)]
  have hpoint (left : Bits n) (right : Bits m) :
      (if right out then ‖first left*second right‖^2 else 0)=
        ‖first left‖^2*(if right out then ‖second right‖^2 else 0) := by
    cases right out <;> simp [norm_mul,mul_pow]
  simp only [hpoint,←Finset.mul_sum,←Finset.sum_mul,hfirst,one_mul]
open _root_.P2Mf6bd8d28 renaming h578 → _Pg2
theorem _root_.P2Mf6bd8d28.h412 {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) (out : Fin n)
    (hsecond : ∑ state,‖second state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.castAdd m out) then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit left++_root_.InfoLossLAR.WorstCase.rightCircuit right) (_root_.InfoLossLAR.WorstCase.tensorState first second) state‖^2 else 0)=
      ∑ state : Bits n,if state out then ‖runLayered left first state‖^2 else 0 := by
  rw [_Pbi]
  apply _Pg0
  have hnorm : (∑ state,‖runLayered right second state‖^2)=∑ state,‖second state‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using _root_.InfoLossLAR.WorstCase.runLayered_mass right second
  exact hnorm.trans hsecond
open _root_.P2Mf6bd8d28 renaming h412 → _Pbg
theorem _root_.P2Mf6bd8d28.h413 {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) (out : Fin m)
    (hfirst : ∑ state,‖first state‖^2=1) :
    (∑ state : Bits (n+m),if state (Fin.natAdd n out) then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit left++_root_.InfoLossLAR.WorstCase.rightCircuit right) (_root_.InfoLossLAR.WorstCase.tensorState first second) state‖^2 else 0)=
      ∑ state : Bits m,if state out then ‖runLayered right second state‖^2 else 0 := by
  rw [_Pbi]
  apply _Pg2
  have hnorm : (∑ state,‖runLayered left first state‖^2)=∑ state,‖first state‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using _root_.InfoLossLAR.WorstCase.runLayered_mass left first
  exact hnorm.trans hfirst
open _root_.P2Mf6bd8d28 renaming h413 → _Pbh
theorem _root_.P2Mf6bd8d28.h550 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n))
    (state : QState n) (event : Bits n → Bool) :
    (∑ output : Bits n,if event output then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible gates) state output‖^2 else 0)=
      ∑ input : Bits n,if event (_root_.InfoLossLAR.WorstCase.reversibleAction gates input) then ‖state input‖^2 else 0 := by
  rw [_Pat]
  have h := (_root_.InfoLossLAR.WorstCase.reversibleAction gates).sum_comp (fun output : Bits n =>
    if event output then ‖state ((_root_.InfoLossLAR.WorstCase.reversibleAction gates).symm output)‖^2 else 0)
  simpa only [Equiv.symm_apply_apply] using h.symm
open _root_.P2Mf6bd8d28 renaming h550 → _Pfa
theorem _root_.P2Mf6bd8d28.h347 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n))
    (hf : _root_.InfoLossLAR.WorstCase.BooleanFresh gates) (state : QState n)
    (hz : ∀ input,state input ≠ 0 → ∀ gate ∈ gates,input gate.target=false)
    (event : Bits n → Bool) :
    (∑ output : Bits n,if event output then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)) state output‖^2 else 0)=
      ∑ input : Bits n,if event (_root_.InfoLossLAR.WorstCase.booleanRun gates input) then ‖state input‖^2 else 0 := by
  rw [_Pfa]
  apply Finset.sum_congr rfl
  intro input _
  by_cases he : state input=0
  · simp [he]
  · rw [_P9o gates hf input (hz input he)]
open _root_.P2Mf6bd8d28 renaming h347 → _P9n
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h347 → _P9n
open _root_.P2Mf6bd8d28 renaming h412 → _Pbg
open _root_.P2Mf6bd8d28 renaming h413 → _Pbh
open _root_.P2Mf6bd8d28 renaming h414 → _Pbi
open _root_.P2Mf6bd8d28 renaming h458 → _Pcq
open _root_.P2Mf6bd8d28 renaming h459 → _Pcr
open _root_.P2Mf6bd8d28 renaming h460 → _Pcs
open _root_.P2Mf6bd8d28 renaming h461 → _Pct
open _root_.P2Mf6bd8d28 renaming h550 → _Pfa
open _root_.P2Mf6bd8d28 renaming h552 → _Pfc
open _root_.P2Mf6bd8d28 renaming h553 → _Pfd
open _root_.P2Mf6bd8d28 renaming h554 → _Pfe
open _root_.P2Mf6bd8d28 renaming h555 → _Pff
open _root_.P2Mf6bd8d28 renaming h574 → _Pfy
open _root_.P2Mf6bd8d28 renaming h576 → _Pg0
open _root_.P2Mf6bd8d28 renaming h577 → _Pg1
open _root_.P2Mf6bd8d28 renaming h578 → _Pg2
open _root_.P2Mf6bd8d28 renaming h870 → _Po6
open _root_.P2Mf6bd8d28 renaming h871 → _Po7
open _root_.P2Mf6bd8d28 renaming h872 → _Po8
open _root_.P2Mf6bd8d28 renaming h873 → _Po9
open _root_.P2Mf6bd8d28 renaming h874 → _Poa
open _root_.P2Mf6bd8d28 renaming h875 → _Pob
open _root_.P2Mf6bd8d28 renaming h876 → _Poc
open _root_.P2Mf6bd8d28 renaming h877 → _Pod
open _root_.P2Mf6bd8d28 renaming h878 → _Poe
open _root_.P2Mf6bd8d28 renaming h879 → _Pof
end
open _root_.P2Mf6bd8d28 renaming h347 → _P9n
open _root_.P2Mf6bd8d28 renaming h412 → _Pbg
open _root_.P2Mf6bd8d28 renaming h413 → _Pbh
open _root_.P2Mf6bd8d28 renaming h414 → _Pbi
open _root_.P2Mf6bd8d28 renaming h458 → _Pcq
open _root_.P2Mf6bd8d28 renaming h459 → _Pcr
open _root_.P2Mf6bd8d28 renaming h460 → _Pcs
open _root_.P2Mf6bd8d28 renaming h461 → _Pct
open _root_.P2Mf6bd8d28 renaming h550 → _Pfa
open _root_.P2Mf6bd8d28 renaming h552 → _Pfc
open _root_.P2Mf6bd8d28 renaming h553 → _Pfd
open _root_.P2Mf6bd8d28 renaming h554 → _Pfe
open _root_.P2Mf6bd8d28 renaming h555 → _Pff
open _root_.P2Mf6bd8d28 renaming h574 → _Pfy
open _root_.P2Mf6bd8d28 renaming h576 → _Pg0
open _root_.P2Mf6bd8d28 renaming h577 → _Pg1
open _root_.P2Mf6bd8d28 renaming h578 → _Pg2
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h374 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock) : (∑ state,‖_root_.InfoLossLAR.WorstCase.bundleState blocks state‖^2)=(1 : ℝ) := by
  induction blocks with
  | nil => simp [_root_.InfoLossLAR.WorstCase.bundleState,_root_.InfoLossLAR.WorstCase.bundleWidth]
  | cons block blocks ih =>
    change (∑ state,‖_root_.InfoLossLAR.WorstCase.tensorState block.input (_root_.InfoLossLAR.WorstCase.bundleState blocks) state‖^2)=1
    rw [_Pg1,block.normalized,ih,one_mul]
open _root_.P2Mf6bd8d28 renaming h374 → _Pae
theorem _root_.P2Mf6bd8d28.h376 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock) (index : Fin blocks.length) :
    (∑ state : Bits (_root_.InfoLossLAR.WorstCase.bundleWidth blocks),if state (_root_.InfoLossLAR.WorstCase.bundleOutput blocks index) then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks) (_root_.InfoLossLAR.WorstCase.bundleState blocks) state‖^2 else 0)=
      (blocks.get index).probability := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block blocks ih =>
    refine Fin.cases ?_ (fun tail => ?_) index
    · change (∑ state : Bits (block.wires+_root_.InfoLossLAR.WorstCase.bundleWidth blocks),if state (Fin.castAdd (_root_.InfoLossLAR.WorstCase.bundleWidth blocks) block.out) then
        ‖runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit block.circuit++_root_.InfoLossLAR.WorstCase.rightCircuit (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks))
          (_root_.InfoLossLAR.WorstCase.tensorState block.input (_root_.InfoLossLAR.WorstCase.bundleState blocks)) state‖^2 else 0)=block.probability
      exact _Pbg block.circuit (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)
        block.input (_root_.InfoLossLAR.WorstCase.bundleState blocks) block.out (_Pae blocks)
    · change (∑ state : Bits (block.wires+_root_.InfoLossLAR.WorstCase.bundleWidth blocks),if state (Fin.natAdd block.wires (_root_.InfoLossLAR.WorstCase.bundleOutput blocks tail)) then
        ‖runLayered (_root_.InfoLossLAR.WorstCase.leftCircuit block.circuit++_root_.InfoLossLAR.WorstCase.rightCircuit (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks))
          (_root_.InfoLossLAR.WorstCase.tensorState block.input (_root_.InfoLossLAR.WorstCase.bundleState blocks)) state‖^2 else 0)=(blocks.get tail).probability
      rw [_Pbh block.circuit (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)
        block.input (_root_.InfoLossLAR.WorstCase.bundleState blocks) (_root_.InfoLossLAR.WorstCase.bundleOutput blocks tail) block.normalized]
      exact ih tail
open _root_.P2Mf6bd8d28 renaming h376 → _Pag
theorem _root_.P2Mf6bd8d28.h370 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock)
    (h : ∀ block ∈ blocks,∀ layer ∈ block.circuit,LayerOk layer) :
    ∀ layer ∈ _root_.InfoLossLAR.WorstCase.bundleCircuit blocks,LayerOk layer := by
  induction blocks with
  | nil => simp [_root_.InfoLossLAR.WorstCase.bundleCircuit]
  | cons block blocks ih =>
    intro layer hl
    rcases List.mem_append.mp hl with hl|hl
    · exact _Pcr block.circuit (h block (by simp)) layer hl
    · exact _Pfd (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)
        (ih (fun b hb => h b (by simp [hb]))) layer hl
open _root_.P2Mf6bd8d28 renaming h370 → _Paa
theorem _root_.P2Mf6bd8d28.h369 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock) :
    depth (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)=(blocks.map (fun block => depth block.circuit)).sum := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    change depth (_root_.InfoLossLAR.WorstCase.leftCircuit block.circuit++_root_.InfoLossLAR.WorstCase.rightCircuit (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)) = _
    have hd {n : ℕ} (first second : Layered n) : depth (first++second)=depth first+depth second := List.length_append
    rw [hd,_root_.InfoLossLAR.WorstCase.leftCircuit_depth,_root_.InfoLossLAR.WorstCase.rightCircuit_depth,ih]
    rfl
open _root_.P2Mf6bd8d28 renaming h369 → _Pa9
theorem _root_.P2Mf6bd8d28.h418 (D : Family) (word : Str) :
    (_root_.InfoLossLAR.WorstCase.familyBlock D word.length (toBits word)).probability=acceptProb D word := rfl
open _root_.P2Mf6bd8d28 renaming h418 → _Pbm
theorem _root_.P2Mf6bd8d28.h375 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock) :
    _root_.InfoLossLAR.WorstCase.bundleWidth blocks=(blocks.map _root_.InfoLossLAR.WorstCase.QuantumBlock.wires).sum := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih => simp only [_root_.InfoLossLAR.WorstCase.bundleWidth,List.map_cons,List.sum_cons,ih]
open _root_.P2Mf6bd8d28 renaming h375 → _Paf
theorem _root_.P2Mf6bd8d28.h509 (D : Family) (maximum : ℕ) (first second : Str) :
    _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum first)=_root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum second) := by
  simp only [_Paf,_root_.InfoLossLAR.WorstCase.queryBlocks,List.map_ofFn,_root_.InfoLossLAR.WorstCase.familyBlock,Function.comp_def]
open _root_.P2Mf6bd8d28 renaming h509 → _Pe5
theorem _root_.P2Mf6bd8d28.h507 (D : Family) (maximum : ℕ) (query : Str)
    (hlength : query.length ≤ maximum) :
    let index : Fin (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query).length := ⟨query.length,by
      simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]
      omega⟩
    (∑ state : Bits (_root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query)),
      if state (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query) index) then
        ‖runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query))
          (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query)) state‖^2 else 0)=acceptProb D query := by
  dsimp only
  rw [_Pag]
  simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.get_eq_getElem,List.getElem_ofFn]
  change (_root_.InfoLossLAR.WorstCase.familyBlock D query.length (fun index => (query[index.val]?).getD false)).probability=acceptProb D query
  have hbits : (fun index : Fin query.length => (query[index.val]?).getD false)=toBits query := by
    funext index
    simp [toBits,index.isLt]
  rw [hbits,_Pbm]
open _root_.P2Mf6bd8d28 renaming h507 → _Pe3
theorem _root_.P2Mf6bd8d28.h508 (D : Family) (hD : WellFormed D) (maximum : ℕ) (query : Str) :
    ∀ layer ∈ _root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query),LayerOk layer := by
  apply _Paa
  intro block hb
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hb
  exact hD index.val
open _root_.P2Mf6bd8d28 renaming h508 → _Pe4
theorem _root_.P2Mf6bd8d28.h503 (D : Family) (p : Polynomial ℕ)
    (hdepth : ∀ length,depth (D.circ length) ≤ p.eval length) (maximum : ℕ) (query : Str) :
    depth (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query)) ≤ (maximum+1)*p.eval maximum := by
  rw [_Pa9]
  simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.map_ofFn,List.sum_ofFn,_root_.InfoLossLAR.WorstCase.familyBlock]
  calc
    (∑ index : Fin (maximum+1),depth (D.circ index.val)) ≤ ∑ _ : Fin (maximum+1),p.eval maximum := by
      apply Finset.sum_le_sum
      intro index _
      exact (hdepth index.val).trans (OAI.MetricKMedian.Binary.polynomial_eval_mono p (b := maximum) (by omega))
    _ = _ := by simp
open _root_.P2Mf6bd8d28 renaming h503 → _Pdz
theorem _root_.P2Mf6bd8d28.h510 (D : Family) (p : Polynomial ℕ)
    (hanc : ∀ length,D.anc length ≤ p.eval length) (maximum : ℕ) (query : Str) :
    _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query) ≤ (maximum+1)*(maximum+p.eval maximum+1) := by
  rw [_Paf]
  simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.map_ofFn,List.sum_ofFn,_root_.InfoLossLAR.WorstCase.familyBlock]
  calc
    (∑ index : Fin (maximum+1),(index.val+(D.anc index.val+1))) ≤
        ∑ _ : Fin (maximum+1),(maximum+p.eval maximum+1) := by
      apply Finset.sum_le_sum
      intro index _
      have h := (hanc index.val).trans (OAI.MetricKMedian.Binary.polynomial_eval_mono p (b := maximum) (by omega))
      have hi := index.isLt
      omega
    _ = _ := by simp
open _root_.P2Mf6bd8d28 renaming h510 → _Pe6
theorem _root_.P2Mf6bd8d28.h372 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock) :
    _root_.InfoLossLAR.WorstCase.bundlePhysical blocks=(blocks.map (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires))).foldr
      _root_.InfoLossLAR.WorstCase.appendPhysical ⟨0,[]⟩ := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    change _root_.InfoLossLAR.WorstCase.appendPhysical ⟨block.wires,block.circuit⟩ (_root_.InfoLossLAR.WorstCase.bundlePhysical blocks)=_
    rw [List.map_cons,List.foldr_cons,ih]
open _root_.P2Mf6bd8d28 renaming h372 → _Pac
theorem _root_.P2Mf6bd8d28.h506 (D : Family) (maximum : ℕ) (first second : Str) :
    _root_.InfoLossLAR.WorstCase.bundlePhysical (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum first)=_root_.InfoLossLAR.WorstCase.bundlePhysical (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum second) := by
  rw [_Pac,_Pac]
  have h : (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum first).map
      (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires))=
      (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum second).map
      (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires)) := by
    simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.map_ofFn,_root_.InfoLossLAR.WorstCase.familyBlock,Function.comp_def]
  rw [h]
open _root_.P2Mf6bd8d28 renaming h506 → _Pe2
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h369 → _Pa9
open _root_.P2Mf6bd8d28 renaming h370 → _Paa
open _root_.P2Mf6bd8d28 renaming h372 → _Pac
open _root_.P2Mf6bd8d28 renaming h374 → _Pae
open _root_.P2Mf6bd8d28 renaming h375 → _Paf
open _root_.P2Mf6bd8d28 renaming h376 → _Pag
open _root_.P2Mf6bd8d28 renaming h418 → _Pbm
open _root_.P2Mf6bd8d28 renaming h503 → _Pdz
open _root_.P2Mf6bd8d28 renaming h506 → _Pe2
open _root_.P2Mf6bd8d28 renaming h507 → _Pe3
open _root_.P2Mf6bd8d28 renaming h508 → _Pe4
open _root_.P2Mf6bd8d28 renaming h509 → _Pe5
open _root_.P2Mf6bd8d28 renaming h510 → _Pe6
end
open _root_.P2Mf6bd8d28 renaming h369 → _Pa9
open _root_.P2Mf6bd8d28 renaming h370 → _Paa
open _root_.P2Mf6bd8d28 renaming h372 → _Pac
open _root_.P2Mf6bd8d28 renaming h374 → _Pae
open _root_.P2Mf6bd8d28 renaming h375 → _Paf
open _root_.P2Mf6bd8d28 renaming h376 → _Pag
open _root_.P2Mf6bd8d28 renaming h418 → _Pbm
open _root_.P2Mf6bd8d28 renaming h503 → _Pdz
open _root_.P2Mf6bd8d28 renaming h506 → _Pe2
open _root_.P2Mf6bd8d28 renaming h507 → _Pe3
open _root_.P2Mf6bd8d28 renaming h508 → _Pe4
open _root_.P2Mf6bd8d28 renaming h509 → _Pe5
open _root_.P2Mf6bd8d28 renaming h510 → _Pe6
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h383 (count : ℕ) : (∑ state,‖_root_.InfoLossLAR.WorstCase.coinZero count state‖^2)=(1 : ℝ) := by
  classical
  rw [Finset.sum_eq_single (fun _ : Fin count => false)]
  · simp [_root_.InfoLossLAR.WorstCase.coinZero]
  · intro state _ hne
    simp [_root_.InfoLossLAR.WorstCase.coinZero,hne]
  · simp
open _root_.P2Mf6bd8d28 renaming h383 → _Pan
theorem _root_.P2Mf6bd8d28.h384 (first second : ℕ) : _root_.InfoLossLAR.WorstCase.coinZero (first+second)=_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.coinZero first) (_root_.InfoLossLAR.WorstCase.coinZero second) := by
  funext state
  have hzero : state=(fun _ => false) ↔ _root_.InfoLossLAR.WorstCase.leftRegister state=(fun _ => false) ∧ _root_.InfoLossLAR.WorstCase.rightRegister state=(fun _ => false) := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · rintro ⟨hl,hr⟩
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro i
        exact congrArg (fun word => word i) hl
      · intro i
        exact congrArg (fun word => word i) hr
  by_cases hl : _root_.InfoLossLAR.WorstCase.leftRegister state=(fun _ => false)
  · by_cases hr : _root_.InfoLossLAR.WorstCase.rightRegister state=(fun _ => false)
    · change (if state=(fun _ => false) then (1 : ℂ) else 0)=
        (if _root_.InfoLossLAR.WorstCase.leftRegister state=(fun _ => false) then 1 else 0)*
          (if _root_.InfoLossLAR.WorstCase.rightRegister state=(fun _ => false) then 1 else 0)
      rw [if_pos (hzero.mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ (fun _ => false) := fun h => hr (hzero.mp h).2
      simp [_root_.InfoLossLAR.WorstCase.coinZero,_root_.InfoLossLAR.WorstCase.tensorState,hl,hr,hs]
  · have hs : state ≠ (fun _ => false) := fun h => hl (hzero.mp h).1
    simp [_root_.InfoLossLAR.WorstCase.coinZero,_root_.InfoLossLAR.WorstCase.tensorState,hl,hs]
open _root_.P2Mf6bd8d28 renaming h384 → _Pao
private theorem _root_.P2Mf6bd8d28.h895 : runLayered [[.h (0 : Fin 1)]] (_root_.InfoLossLAR.WorstCase.coinZero 1)=
    (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) := by
  funext state
  have hf : Function.update state (0 : Fin 1) false=(fun _ => false) := by
    funext index
    have hi : index=0 := Subsingleton.elim _ _
    subst index
    simp
  have ht : Function.update state (0 : Fin 1) true ≠ (fun _ => false) := by
    intro h
    have hh := congrArg (fun word => word 0) h
    simp at hh
  simp only [runLayered,runLayer,List.foldl_cons,List.foldl_nil,Instr.apply,apply1,Fintype.sum_bool]
  simp [_root_.InfoLossLAR.WorstCase.coinZero,hf,ht,hMat]
open _root_.P2Mf6bd8d28 renaming h895 → _Pov
theorem _root_.P2Mf6bd8d28.h381 (count : ℕ) : runLayered (_root_.InfoLossLAR.WorstCase.coinCircuit count) (_root_.InfoLossLAR.WorstCase.coinZero count)=
    (fun _ => _root_.InfoLossLAR.WorstCase.coinAmplitude count) := by
  induction count with
  | zero =>
    funext state
    have hs : state=(fun _ : Fin 0 => false) := Subsingleton.elim _ _
    simp [_root_.InfoLossLAR.WorstCase.coinCircuit,runLayered,_root_.InfoLossLAR.WorstCase.coinZero,_root_.InfoLossLAR.WorstCase.coinAmplitude,hs]
  | succ count ih =>
    rw [_root_.InfoLossLAR.WorstCase.coinCircuit,_Pao count 1,_Pbi,ih,_Pov]
    funext state
    exact (pow_succ _ count).symm
open _root_.P2Mf6bd8d28 renaming h381 → _Pal
theorem _root_.P2Mf6bd8d28.h382 (count : ℕ) : ∀ layer ∈ _root_.InfoLossLAR.WorstCase.coinCircuit count,LayerOk layer := by
  rw [_root_.InfoLossLAR.WorstCase.coinCircuit_direct]
  intro layer hl
  obtain ⟨wire,rfl⟩ := List.mem_ofFn.mp hl
  exact List.pairwise_singleton _ _
open _root_.P2Mf6bd8d28 renaming h382 → _Pam
theorem _root_.P2Mf6bd8d28.h377 (count : ℕ) : ‖_root_.InfoLossLAR.WorstCase.coinAmplitude count‖^2=(Fintype.card (Bits count) : ℝ)⁻¹ := by
  have h := _root_.InfoLossLAR.WorstCase.runLayered_mass (_root_.InfoLossLAR.WorstCase.coinCircuit count) (_root_.InfoLossLAR.WorstCase.coinZero count)
  simp only [_Pal,Complex.normSq_eq_norm_sq] at h
  rw [_Pan] at h
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have hc : (Fintype.card (Bits count) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (mul_left_cancel₀ hc)
  rw [h,mul_inv_cancel₀ hc]
open _root_.P2Mf6bd8d28 renaming h377 → _Pah
section Description
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h380 : Poly _root_.InfoLossLAR.WorstCase.coinCircuitDescription := by
  have hgate : Poly (fun input : Str × ℕ =>
      _root_.Integration9_9.TM2PlatformSerialization.serializeWords [encNat 0++_root_.Integration9_9.TM2PlatformSerialization.lengthToken (input.1.take input.2)]) := by
    have ht : Poly (fun input : Str × ℕ => input.1.take input.2) := parser_take_poly
    fun_prop
  unfold _root_.InfoLossLAR.WorstCase.coinCircuitDescription
  exact Poly.comp _Pn2 (Poly.list_map hgate Poly.list_indices)
open _root_.P2Mf6bd8d28 renaming h380 → _Pak
theorem _root_.P2Mf6bd8d28.h379 (xs : Str) :
    _root_.InfoLossLAR.WorstCase.coinCircuitDescription xs=encCirc (_root_.InfoLossLAR.WorstCase.coinCircuit xs.length) := by
  rw [_root_.InfoLossLAR.WorstCase.coinCircuit_direct]
  unfold _root_.InfoLossLAR.WorstCase.coinCircuitDescription encCirc
  rw [List.map_ofFn,_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq]
  apply congrArg encStr
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hi : index<xs.length := by simpa using hleft
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq,
      _root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,List.length_take,Nat.min_eq_left hi.le,Function.comp_def,encLayer,encInstr,
      List.map_cons,List.map_nil]
open _root_.P2Mf6bd8d28 renaming h379 → _Paj
end Description
open _root_.P2Mf6bd8d28 renaming h379 → _Paj
open _root_.P2Mf6bd8d28 renaming h380 → _Pak
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h377 → _Pah
open _root_.P2Mf6bd8d28 renaming h379 → _Paj
open _root_.P2Mf6bd8d28 renaming h380 → _Pak
open _root_.P2Mf6bd8d28 renaming h381 → _Pal
open _root_.P2Mf6bd8d28 renaming h382 → _Pam
open _root_.P2Mf6bd8d28 renaming h383 → _Pan
open _root_.P2Mf6bd8d28 renaming h384 → _Pao
open _root_.P2Mf6bd8d28 renaming h895 → _Pov
end
open _root_.P2Mf6bd8d28 renaming h377 → _Pah
open _root_.P2Mf6bd8d28 renaming h379 → _Paj
open _root_.P2Mf6bd8d28 renaming h380 → _Pak
open _root_.P2Mf6bd8d28 renaming h381 → _Pal
open _root_.P2Mf6bd8d28 renaming h382 → _Pam
open _root_.P2Mf6bd8d28 renaming h383 → _Pan
open _root_.P2Mf6bd8d28 renaming h384 → _Pao
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
private theorem _root_.P2Mf6bd8d28.h869 {n m : ℕ} (state : Bits (n+m)) (left : Bits n) (right : Bits m) :
    state=Fin.append left right ↔ _root_.InfoLossLAR.WorstCase.leftRegister state=left ∧ _root_.InfoLossLAR.WorstCase.rightRegister state=right := by
  constructor
  · rintro rfl
    exact ⟨by funext i; simp [_root_.InfoLossLAR.WorstCase.leftRegister],by funext i; simp [_root_.InfoLossLAR.WorstCase.rightRegister]⟩
  · rintro ⟨hl,hr⟩
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i
      simpa only [Fin.append_left,_root_.InfoLossLAR.WorstCase.leftRegister] using congrArg (fun word => word i) hl
    · intro i
      simpa only [Fin.append_right,_root_.InfoLossLAR.WorstCase.rightRegister] using congrArg (fun word => word i) hr
open _root_.P2Mf6bd8d28 renaming h869 → _Po5
theorem _root_.P2Mf6bd8d28.h344 {n a : ℕ} (input : Bits n) :
    basisInput (a := a) input=_root_.InfoLossLAR.WorstCase.computationalBasis (Fin.append input (fun _ => false)) := by
  funext state
  unfold basisInput _root_.InfoLossLAR.WorstCase.computationalBasis
  congr 1
  apply propext
  rw [_Po5]
  simp only [funext_iff,_root_.InfoLossLAR.WorstCase.leftRegister,_root_.InfoLossLAR.WorstCase.rightRegister]
open _root_.P2Mf6bd8d28 renaming h344 → _P9k
theorem _root_.P2Mf6bd8d28.h401 {n m : ℕ} (left : Bits n) (right : Bits m) :
    _root_.InfoLossLAR.WorstCase.computationalBasis (Fin.append left right)=_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis left) (_root_.InfoLossLAR.WorstCase.computationalBasis right) := by
  funext state
  change (if state=Fin.append left right then (1 : ℂ) else 0)=
    (if _root_.InfoLossLAR.WorstCase.leftRegister state=left then 1 else 0)*(if _root_.InfoLossLAR.WorstCase.rightRegister state=right then 1 else 0)
  by_cases hl : _root_.InfoLossLAR.WorstCase.leftRegister state=left
  · by_cases hr : _root_.InfoLossLAR.WorstCase.rightRegister state=right
    · rw [if_pos ((_Po5 state left right).mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ Fin.append left right := fun h => hr ((_Po5 state left right).mp h).2
      rw [if_neg hs,if_pos hl,if_neg hr,mul_zero]
  · have hs : state ≠ Fin.append left right := fun h => hl ((_Po5 state left right).mp h).1
    rw [if_neg hs,if_neg hl,zero_mul]
open _root_.P2Mf6bd8d28 renaming h401 → _Pb5
theorem _root_.P2Mf6bd8d28.h378 {coins body : ℕ} (outputs : Bits coins → Bits body) :
    _root_.InfoLossLAR.WorstCase.coinBranchState (fun coin => _root_.InfoLossLAR.WorstCase.computationalBasis (outputs coin))=
      ∑ coin : Bits coins,_root_.InfoLossLAR.WorstCase.coinAmplitude coins • _root_.InfoLossLAR.WorstCase.computationalBasis (Fin.append coin (outputs coin)) := by
  classical
  simp_rw [_Pb5]
  funext state
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,_root_.InfoLossLAR.WorstCase.tensorState,_root_.InfoLossLAR.WorstCase.computationalBasis,_root_.InfoLossLAR.WorstCase.coinBranchState]
  rw [Finset.sum_eq_single (_root_.InfoLossLAR.WorstCase.leftRegister state)]
  · simp
  · intro coin _ hne
    simp [Ne.symm hne]
  · simp
open _root_.P2Mf6bd8d28 renaming h378 → _Pai
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h344 → _P9k
open _root_.P2Mf6bd8d28 renaming h378 → _Pai
open _root_.P2Mf6bd8d28 renaming h401 → _Pb5
open _root_.P2Mf6bd8d28 renaming h869 → _Po5
end
open _root_.P2Mf6bd8d28 renaming h344 → _P9k
open _root_.P2Mf6bd8d28 renaming h378 → _Pai
open _root_.P2Mf6bd8d28 renaming h401 → _Pb5
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing QAlgorithms.Complexity
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}
theorem _root_.P2Mf6bd8d28.h314 (word : List Bool) (i : ℕ) (h : i < word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word i = word[i] := by simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension, List.getElem?_eq_getElem h, Option.getD_some]
open _root_.P2Mf6bd8d28 renaming h314 → _P8q
theorem _root_.P2Mf6bd8d28.h312 (word : List Bool) (i : ℕ) (h : word.length ≤ i) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word i = false := by simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension, List.getElem?_eq_none h, Option.getD_none]
open _root_.P2Mf6bd8d28 renaming h312 → _P8o
theorem _root_.P2Mf6bd8d28.h313 (word : List Bool) (ancillas : ℕ) :
    Fin.append (toBits word) (fun _ : Fin (ancillas + 1) => false) =
      (fun i : Fin (word.length + (ancillas + 1)) => _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word i.val) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Fin.coe_castAdd, toBits, List.get_eq_getElem] using
      (_P8q word j.val j.isLt).symm
  · intro j
    simp only [Fin.append_right, Fin.val_natAdd]
    exact (_P8o word _ (Nat.le_add_right _ _)).symm
open _root_.P2Mf6bd8d28 renaming h313 → _P8p
theorem _root_.P2Mf6bd8d28.h301 (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool)
    (hsize : word.length + _root_.Integration9_9.TM2OutputLength.programPushBound program * ticks ≤ width) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) :
    (fun j => _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks word.length).ops (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) j.val)
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineOutputWire hw program input main initialState ticks word.length i) =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.configurationBit ((_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep program)^[ticks] (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration input main initialState word)) i :=
  _P8f hw program input main initialState ticks word (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word)
    (_P8q word) hsize i
open _root_.P2Mf6bd8d28 renaming h301 → _P8d
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h301 → _P8d
open _root_.P2Mf6bd8d28 renaming h312 → _P8o
open _root_.P2Mf6bd8d28 renaming h313 → _P8p
open _root_.P2Mf6bd8d28 renaming h314 → _P8q
end
open _root_.P2Mf6bd8d28 renaming h301 → _P8d
open _root_.P2Mf6bd8d28 renaming h312 → _P8o
open _root_.P2Mf6bd8d28 renaming h313 → _P8p
open _root_.P2Mf6bd8d28 renaming h314 → _P8q
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2PlatformSerialization
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
@[fun_prop] theorem _root_.P2Mf6bd8d28.h202 (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) :
    Poly (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request × ℕ => _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.description program input main initialState x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.description
  fun_prop
open _root_.P2Mf6bd8d28 renaming h202 → _P5m
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open _root_.P2Mf6bd8d28 renaming h202 → _P5m
end
open _root_.P2Mf6bd8d28 renaming h202 → _P5m
section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing StateTransition QAlgorithms.Complexity
open Integration9_9.TM2OutputLength
open OAI.MetricKMedian.Binary
namespace PolyProgramCircuit
variable {f : Str → Str} (P : PolyProgram id id f)
attribute [local instance] _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions
attribute [local instance] _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions
theorem _root_.P2Mf6bd8d28.h223 (word : Str) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.stickyStep P.machine.code)^[P.time.eval word.length]
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration P.machine.input P.machine.main P.machine.initial word) =
        P.machine.finalCfg (f word) := by
  have hh := P.outputs word
  change EvalsToInTime (TM2.step P.machine.code)
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.initialConfiguration P.machine.input P.machine.main P.machine.initial word)
    (some (P.machine.finalCfg (f word))) (P.time.eval word.length) at hh
  exact _P8k P.machine.code _ _ _ hh rfl
open _root_.P2Mf6bd8d28 renaming h223 → _P67
theorem _root_.P2Mf6bd8d28.h235 (word : Str) (i : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length)) (b : Option Bool) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputWire P word.length i b) = decide (b = (f word)[i.val]?) := by
  have hh := _P8d (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity_pos P word.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval word.length) word (by unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity; omega)
    (.inr (.inr (P.machine.output, i, b)))
  rw [_P67 P word] at hh
  simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result, _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputWire, _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled, _root_.InfoLossLAR.WorstCase.TM2Boolean.configurationBit, Machine.finalCfg, ↓reduceIte] using hh
open _root_.P2Mf6bd8d28 renaming h235 → _P6j
theorem _root_.P2Mf6bd8d28.h241 (length : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.spacePolynomial P).eval length =
      (1 + P.time.eval length * _root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound P.machine.code 0) *
        Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot P.machine.K P.machine.Label P.machine.State (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length)) := by
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.spacePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, _root_.InfoLossLAR.WorstCase.TM2Boolean.slot_count, _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity]
  ring
open _root_.P2Mf6bd8d28 renaming h241 → _P6p
theorem _root_.P2Mf6bd8d28.h220 (length : ℕ) : (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P length).ops.length ≤ (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.spacePolynomial P).eval length := by
  rw [_P6p]
  exact _P8e _ _ _ _ _ _ _
open _root_.P2Mf6bd8d28 renaming h220 → _P64
end PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h220 → _P64
open _root_.P2Mf6bd8d28 renaming h223 → _P67
open _root_.P2Mf6bd8d28 renaming h235 → _P6j
open _root_.P2Mf6bd8d28 renaming h241 → _P6p
end InfoLossLAR.WorstCase.TM2Boolean
open _root_.P2Mf6bd8d28 renaming h220 → _P64
open _root_.P2Mf6bd8d28 renaming h223 → _P67
open _root_.P2Mf6bd8d28 renaming h235 → _P6j
open _root_.P2Mf6bd8d28 renaming h241 → _P6p
end
end
open _root_.P2Mf6bd8d28 renaming h220 → _P64
open _root_.P2Mf6bd8d28 renaming h223 → _P67
open _root_.P2Mf6bd8d28 renaming h235 → _P6j
open _root_.P2Mf6bd8d28 renaming h241 → _P6p
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open Turing StateTransition QAlgorithms.Complexity Polynomial
open Integration9_9.TM2OutputLength Integration9_9.TM2PlatformSerialization
open Integration9_9.TM2PolynomialBudget
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open CodeGenerator
variable {f : Str → Str} (P : PolyProgram id id f)
attribute [local instance] _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_1
attribute [local instance] _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_1
@[fun_prop] theorem _root_.P2Mf6bd8d28.h240 : Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.request P) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.request
  fun_prop
open _root_.P2Mf6bd8d28 renaming h240 → _P6o
@[fun_prop] theorem _root_.P2Mf6bd8d28.h222 : Poly (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.descriptionGenerator P) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.descriptionGenerator _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputIndex
  fun_prop
open _root_.P2Mf6bd8d28 renaming h222 → _P66
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h222 → _P66
open _root_.P2Mf6bd8d28 renaming h240 → _P6o
end
end
open _root_.P2Mf6bd8d28 renaming h222 → _P66
open _root_.P2Mf6bd8d28 renaming h240 → _P6o
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open Integration9_9.TM2OutputLength
theorem _root_.P2Mf6bd8d28.h219 {f : Str → Str} (P : PolyProgram id id f) (word : Str) :
    (f word).length<_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length := by
  have h := _root_.Integration9_9.TM2OutputLength.output_length_le P.machine.tm word (f word) (P.time.eval word.length) (P.outputs word)
  change (f word).length≤word.length+_root_.Integration9_9.TM2OutputLength.programPushBound P.machine.code*P.time.eval word.length at h
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity
  omega
open _root_.P2Mf6bd8d28 renaming h219 → _P63
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h219 → _P63
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
open LARRankOneMachine
end Integration9_9.LARCoinLayout
end
open _root_.P2Mf6bd8d28 renaming h219 → _P63
namespace Integration9_9.LARCoinLayout
end Integration9_9.LARCoinLayout
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open CodeGenerator
variable {f : Str → Str} (P : PolyProgram id id f)
attribute [local instance] _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_3
attribute [local instance] _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_3
@[fun_prop] theorem _root_.P2Mf6bd8d28.h234 :
    Poly (fun x : ℕ × ℕ => _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputSlotIndex P x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputSlotIndex
  fun_prop
open _root_.P2Mf6bd8d28 renaming h234 → _P6i
theorem _root_.P2Mf6bd8d28.h233 (width : ℕ) (index : Fin width) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputSlotIndex P width index.val=
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv P.machine.K P.machine.Label P.machine.State width
        (.inr (.inr (P.machine.output,index,some true)))).val :=
  (_root_.InfoLossLAR.WorstCase.TM2Boolean.slot_stack_index width P.machine.output index (some true)).symm
open _root_.P2Mf6bd8d28 renaming h233 → _P6h
@[fun_prop] theorem _root_.P2Mf6bd8d28.h228 :
    Poly (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request × ℕ => _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedOutputAddress P x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedOutputAddress
  fun_prop
open _root_.P2Mf6bd8d28 renaming h228 → _P6c
theorem _root_.P2Mf6bd8d28.h227 (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) (hw : 0<x.2.1.length) (index : Fin x.2.1.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedOutputAddress P x index.val=
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw P.machine.code P.machine.input P.machine.main P.machine.initial
        x.2.2.length x.1.length).output (.inr (.inr (P.machine.output,index,some true))) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedOutputAddress
  rw [_P6h]
  exact (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial x hw).2.2 _
open _root_.P2Mf6bd8d28 renaming h227 → _P6b
@[fun_prop] theorem _root_.P2Mf6bd8d28.h230 :
    Poly (fun x : Str × ℕ => _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress
  fun_prop
open _root_.P2Mf6bd8d28 renaming h230 → _P6e
theorem _root_.P2Mf6bd8d28.h232 {a b : ℕ} (he : a=b) (ha : 0<a) (hb : 0<b)
    (ticks length : ℕ) (index : Fin a) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram ha P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,index,some true)))=
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hb P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,Fin.cast he index,some true))) := by
  cases he
  rfl
open _root_.P2Mf6bd8d28 renaming h232 → _P6g
theorem _root_.P2Mf6bd8d28.h229 (length : ℕ) (index : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length)) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary length) index.val=(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputWire P length index (some true)).val := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.request_unary]
  let width := (List.replicate (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length) ()).length
  have hwidth : width=_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length := List.length_replicate
  have hw : 0<width := by rw [hwidth]; exact _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity_pos P length
  let i : Fin width := ⟨index.val,by rw [hwidth]; exact index.isLt⟩
  have hi : Fin.cast hwidth i=index := Fin.ext rfl
  have h := _P6b P
    (List.replicate length (),List.replicate (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length) (),List.replicate (P.time.eval length) ()) hw i
  simp only [List.length_replicate] at h
  have he := _P6g P hwidth hw (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity_pos P length) (P.time.eval length) length i
  rw [he,hi] at h
  simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputWire,_root_.InfoLossLAR.WorstCase.TM2Boolean.machineOutputWire,_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled,i] using h
open _root_.P2Mf6bd8d28 renaming h229 → _P6d
@[fun_prop] theorem _root_.P2Mf6bd8d28.h226 :
    Poly (fun x : Str × (List Unit × ℕ) => _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange P x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun x : Str × (List Unit × ℕ) => x.2.1) Automatic.Poly.list_indices (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h226 → _P6a
theorem _root_.P2Mf6bd8d28.h224 (length : ℕ) (slots : List Unit) (offset : ℕ)
    (h : offset+slots.length ≤ _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length) :
    ∀ address∈_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange P (unary length) slots offset,
      address<length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P length).ops.length+1) := by
  intro address ha
  obtain ⟨index,hi,rfl⟩ := List.mem_map.mp ha
  have hin := List.mem_range.mp hi
  let cell : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P length) := ⟨offset+index,by omega⟩
  change _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary length) cell.val<_
  rw [_P6d]
  exact (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputWire P length cell (some true)).isLt
open _root_.P2Mf6bd8d28 renaming h224 → _P68
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h224 → _P68
open _root_.P2Mf6bd8d28 renaming h226 → _P6a
open _root_.P2Mf6bd8d28 renaming h227 → _P6b
open _root_.P2Mf6bd8d28 renaming h228 → _P6c
open _root_.P2Mf6bd8d28 renaming h229 → _P6d
open _root_.P2Mf6bd8d28 renaming h230 → _P6e
open _root_.P2Mf6bd8d28 renaming h232 → _P6g
open _root_.P2Mf6bd8d28 renaming h233 → _P6h
open _root_.P2Mf6bd8d28 renaming h234 → _P6i
end
end
open _root_.P2Mf6bd8d28 renaming h224 → _P68
open _root_.P2Mf6bd8d28 renaming h226 → _P6a
open _root_.P2Mf6bd8d28 renaming h227 → _P6b
open _root_.P2Mf6bd8d28 renaming h228 → _P6c
open _root_.P2Mf6bd8d28 renaming h229 → _P6d
open _root_.P2Mf6bd8d28 renaming h230 → _P6e
open _root_.P2Mf6bd8d28 renaming h232 → _P6g
open _root_.P2Mf6bd8d28 renaming h233 → _P6h
open _root_.P2Mf6bd8d28 renaming h234 → _P6i
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h463 (start left : ℕ) (choice : ℕ × ℕ)
    (hl : left<start) (hf : choice.1<start) (hr : choice.2<start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (_root_.InfoLossLAR.WorstCase.multiSelectorChunk start left choice) := by
  simp_all [_root_.InfoLossLAR.WorstCase.multiSelectorChunk,_root_.InfoLossLAR.WorstCase.BooleanProgram.Valid,_root_.InfoLossLAR.WorstCase.BooleanOp.Valid,_root_.InfoLossLAR.WorstCase.BooleanOp.sources]
  omega
open _root_.P2Mf6bd8d28 renaming h463 → _Pcv
theorem _root_.P2Mf6bd8d28.h473 (start left : ℕ) (choices : List (ℕ × ℕ))
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices) := by
  induction choices generalizing start left with
  | nil => trivial
  | cons choice rest ih =>
    rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps,_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append]
    have hf := hc choice (by simp)
    refine ⟨_Pcv start left choice hl hf.1 hf.2,?_⟩
    change _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid (start+4) (_root_.InfoLossLAR.WorstCase.multiSelectorOps (start+4) (start+3) rest)
    apply ih (start+4) (start+3) (by omega)
    intro other ho
    have h := hc other (by simp [ho])
    omega
open _root_.P2Mf6bd8d28 renaming h473 → _Pd5
theorem _root_.P2Mf6bd8d28.h464 (start left : ℕ) (choice : ℕ × ℕ) (state : ℕ → Bool)
    (hl : left<start) (hf : choice.1<start) (hr : choice.2<start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (_root_.InfoLossLAR.WorstCase.multiSelectorChunk start left choice) state (start+3)=
      if state choice.1 then state choice.2 else state left := by
  cases hflag : state choice.1 <;> cases hleft : state left <;> cases hright : state choice.2 <;>
    simp (disch := omega) [_root_.InfoLossLAR.WorstCase.multiSelectorChunk,_root_.InfoLossLAR.WorstCase.BooleanProgram.run,_root_.InfoLossLAR.WorstCase.BooleanOp.assign,_root_.InfoLossLAR.WorstCase.BooleanOp.eval,
      Function.update_apply,hflag,hleft,hright]
open _root_.P2Mf6bd8d28 renaming h464 → _Pcw
theorem _root_.P2Mf6bd8d28.h476 (choices : List (ℕ × ℕ)) (first second : ℕ → Bool)
    (initial : Bool) (h : ∀ choice∈choices,first choice.1=second choice.1 ∧ first choice.2=second choice.2) :
    _root_.InfoLossLAR.WorstCase.multiSelectorValue first initial choices=_root_.InfoLossLAR.WorstCase.multiSelectorValue second initial choices := by
  induction choices generalizing initial with
  | nil => rfl
  | cons choice rest ih =>
    have hc := h choice (by simp)
    simp only [_root_.InfoLossLAR.WorstCase.multiSelectorValue,hc.1,hc.2]
    exact ih _ (fun other ho => h other (by simp [ho]))
open _root_.P2Mf6bd8d28 renaming h476 → _Pd8
theorem _root_.P2Mf6bd8d28.h474 (start left : ℕ) (choices : List (ℕ × ℕ)) (state : ℕ → Bool)
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices) state
      (_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices)=_root_.InfoLossLAR.WorstCase.multiSelectorValue state (state left) choices := by
  induction choices generalizing start left state with
  | nil => rfl
  | cons choice rest ih =>
    have hf := hc choice (by simp)
    rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps,_P46]
    change _root_.InfoLossLAR.WorstCase.BooleanProgram.run (start+4) (_root_.InfoLossLAR.WorstCase.multiSelectorOps (start+4) (start+3) rest)
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.run start (_root_.InfoLossLAR.WorstCase.multiSelectorChunk start left choice) state)
      (_root_.InfoLossLAR.WorstCase.multiSelectorOutput (start+4) (start+3) rest)=_
    rw [ih (start+4) (start+3) _ (by omega) (fun other ho => by
      have h := hc other (by simp [ho]); omega)]
    rw [_Pcw start left choice state hl hf.1 hf.2]
    rw [_Pd8 rest _ state _ (fun other ho => by
      have h := hc other (by simp [ho])
      exact ⟨_P47 start _ state _ h.1,_P47 start _ state _ h.2⟩)]
    rfl
open _root_.P2Mf6bd8d28 renaming h474 → _Pd6
theorem _root_.P2Mf6bd8d28.h479 {n start left : ℕ} (choices : List (ℕ × ℕ))
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start)
    (hn : start+4*choices.length ≤ n) (state : QState n)
    (hz : ∀ input,state input≠0 → ∀ index,start ≤ index → index<start+4*choices.length →
      _root_.InfoLossLAR.WorstCase.selectorBitsExtension input index=false) :
    (∑ output : Bits n,if output ⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,
        (_root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl).trans_le hn⟩ then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
        (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
          (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; exact hn)))) state output‖^2 else 0)=
      ∑ input : Bits n,if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
        (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  have hbound : start+(_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices).length≤n := by
    rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; exact hn
  have hzero (input : Bits n) (hi : state input≠0)
      (gate : _root_.InfoLossLAR.WorstCase.BooleanGate n) (hg : gate∈_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices) hbound) :
      input gate.target=false := by
    have ht := _P49 (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices) hbound gate hg
    rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] at ht
    simpa only [_root_.InfoLossLAR.WorstCase.selectorBitsExtension_get] using hz input hi gate.target.val ht.1 ht.2
  rw [_P9n _ (_P40 _ hbound) state hzero]
  apply Finset.sum_congr rfl
  intro input hi
  have he : (fun i : Fin n => _root_.InfoLossLAR.WorstCase.selectorBitsExtension input i.val)=input := by
    funext i; simp
  have hsem := _P48 (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices) hbound
    (_Pd5 start left choices hl hc) (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
  rw [he] at hsem
  have hv := congrFun hsem (⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,
    (_root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl).trans_le hn⟩ : Fin n)
  simp only [Fin.val_mk,_Pd6 start left choices _ hl hc] at hv
  rw [hv]
open _root_.P2Mf6bd8d28 renaming h479 → _Pdb
theorem _root_.P2Mf6bd8d28.h477 (state : ℕ → Bool) (value : Bool) (choices : List (ℕ × ℕ))
    (h : ∀ choice∈choices,state choice.1=true → state choice.2=value) :
    _root_.InfoLossLAR.WorstCase.multiSelectorValue state value choices=value := by
  induction choices with
  | nil => rfl
  | cons choice rest ih =>
    have hr := ih (fun other ho => h other (by simp [ho]))
    cases hf : state choice.1
    · simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorValue,hf,Bool.false_eq_true,ite_false] using hr
    · simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorValue,hf,ite_true,h choice (by simp) hf] using hr
open _root_.P2Mf6bd8d28 renaming h477 → _Pd9
theorem _root_.P2Mf6bd8d28.h478 (state : ℕ → Bool) (value initial : Bool) (choices : List (ℕ × ℕ))
    (h : ∀ choice∈choices,state choice.1=true → state choice.2=value)
    (hex : ∃ choice∈choices,state choice.1=true) :
    _root_.InfoLossLAR.WorstCase.multiSelectorValue state initial choices=value := by
  induction choices generalizing initial with
  | nil => simpa using hex
  | cons choice rest ih =>
    have hr : ∀ other∈rest,state other.1=true → state other.2=value :=
      fun other ho => h other (by simp [ho])
    cases hf : state choice.1
    · have ht : ∃ other∈rest,state other.1=true := by
        obtain ⟨other,ho,ha⟩ := hex
        rcases List.mem_cons.mp ho with he|ho
        · subst other; simp [hf] at ha
        · exact ⟨other,ho,ha⟩
      simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorValue,hf,Bool.false_eq_true,ite_false] using ih initial hr ht
    · simp only [_root_.InfoLossLAR.WorstCase.multiSelectorValue,hf,ite_true,h choice (by simp) hf]
      exact _Pd9 state value rest hr
open _root_.P2Mf6bd8d28 renaming h478 → _Pda
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h463 → _Pcv
open _root_.P2Mf6bd8d28 renaming h464 → _Pcw
open _root_.P2Mf6bd8d28 renaming h473 → _Pd5
open _root_.P2Mf6bd8d28 renaming h474 → _Pd6
open _root_.P2Mf6bd8d28 renaming h476 → _Pd8
open _root_.P2Mf6bd8d28 renaming h477 → _Pd9
open _root_.P2Mf6bd8d28 renaming h478 → _Pda
open _root_.P2Mf6bd8d28 renaming h479 → _Pdb
end
open _root_.P2Mf6bd8d28 renaming h463 → _Pcv
open _root_.P2Mf6bd8d28 renaming h464 → _Pcw
open _root_.P2Mf6bd8d28 renaming h473 → _Pd5
open _root_.P2Mf6bd8d28 renaming h474 → _Pd6
open _root_.P2Mf6bd8d28 renaming h476 → _Pd8
open _root_.P2Mf6bd8d28 renaming h477 → _Pd9
open _root_.P2Mf6bd8d28 renaming h478 → _Pda
open _root_.P2Mf6bd8d28 renaming h479 → _Pdb
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime Integration9_9.TM2PlatformSerialization
open TM2Boolean.RPN
@[fun_prop] theorem _root_.P2Mf6bd8d28.h470 :
    Poly (fun x : ℕ × (ℕ × (ℕ × ℕ)) => _root_.InfoLossLAR.WorstCase.multiSelectorNodeChunk x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.multiSelectorNodeChunk
  fun_prop
open _root_.P2Mf6bd8d28 renaming h470 → _Pd2
theorem _root_.P2Mf6bd8d28.h469 (start left : ℕ) (choice : ℕ × ℕ) :
    _root_.InfoLossLAR.WorstCase.multiSelectorNodeChunk start left choice=(_root_.InfoLossLAR.WorstCase.multiSelectorChunk start left choice).map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node := rfl
open _root_.P2Mf6bd8d28 renaming h469 → _Pd1
@[fun_prop] theorem _root_.P2Mf6bd8d28.h472 :
    Poly (fun x : ℕ × (ℕ × List (ℕ × ℕ)) => _root_.InfoLossLAR.WorstCase.multiSelectorNodes x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.multiSelectorNodes
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.comp (f := fun xs : List (ℕ × ℕ) => List.range xs.length)
      (g := fun x : ℕ × (ℕ × List (ℕ × ℕ)) => x.2.2) Poly.list_indices (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h472 → _Pd4
theorem _root_.P2Mf6bd8d28.h471 (start left : ℕ) (choices : List (ℕ × ℕ)) :
    _root_.InfoLossLAR.WorstCase.multiSelectorNodes start left choices=(_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices).map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node := by
  induction choices generalizing start left with
  | nil => rfl
  | cons choice rest ih =>
    simp only [_root_.InfoLossLAR.WorstCase.multiSelectorNodes,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,
      List.flatMap_map,Function.comp_def,Nat.mul_zero,Nat.add_zero,ite_true,
      List.getElem?_cons_zero,Option.getD_some,_root_.InfoLossLAR.WorstCase.multiSelectorOps,List.map_append]
    rw [←_Pd1,←ih]
    congr 1
    apply List.flatMap_congr
    intro index hi
    have hs : start+4*(index+1)=(start+4)+4*index := by omega
    have hl : (if index+1=0 then left else start+4*(index+1)-1)=
        (if index=0 then start+3 else (start+4)+4*index-1) := by
      by_cases hi : index=0
      · subst index; simp
      · simp only [if_neg (by omega : index+1≠0),if_neg hi,hs]
    simp only [Nat.succ_eq_add_one,List.getElem?_cons_succ]
    rw [hl,hs]
open _root_.P2Mf6bd8d28 renaming h471 → _Pd3
@[fun_prop] theorem _root_.P2Mf6bd8d28.h468 :
    Poly (fun x : List Unit × (ℕ × (ℕ × List (ℕ × ℕ))) =>
      _root_.InfoLossLAR.WorstCase.multiSelectorGateWords x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.multiSelectorGateWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h468 → _Pd0
theorem _root_.P2Mf6bd8d28.h467 {total : ℕ} (slots : List Unit)
    (start left : ℕ) (choices : List (ℕ × ℕ))
    (hl : left<start) (hc : ∀ choice∈choices,choice.1<start ∧ choice.2<start)
    (hn : start+4*choices.length ≤ total) (hs : start+4*choices.length ≤ slots.length) :
    _root_.InfoLossLAR.WorstCase.multiSelectorGateWords slots start left choices=
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
        (by simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] using hn)).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  unfold _root_.InfoLossLAR.WorstCase.multiSelectorGateWords
  rw [_Pd3]
  exact _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWords_gates slots start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
    (by simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] using hn) (_Pd5 start left choices hl hc)
    (by simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] using hs)
open _root_.P2Mf6bd8d28 renaming h467 → _Pcz
@[fun_prop] theorem _root_.P2Mf6bd8d28.h466 :
    Poly (fun x : ℕ × (ℕ × List (ℕ × ℕ)) => _root_.InfoLossLAR.WorstCase.multiSelectorFinalIndex x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.multiSelectorFinalIndex
  fun_prop
open _root_.P2Mf6bd8d28 renaming h466 → _Pcy
theorem _root_.P2Mf6bd8d28.h465 (start left : ℕ) (choices : List (ℕ × ℕ)) :
    _root_.InfoLossLAR.WorstCase.multiSelectorFinalIndex start left choices=_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices := by
  induction choices generalizing start left with
  | nil => rfl
  | cons choice rest ih =>
    simp only [_root_.InfoLossLAR.WorstCase.multiSelectorOutput,←ih,_root_.InfoLossLAR.WorstCase.multiSelectorFinalIndex,List.isEmpty_cons,Bool.false_eq_true,ite_false]
    cases rest with
    | nil => simp
    | cons next remaining =>
      simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false,List.length_cons]
      omega
open _root_.P2Mf6bd8d28 renaming h465 → _Pcx
@[fun_prop] theorem _root_.P2Mf6bd8d28.h475 : Poly _root_.InfoLossLAR.WorstCase.multiSelectorScratch := by
  unfold _root_.InfoLossLAR.WorstCase.multiSelectorScratch
  fun_prop
open _root_.P2Mf6bd8d28 renaming h475 → _Pd7
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h465 → _Pcx
open _root_.P2Mf6bd8d28 renaming h466 → _Pcy
open _root_.P2Mf6bd8d28 renaming h467 → _Pcz
open _root_.P2Mf6bd8d28 renaming h468 → _Pd0
open _root_.P2Mf6bd8d28 renaming h469 → _Pd1
open _root_.P2Mf6bd8d28 renaming h470 → _Pd2
open _root_.P2Mf6bd8d28 renaming h471 → _Pd3
open _root_.P2Mf6bd8d28 renaming h472 → _Pd4
open _root_.P2Mf6bd8d28 renaming h475 → _Pd7
end
open _root_.P2Mf6bd8d28 renaming h465 → _Pcx
open _root_.P2Mf6bd8d28 renaming h466 → _Pcy
open _root_.P2Mf6bd8d28 renaming h467 → _Pcz
open _root_.P2Mf6bd8d28 renaming h468 → _Pd0
open _root_.P2Mf6bd8d28 renaming h469 → _Pd1
open _root_.P2Mf6bd8d28 renaming h470 → _Pd2
open _root_.P2Mf6bd8d28 renaming h471 → _Pd3
open _root_.P2Mf6bd8d28 renaming h472 → _Pd4
open _root_.P2Mf6bd8d28 renaming h475 → _Pd7
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2Boolean.RPN
theorem _root_.P2Mf6bd8d28.h544 (start : ℕ) (source : Bool × ℕ)
    (h : source.1=true → source.2<start) : (_root_.InfoLossLAR.WorstCase.registerLoadOp source).Valid start := by
  cases hs : source.1
  · simp [_root_.InfoLossLAR.WorstCase.registerLoadOp,hs,_root_.InfoLossLAR.WorstCase.BooleanOp.Valid,_root_.InfoLossLAR.WorstCase.BooleanOp.sources]
  · simpa [_root_.InfoLossLAR.WorstCase.registerLoadOp,hs,_root_.InfoLossLAR.WorstCase.BooleanOp.Valid,_root_.InfoLossLAR.WorstCase.BooleanOp.sources] using h hs
open _root_.P2Mf6bd8d28 renaming h544 → _Pf4
theorem _root_.P2Mf6bd8d28.h546 (start : ℕ) (sources : List (Bool × ℕ))
    (h : ∀ source∈sources,source.1=true → source.2<start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (_root_.InfoLossLAR.WorstCase.registerLoadOps sources) := by
  induction sources generalizing start with
  | nil => trivial
  | cons source rest ih =>
    change (_root_.InfoLossLAR.WorstCase.registerLoadOp source).Valid start ∧ _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid (start+1) (_root_.InfoLossLAR.WorstCase.registerLoadOps rest)
    refine ⟨_Pf4 start source (h source (by simp)),?_⟩
    apply ih (start+1)
    intro other ho ht
    exact (h other (by simp [ho]) ht).trans (by omega)
open _root_.P2Mf6bd8d28 renaming h546 → _Pf6
theorem _root_.P2Mf6bd8d28.h545 (source : Bool × ℕ) (state : ℕ → Bool) :
    (_root_.InfoLossLAR.WorstCase.registerLoadOp source).eval state=_root_.InfoLossLAR.WorstCase.registerLoadValue source state := by
  cases hs : source.1 <;> simp [_root_.InfoLossLAR.WorstCase.registerLoadOp,_root_.InfoLossLAR.WorstCase.registerLoadValue,_root_.InfoLossLAR.WorstCase.BooleanOp.eval,hs]
open _root_.P2Mf6bd8d28 renaming h545 → _Pf5
theorem _root_.P2Mf6bd8d28.h547 (start : ℕ) (sources : List (Bool × ℕ))
    (h : ∀ source∈sources,source.1=true → source.2<start) (state : ℕ → Bool)
    (index : ℕ) (hi : index<sources.length) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run start (_root_.InfoLossLAR.WorstCase.registerLoadOps sources) state (start+index)=
      _root_.InfoLossLAR.WorstCase.registerLoadValue sources[index] state := by
  induction sources generalizing start index state with
  | nil => simp at hi
  | cons source rest ih =>
    cases index with
    | zero =>
      change _root_.InfoLossLAR.WorstCase.BooleanProgram.run (start+1) (_root_.InfoLossLAR.WorstCase.registerLoadOps rest)
        ((_root_.InfoLossLAR.WorstCase.registerLoadOp source).assign start state) (start+0)=_
      rw [_P47 _ _ _ _ (by omega)]
      simp only [Nat.add_zero,_root_.InfoLossLAR.WorstCase.BooleanOp.assign,Function.update_self,List.getElem_cons_zero,_Pf5]
    | succ index =>
      have hindex : index<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      change _root_.InfoLossLAR.WorstCase.BooleanProgram.run (start+1) (_root_.InfoLossLAR.WorstCase.registerLoadOps rest)
        ((_root_.InfoLossLAR.WorstCase.registerLoadOp source).assign start state) (start+(index+1))=_
      rw [show start+(index+1)=(start+1)+index by omega,
        ih (start+1) (fun other ho ht => (h other (by simp [ho]) ht).trans (by omega)) _ index hindex]
      simp only [List.getElem_cons_succ,_root_.InfoLossLAR.WorstCase.registerLoadValue]
      cases ht : rest[index].1
      · simp [ht]
      · have hb := h rest[index] (by simp) ht
        simp only [ht,ite_true,_root_.InfoLossLAR.WorstCase.BooleanOp.assign]
        exact Function.update_of_ne (by omega) _ _
open _root_.P2Mf6bd8d28 renaming h547 → _Pf7
@[fun_prop] theorem _root_.P2Mf6bd8d28.h543 : Poly _root_.InfoLossLAR.WorstCase.registerLoadNode := by
  unfold _root_.InfoLossLAR.WorstCase.registerLoadNode
  fun_prop
open _root_.P2Mf6bd8d28 renaming h543 → _Pf3
theorem _root_.P2Mf6bd8d28.h542 (source : Bool × ℕ) : _root_.InfoLossLAR.WorstCase.registerLoadNode source=_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node (_root_.InfoLossLAR.WorstCase.registerLoadOp source) := by
  cases hs : source.1 <;> simp [_root_.InfoLossLAR.WorstCase.registerLoadNode,_root_.InfoLossLAR.WorstCase.registerLoadOp,_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node,hs]
open _root_.P2Mf6bd8d28 renaming h542 → _Pf2
@[fun_prop] theorem _root_.P2Mf6bd8d28.h541 :
    Poly (fun x : List Unit × (ℕ × List (Bool × ℕ)) => _root_.InfoLossLAR.WorstCase.registerLoadGateWords x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.registerLoadGateWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h541 → _Pf1
theorem _root_.P2Mf6bd8d28.h540 {total : ℕ} (slots : List Unit) (start : ℕ)
    (sources : List (Bool × ℕ)) (h : ∀ source∈sources,source.1=true → source.2<start)
    (hn : start+sources.length ≤ total) (hs : start+sources.length ≤ slots.length) :
    _root_.InfoLossLAR.WorstCase.registerLoadGateWords slots start sources=
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.registerLoadOps sources)
        (by simpa only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length] using hn)).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  unfold _root_.InfoLossLAR.WorstCase.registerLoadGateWords
  have he : sources.map _root_.InfoLossLAR.WorstCase.registerLoadNode=(_root_.InfoLossLAR.WorstCase.registerLoadOps sources).map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node := by
    change sources.map _root_.InfoLossLAR.WorstCase.registerLoadNode=(sources.map _root_.InfoLossLAR.WorstCase.registerLoadOp).map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node
    rw [List.map_map]
    exact List.map_congr_left (fun source _ => _Pf2 source)
  rw [he]
  exact _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWords_gates slots start (_root_.InfoLossLAR.WorstCase.registerLoadOps sources)
    (by simpa only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length] using hn) (_Pf6 start sources h)
    (by simpa only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length] using hs)
open _root_.P2Mf6bd8d28 renaming h540 → _Pf0
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h540 → _Pf0
open _root_.P2Mf6bd8d28 renaming h541 → _Pf1
open _root_.P2Mf6bd8d28 renaming h542 → _Pf2
open _root_.P2Mf6bd8d28 renaming h543 → _Pf3
open _root_.P2Mf6bd8d28 renaming h544 → _Pf4
open _root_.P2Mf6bd8d28 renaming h545 → _Pf5
open _root_.P2Mf6bd8d28 renaming h546 → _Pf6
open _root_.P2Mf6bd8d28 renaming h547 → _Pf7
end
open _root_.P2Mf6bd8d28 renaming h540 → _Pf0
open _root_.P2Mf6bd8d28 renaming h541 → _Pf1
open _root_.P2Mf6bd8d28 renaming h542 → _Pf2
open _root_.P2Mf6bd8d28 renaming h543 → _Pf3
open _root_.P2Mf6bd8d28 renaming h544 → _Pf4
open _root_.P2Mf6bd8d28 renaming h545 → _Pf5
open _root_.P2Mf6bd8d28 renaming h546 → _Pf6
open _root_.P2Mf6bd8d28 renaming h547 → _Pf7
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h582 : Poly _root_.InfoLossLAR.WorstCase.unaryPayload := by
  unfold _root_.InfoLossLAR.WorstCase.unaryPayload
  exact Poly.comp parser_take_poly (Poly.pair Poly.identity inputWidth_poly)
open _root_.P2Mf6bd8d28 renaming h582 → _Pg6
@[fun_prop] theorem _root_.P2Mf6bd8d28.h571 : Poly (fun input : Str × Str => _root_.InfoLossLAR.WorstCase.shiftWireWord input.1 input.2) := by
  unfold _root_.InfoLossLAR.WorstCase.shiftWireWord
  fun_prop
open _root_.P2Mf6bd8d28 renaming h571 → _Pfv
@[fun_prop] theorem _root_.P2Mf6bd8d28.h569 : Poly (fun input : Str × Str => _root_.InfoLossLAR.WorstCase.shiftInstructionWord input.1 input.2) := by
  unfold _root_.InfoLossLAR.WorstCase.shiftInstructionWord
  fun_prop
open _root_.P2Mf6bd8d28 renaming h569 → _Pft
theorem _root_.P2Mf6bd8d28.h568 {n : ℕ} (prior : Str) (gate : Instr n) :
    _root_.InfoLossLAR.WorstCase.shiftInstructionWord prior (encInstr gate)=encInstr (_root_.InfoLossLAR.WorstCase.rightInstruction (n := prior.length) gate) := by
  cases gate <;>
    simp only [encInstr,List.append_assoc,_root_.InfoLossLAR.WorstCase.shiftInstructionWord,_root_.Integration9_9.TM2PlatformSerialization.readUnary_append,_root_.InfoLossLAR.WorstCase.emitter_width_append,
      _root_.InfoLossLAR.WorstCase.unaryPayload_encNat,_root_.InfoLossLAR.WorstCase.unaryPayload_number,_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,List.length_append,unary,List.length_replicate,
      _root_.InfoLossLAR.WorstCase.rightInstruction,Fin.val_natAdd] <;> norm_num <;> rfl
open _root_.P2Mf6bd8d28 renaming h568 → _Pfs
@[fun_prop] theorem _root_.P2Mf6bd8d28.h564 :
    Poly (fun input : Str × List (List Str) => _root_.InfoLossLAR.WorstCase.shiftCircuitWords input.1 input.2) := by
  have hg : Poly (fun x : ((Str × List (List Str)) × List Str) × Str =>
      _root_.InfoLossLAR.WorstCase.shiftInstructionWord x.1.1.1 x.2) :=
    Poly.comp (f := fun p : Str × Str => _root_.InfoLossLAR.WorstCase.shiftInstructionWord p.1 p.2)
      (g := fun x : ((Str × List (List Str)) × List Str) × Str => (x.1.1.1,x.2))
      _Pft (by fun_prop)
  have hl : Poly (fun x : (Str × List (List Str)) × List Str =>
      x.2.map (_root_.InfoLossLAR.WorstCase.shiftInstructionWord x.1.1)) := Poly.list_map hg Poly.snd
  unfold _root_.InfoLossLAR.WorstCase.shiftCircuitWords
  exact Poly.list_map hl Poly.snd
open _root_.P2Mf6bd8d28 renaming h564 → _Pfo
theorem _root_.P2Mf6bd8d28.h562 {n : ℕ} (prior : Str) (circuit : Layered n) :
    _root_.InfoLossLAR.WorstCase.shiftCircuitWords prior (circuit.map (List.map encInstr))=
      (_root_.InfoLossLAR.WorstCase.rightCircuit (n := prior.length) circuit).map (List.map encInstr) := by
  simp only [_root_.InfoLossLAR.WorstCase.shiftCircuitWords,_root_.InfoLossLAR.WorstCase.rightCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  exact _Pfs prior gate
open _root_.P2Mf6bd8d28 renaming h562 → _Pfm
@[fun_prop] theorem _root_.P2Mf6bd8d28.h527 : Poly _root_.InfoLossLAR.WorstCase.readFamilyFrame := by
  unfold _root_.InfoLossLAR.WorstCase.readFamilyFrame
  fun_prop
open _root_.P2Mf6bd8d28 renaming h527 → _Pen
@[fun_prop] theorem _root_.P2Mf6bd8d28.h501 : Poly _root_.InfoLossLAR.WorstCase.precedingWireSlots := by
  unfold _root_.InfoLossLAR.WorstCase.precedingWireSlots
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.comp parser_take_poly Poly.identity
open _root_.P2Mf6bd8d28 renaming h501 → _Pdx
@[fun_prop] theorem _root_.P2Mf6bd8d28.h368 : Poly _root_.InfoLossLAR.WorstCase.bundleCircuitWordLayers := by
  unfold _root_.InfoLossLAR.WorstCase.bundleCircuitWordLayers
  apply Poly.list_flatMap
  · exact Poly.comp _Pfo
      (Poly.pair _Pdx (by fun_prop))
  · exact Poly.list_indices
open _root_.P2Mf6bd8d28 renaming h368 → _Pa8
@[fun_prop] theorem _root_.P2Mf6bd8d28.h371 : Poly _root_.InfoLossLAR.WorstCase.bundleOutputWords := by
  unfold _root_.InfoLossLAR.WorstCase.bundleOutputWords
  apply Poly.list_map
  · exact Poly.comp _Pfv (Poly.pair _Pdx (by fun_prop))
  · exact Poly.list_indices
open _root_.P2Mf6bd8d28 renaming h371 → _Pab
private theorem _root_.P2Mf6bd8d28.h865 (number : ℕ) : _root_.Integration9_9.TM2PlatformSerialization.readUnary (encNat number)=(encNat number,[]) := by
  simpa only [List.append_nil] using _root_.Integration9_9.TM2PlatformSerialization.readUnary_append number []
open _root_.P2Mf6bd8d28 renaming h865 → _Po1
theorem _root_.P2Mf6bd8d28.h570 (prior xs : Str) :
    _root_.InfoLossLAR.WorstCase.shiftInstructionWord prior xs=
      encNat (inputWidth xs)++encNat (prior.length+inputWidth (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)++
        (if inputWidth xs=4 then
          encNat (prior.length+inputWidth (_root_.Integration9_9.TM2PlatformSerialization.readUnary (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2).2) else []) := by
  unfold _root_.InfoLossLAR.WorstCase.shiftInstructionWord
  simp only [_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,List.length_append,_root_.InfoLossLAR.WorstCase.unaryPayload_length]
  split_ifs <;> simp
open _root_.P2Mf6bd8d28 renaming h570 → _Pfu
theorem _root_.P2Mf6bd8d28.h566 (prior : Str) (tag first second : ℕ) :
    _root_.InfoLossLAR.WorstCase.shiftInstructionWord prior (encNat tag++encNat first++(if tag=4 then encNat second else []))=
      encNat tag++encNat (prior.length+first)++(if tag=4 then encNat (prior.length+second) else []) := by
  rw [_Pfu]
  by_cases h : tag=4 <;>
    simp [h,List.append_assoc,_root_.Integration9_9.TM2PlatformSerialization.readUnary_append,_root_.InfoLossLAR.WorstCase.emitter_width_append,_root_.InfoLossLAR.WorstCase.emitter_width_number,_Po1]
open _root_.P2Mf6bd8d28 renaming h566 → _Pfq
theorem _root_.P2Mf6bd8d28.h567 (first second xs : Str) :
    _root_.InfoLossLAR.WorstCase.shiftInstructionWord first (_root_.InfoLossLAR.WorstCase.shiftInstructionWord second xs)=_root_.InfoLossLAR.WorstCase.shiftInstructionWord (first++second) xs := by
  rw [_Pfu second xs,_Pfq,_Pfu]
  simp only [List.length_append,Nat.add_assoc]
open _root_.P2Mf6bd8d28 renaming h567 → _Pfr
theorem _root_.P2Mf6bd8d28.h561 (first second : Str) (layers : List (List Str)) :
    _root_.InfoLossLAR.WorstCase.shiftCircuitWords first (_root_.InfoLossLAR.WorstCase.shiftCircuitWords second layers)=_root_.InfoLossLAR.WorstCase.shiftCircuitWords (first++second) layers := by
  simp only [_root_.InfoLossLAR.WorstCase.shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro word _
  exact _Pfr first second word
open _root_.P2Mf6bd8d28 renaming h561 → _Pfl
theorem _root_.P2Mf6bd8d28.h563 {α : Type*} (prior : Str) (values : List α) (layers : α → List (List Str)) :
    _root_.InfoLossLAR.WorstCase.shiftCircuitWords prior (values.flatMap layers)=values.flatMap (fun value => _root_.InfoLossLAR.WorstCase.shiftCircuitWords prior (layers value)) := by
  simp only [_root_.InfoLossLAR.WorstCase.shiftCircuitWords,List.map_flatMap]
open _root_.P2Mf6bd8d28 renaming h563 → _Pfn
theorem _root_.P2Mf6bd8d28.h565 {n : ℕ} (circuit : Layered n) :
    _root_.InfoLossLAR.WorstCase.shiftCircuitWords [] (circuit.map (List.map encInstr))=circuit.map (List.map encInstr) := by
  simp only [_root_.InfoLossLAR.WorstCase.shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  rw [_Pfs]
  cases gate <;> simp [_root_.InfoLossLAR.WorstCase.rightInstruction,encInstr]
open _root_.P2Mf6bd8d28 renaming h565 → _Pfp
theorem _root_.P2Mf6bd8d28.h366 (frame : _root_.InfoLossLAR.WorstCase.PhysicalFrameWords) (frames : List _root_.InfoLossLAR.WorstCase.PhysicalFrameWords) :
    _root_.InfoLossLAR.WorstCase.bundleCircuitWordLayers (frame::frames)=
      _root_.InfoLossLAR.WorstCase.shiftCircuitWords [] frame.2.2++_root_.InfoLossLAR.WorstCase.shiftCircuitWords frame.1 (_root_.InfoLossLAR.WorstCase.bundleCircuitWordLayers frames) := by
  unfold _root_.InfoLossLAR.WorstCase.bundleCircuitWordLayers
  simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
    List.getElem?_cons_zero,Option.getD_some,_root_.InfoLossLAR.WorstCase.precedingWireSlots,List.take_zero,List.flatMap_nil]
  rw [_Pfn]
  apply congrArg (fun tail => _root_.InfoLossLAR.WorstCase.shiftCircuitWords [] frame.2.2++tail)
  apply List.flatMap_congr
  intro index _
  simp only [List.getElem?_cons_succ,_root_.InfoLossLAR.WorstCase.precedingWireSlots,List.take_succ_cons,List.flatMap_cons]
  exact (_Pfl frame.1 _ _).symm
open _root_.P2Mf6bd8d28 renaming h366 → _Pa6
private theorem _root_.P2Mf6bd8d28.h866 {n : ℕ} (first second : ℕ) (h : first=second) (circuit : Layered n) :
    (_root_.InfoLossLAR.WorstCase.rightCircuit (n := first) circuit).map (List.map encInstr)=
      (_root_.InfoLossLAR.WorstCase.rightCircuit (n := second) circuit).map (List.map encInstr) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h866 → _Po2
theorem _root_.P2Mf6bd8d28.h367 (blocks : List _root_.InfoLossLAR.WorstCase.QuantumBlock) :
    _root_.InfoLossLAR.WorstCase.bundleCircuitWordLayers (blocks.map _root_.InfoLossLAR.WorstCase.blockFrameWords)=
      (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks).map (List.map encInstr) := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    rw [List.map_cons,_Pa6]
    simp only [_root_.InfoLossLAR.WorstCase.blockFrameWords,_Pfp]
    have hlen : (unary block.wires).length=block.wires := by simp [unary]
    have hshift : _root_.InfoLossLAR.WorstCase.shiftCircuitWords (unary block.wires) ((_root_.InfoLossLAR.WorstCase.bundleCircuit blocks).map (List.map encInstr))=
        (_root_.InfoLossLAR.WorstCase.rightCircuit (n := block.wires) (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)).map (List.map encInstr) := by
      exact (_Pfm (unary block.wires) (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks)).trans
        (_Po2 _ _ hlen _)
    rw [ih,hshift]
    simp only [_root_.InfoLossLAR.WorstCase.bundleCircuit,_root_.InfoLossLAR.WorstCase.bundleWidth,List.map_append,_root_.InfoLossLAR.WorstCase.leftCircuit,List.map_map,Function.comp_def,
      _root_.InfoLossLAR.WorstCase.leftInstruction_encInstr]
open _root_.P2Mf6bd8d28 renaming h367 → _Pa7
@[fun_prop] theorem _root_.P2Mf6bd8d28.h415 : Poly _root_.InfoLossLAR.WorstCase.emitDOutputs := by
  unfold _root_.InfoLossLAR.WorstCase.emitDOutputs
  exact Poly.comp _Pab (Poly.list_map (Poly.comp _Pen Poly.snd) Poly.identity)
open _root_.P2Mf6bd8d28 renaming h415 → _Pbj
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h366 → _Pa6
open _root_.P2Mf6bd8d28 renaming h367 → _Pa7
open _root_.P2Mf6bd8d28 renaming h368 → _Pa8
open _root_.P2Mf6bd8d28 renaming h371 → _Pab
open _root_.P2Mf6bd8d28 renaming h415 → _Pbj
open _root_.P2Mf6bd8d28 renaming h501 → _Pdx
open _root_.P2Mf6bd8d28 renaming h527 → _Pen
open _root_.P2Mf6bd8d28 renaming h561 → _Pfl
open _root_.P2Mf6bd8d28 renaming h562 → _Pfm
open _root_.P2Mf6bd8d28 renaming h563 → _Pfn
open _root_.P2Mf6bd8d28 renaming h564 → _Pfo
open _root_.P2Mf6bd8d28 renaming h565 → _Pfp
open _root_.P2Mf6bd8d28 renaming h566 → _Pfq
open _root_.P2Mf6bd8d28 renaming h567 → _Pfr
open _root_.P2Mf6bd8d28 renaming h568 → _Pfs
open _root_.P2Mf6bd8d28 renaming h569 → _Pft
open _root_.P2Mf6bd8d28 renaming h570 → _Pfu
open _root_.P2Mf6bd8d28 renaming h571 → _Pfv
open _root_.P2Mf6bd8d28 renaming h582 → _Pg6
open _root_.P2Mf6bd8d28 renaming h865 → _Po1
open _root_.P2Mf6bd8d28 renaming h866 → _Po2
end
open _root_.P2Mf6bd8d28 renaming h366 → _Pa6
open _root_.P2Mf6bd8d28 renaming h367 → _Pa7
open _root_.P2Mf6bd8d28 renaming h368 → _Pa8
open _root_.P2Mf6bd8d28 renaming h371 → _Pab
open _root_.P2Mf6bd8d28 renaming h415 → _Pbj
open _root_.P2Mf6bd8d28 renaming h501 → _Pdx
open _root_.P2Mf6bd8d28 renaming h527 → _Pen
open _root_.P2Mf6bd8d28 renaming h561 → _Pfl
open _root_.P2Mf6bd8d28 renaming h562 → _Pfm
open _root_.P2Mf6bd8d28 renaming h563 → _Pfn
open _root_.P2Mf6bd8d28 renaming h564 → _Pfo
open _root_.P2Mf6bd8d28 renaming h565 → _Pfp
open _root_.P2Mf6bd8d28 renaming h566 → _Pfq
open _root_.P2Mf6bd8d28 renaming h567 → _Pfr
open _root_.P2Mf6bd8d28 renaming h568 → _Pfs
open _root_.P2Mf6bd8d28 renaming h569 → _Pft
open _root_.P2Mf6bd8d28 renaming h570 → _Pfu
open _root_.P2Mf6bd8d28 renaming h571 → _Pfv
open _root_.P2Mf6bd8d28 renaming h582 → _Pg6
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity Turing Function Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open Integration9_9 Integration9_9.TM2StockLists QMCNumericRuntime
theorem _root_.P2Mf6bd8d28.h373 (budget : Polynomial ℕ) (input : Str) :
    _root_.InfoLossLAR.WorstCase.bundleRequests budget input = List.ofFn (fun index : Fin (budget.eval input.length+1) => unary index.val) := by
  apply List.ext_getElem
  · simp [_root_.InfoLossLAR.WorstCase.bundleRequests,_root_.InfoLossLAR.WorstCase.bundleRequestsFromSlots]
  · intro i hi hj
    simp only [_root_.InfoLossLAR.WorstCase.bundleRequests,_root_.InfoLossLAR.WorstCase.bundleRequestsFromSlots,List.length_map,List.length_range,
      List.length_replicate] at hi
    simp only [_root_.InfoLossLAR.WorstCase.bundleRequests,_root_.InfoLossLAR.WorstCase.bundleRequestsFromSlots,List.getElem_map,List.getElem_range,
      List.take_replicate,List.getElem_ofFn,List.map_replicate,unary]
    rw [Nat.min_eq_left (by omega)]
open _root_.P2Mf6bd8d28 renaming h373 → _Pad
theorem _root_.P2Mf6bd8d28.h429 (D : Family) (generator : Str → Str)
    (h : ∀ n,generator (unary n)=encFamilyAt D n) (budget : Polynomial ℕ) (input : Str) :
    _root_.InfoLossLAR.WorstCase.generatedBundleDescriptions generator budget input=_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (budget.eval input.length) := by
  rw [_root_.InfoLossLAR.WorstCase.generatedBundleDescriptions,_Pad]
  simp only [List.map_ofFn,Function.comp_def,h,_root_.InfoLossLAR.WorstCase.describedQueryBlocks]
open _root_.P2Mf6bd8d28 renaming h429 → _Pbx
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h373 → _Pad
open _root_.P2Mf6bd8d28 renaming h429 → _Pbx
end
open _root_.P2Mf6bd8d28 renaming h373 → _Pad
open _root_.P2Mf6bd8d28 renaming h429 → _Pbx
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime
@[fun_prop] theorem _root_.P2Mf6bd8d28.h402 :
    Poly (fun x : List ℕ × (List Unit × List Unit) => _root_.InfoLossLAR.WorstCase.dBlockLoadSources x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.dBlockLoadSources
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun x : List ℕ × (List Unit × List Unit) => x.2.2) Poly.list_indices (by fun_prop)
open _root_.P2Mf6bd8d28 renaming h402 → _Pb6
theorem _root_.P2Mf6bd8d28.h403 (start : ℕ) (querySources : List ℕ) (request slots : List Unit)
    (hq : request.length ≤ querySources.length)
    (hs : ∀ address∈querySources,address  <  start) :
    ∀ source∈_root_.InfoLossLAR.WorstCase.dBlockLoadSources querySources request slots,source.1=true → source.2  <  start := by
  intro source hsource ht
  obtain ⟨index,hi,he⟩ := List.mem_map.mp hsource
  rw [←he] at ht ⊢
  have hj : index  <  request.length := by simpa using ht
  have hindex : index  <  querySources.length := hj.trans_le hq
  simpa only [List.getElem?_eq_getElem hindex,Option.getD_some] using
    hs querySources[index] (List.getElem_mem hindex)
open _root_.P2Mf6bd8d28 renaming h403 → _Pb7
@[fun_prop] theorem _root_.P2Mf6bd8d28.h406 :
    Poly (fun x : List ℕ × List (Str × Str) => _root_.InfoLossLAR.WorstCase.dBundleLoadSources x.1 x.2) := by
  unfold _root_.InfoLossLAR.WorstCase.dBundleLoadSources
  fun_prop
open _root_.P2Mf6bd8d28 renaming h406 → _Pba
theorem _root_.P2Mf6bd8d28.h407 (start : ℕ) (querySources : List ℕ) (descriptions : List (Str × Str))
    (hq : ∀ description∈descriptions,description.1.length ≤ querySources.length)
    (hs : ∀ address∈querySources,address  <  start) :
    ∀ source∈_root_.InfoLossLAR.WorstCase.dBundleLoadSources querySources descriptions,source.1=true → source.2  <  start := by
  intro source hsource ht
  obtain ⟨description,hd,hmem⟩ := List.mem_flatMap.mp hsource
  exact _Pb7 start querySources _ _
    (by simpa only [List.length_map] using hq description hd) hs source hmem ht
open _root_.P2Mf6bd8d28 renaming h407 → _Pbb
theorem _root_.P2Mf6bd8d28.h410 (D : Family) (maximum : ℕ) :
    ∀ description∈_root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum,description.1.length ≤ maximum := by
  intro description hd
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hd
  simp only [unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h410 → _Pbe
theorem _root_.P2Mf6bd8d28.h405 (start : ℕ) (D : Family) (maximum : ℕ) (querySources : List ℕ)
    (hl : querySources.length=maximum) (hs : ∀ address∈querySources,address < start) :
    ∀ source∈_root_.InfoLossLAR.WorstCase.dBundleLoadSources querySources (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum),
      source.1=true → source.2 < start :=
  _Pbb start querySources _
    (fun description hd => (_Pbe D maximum description hd).trans hl.ge) hs
open _root_.P2Mf6bd8d28 renaming h405 → _Pb9
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h402 → _Pb6
open _root_.P2Mf6bd8d28 renaming h403 → _Pb7
open _root_.P2Mf6bd8d28 renaming h405 → _Pb9
open _root_.P2Mf6bd8d28 renaming h406 → _Pba
open _root_.P2Mf6bd8d28 renaming h407 → _Pbb
open _root_.P2Mf6bd8d28 renaming h410 → _Pbe
end
open _root_.P2Mf6bd8d28 renaming h402 → _Pb6
open _root_.P2Mf6bd8d28 renaming h403 → _Pb7
open _root_.P2Mf6bd8d28 renaming h405 → _Pb9
open _root_.P2Mf6bd8d28 renaming h406 → _Pba
open _root_.P2Mf6bd8d28 renaming h407 → _Pbb
open _root_.P2Mf6bd8d28 renaming h410 → _Pbe
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
@[fun_prop] theorem _root_.P2Mf6bd8d28.h748 (coins : Polynomial ℕ) : Poly (_root_.Integration9_9.LARCoinLayout.queryWireRequest coins) := by
  have hs : Poly (fun word : Str => List.replicate ((coins+X).eval (word.map (fun _ => ())).length) ()) :=
    Poly.comp (f := fun slots : List Unit => List.replicate ((coins+X).eval slots.length) ())
      (g := fun word : Str => word.map (fun _ => ()))
      (_root_.Integration9_9.TM2PolynomialBudget.polynomialSlots_poly (coins+X)) (by fun_prop)
  exact Poly.comp (f := fun slots : List Unit => slots.map (fun _ => true))
    (g := fun word : Str => List.replicate ((coins+X).eval (word.map (fun _ => ())).length) ())
    (by fun_prop) hs
open _root_.P2Mf6bd8d28 renaming h748 → _Pks
theorem _root_.P2Mf6bd8d28.h749 (coins : Polynomial ℕ) (n : ℕ) :
    _root_.Integration9_9.LARCoinLayout.queryWireRequest coins (unary n)=unary (coins.eval n+n) := by
  simp only [_root_.Integration9_9.LARCoinLayout.queryWireRequest,List.length_map,unary,List.length_replicate,eval_add,eval_X,List.map_replicate]
open _root_.P2Mf6bd8d28 renaming h749 → _Pkt
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h748 → _Pks
open _root_.P2Mf6bd8d28 renaming h749 → _Pkt
end
end
open _root_.P2Mf6bd8d28 renaming h748 → _Pks
open _root_.P2Mf6bd8d28 renaming h749 → _Pkt
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime
theorem _root_.P2Mf6bd8d28.h742 (D : Family) (maximum : ℕ) (query : Str) :
    ∀ address∈(_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum)).map inputWidth,
      address < _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query) := by
  intro address ha
  obtain ⟨token,ht,rfl⟩ := List.mem_map.mp ha
  rw [_root_.InfoLossLAR.WorstCase.emitDOutputs_correct D maximum query] at ht
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp ht
  have hn (number : ℕ) : inputWidth (encNat number)=number := by
    rw [←_root_.InfoLossLAR.WorstCase.unaryPayload_length,_root_.InfoLossLAR.WorstCase.unaryPayload_number]
    simp only [unary,List.length_replicate]
  rw [hn]
  exact (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query) index).isLt
open _root_.P2Mf6bd8d28 renaming h742 → _Pkm
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h742 → _Pkm
end
end
open _root_.P2Mf6bd8d28 renaming h742 → _Pkm
namespace Integration9_9.LARCoinLayout.queryFlagAddresses
end Integration9_9.LARCoinLayout.queryFlagAddresses
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
theorem _root_.P2Mf6bd8d28.h231 {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (index : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length)) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits P word (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary word.length) index.val)=
      decide (some true=(f word)[index.val]?) := by
  rw [_P6d]
  exact (_root_.InfoLossLAR.WorstCase.selectorBitsExtension_get (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.outputWire P word.length index (some true))).trans
    (_P6j P word index (some true))
open _root_.P2Mf6bd8d28 renaming h231 → _P6f
theorem _root_.P2Mf6bd8d28.h225 {f : Str → Str} (P : PolyProgram id id f)
    (word : Str) (slots : List Unit) (offset index : ℕ) (hi : index < slots.length) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange P word slots offset)[index]'(by simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange,List.length_map,List.length_range] using hi)=
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P word (offset+index) := by
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange,List.getElem_map,List.getElem_range]
open _root_.P2Mf6bd8d28 renaming h225 → _P69
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h225 → _P69
open _root_.P2Mf6bd8d28 renaming h231 → _P6f
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
open LARRankOneMachine
end Integration9_9.LARCoinLayout
end
end
open _root_.P2Mf6bd8d28 renaming h225 → _P69
open _root_.P2Mf6bd8d28 renaming h231 → _P6f
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open LARRankOneMachine
attribute [local irreducible] coinFirstPre queryWireSlots
theorem _root_.P2Mf6bd8d28.h728 (coins padding : Polynomial ℕ) (fallback word : Str) :
    (_root_.Integration9_9.LARCoinLayout.bodyQueryOutput coins padding fallback word).length=2*padding.eval word.length+1 := by
  rw [_root_.Integration9_9.LARCoinLayout.bodyQueryOutput,_root_.Integration9_9.LARCoinLayout.encodeQueryOutput_length,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length]
open _root_.P2Mf6bd8d28 renaming h728 → _Pk8
theorem _root_.P2Mf6bd8d28.h726 (coins : Polynomial ℕ) (fallback word : Str) :
    (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length ≤ (_root_.Integration9_9.LARCoinLayout.bodyQueryBudget coins fallback).eval word.length :=
  (_root_.Integration9_9.LARCoinLayout.coinFirstPreProgram coins fallback).length_bound word
open _root_.P2Mf6bd8d28 renaming h726 → _Pk6
theorem _root_.P2Mf6bd8d28.h727 (coins padding : Polynomial ℕ) (fallback : Str) (n : ℕ) :
    2*padding.eval n+1 < _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n := by
  have h := _P63 (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) (unary n)
  change (_root_.Integration9_9.LARCoinLayout.bodyQueryOutput coins padding fallback (unary n)).length < _ at h
  rw [_Pk8] at h
  simpa only [unary,List.length_replicate] using h
open _root_.P2Mf6bd8d28 renaming h727 → _Pk7
theorem _root_.P2Mf6bd8d28.h715 (coins padding : Polynomial ℕ) (fallback word : Str) :
    (_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses coins padding fallback word).length=padding.eval word.length := by
  simp only [_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses,_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange,List.length_map,List.length_range,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length]
open _root_.P2Mf6bd8d28 renaming h715 → _Pjv
theorem _root_.P2Mf6bd8d28.h716 (coins padding : Polynomial ℕ) (fallback : Str) (n : ℕ) :
    ∀ address∈_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses coins padding fallback (unary n),
      address < n+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n).ops.length+1) := by
  intro address ha
  apply _P68 (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n
    (_root_.Integration9_9.LARCoinLayout.queryWireSlots padding (unary n)) ((_root_.Integration9_9.LARCoinLayout.queryWireSlots padding (unary n)).length+1) _ address ha
  have h := _Pk7 coins padding fallback n
  simp only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h716 → _Pjw
theorem _root_.P2Mf6bd8d28.h713 (coins padding : Polynomial ℕ) (fallback : Str) (n : ℕ) :
    ∀ address∈_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses coins padding fallback (unary n),
      address < n+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n).ops.length+1) := by
  intro address ha
  apply _P68 (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n
    (_root_.Integration9_9.LARCoinLayout.queryWireSlots padding (unary n)++[()]) 0 _ address ha
  have h := _Pk7 coins padding fallback n
  simp only [zero_add,List.length_append,List.length_singleton,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h713 → _Pjt
theorem _root_.P2Mf6bd8d28.h703 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family) (n : ℕ) :
    ∀ source∈_root_.InfoLossLAR.WorstCase.dBundleLoadSources (_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses coins padding fallback (unary n))
      (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval n)),source.1=true →
        source.2 < n+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n).ops.length+1) :=
  _Pb9 _ D _ _
    (by simp only [_Pjv,unary,List.length_replicate])
    (_Pjw coins padding fallback n)
open _root_.P2Mf6bd8d28 renaming h703 → _Pjj
theorem _root_.P2Mf6bd8d28.h714 (coins padding : Polynomial ℕ) (fallback word : Str)
    (index : ℕ) (hi : index ≤ padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word
      ((_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses coins padding fallback (unary word.length))[index]'(by
        simp only [_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses_length,unary,List.length_replicate]; omega))=
      decide ((_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length=index) := by
  let P := _root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback
  have hcap := _Pk7 coins padding fallback word.length
  let cell : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length) := ⟨index,by dsimp only [P]; omega⟩
  have haddr : (_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses coins padding fallback (unary word.length))[index]'(by
        simp only [_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses_length,unary,List.length_replicate]; omega)=
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary word.length) cell.val := by
    unfold _root_.Integration9_9.LARCoinLayout.bodyFlagAddresses
    rw [_P69 _ _ _ 0 index (by
      simp only [List.length_append,List.length_singleton,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]; omega)]
    simp only [zero_add,P,cell]
  rw [haddr,_P6f]
  change decide (some true=(_root_.Integration9_9.LARCoinLayout.bodyQueryOutput coins padding fallback word)[index]?)=_
  unfold _root_.Integration9_9.LARCoinLayout.bodyQueryOutput
  rw [_Pko _ _ index (by simpa only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length] using hi)]
  by_cases he : (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length=index  <;> simp [he]
open _root_.P2Mf6bd8d28 renaming h714 → _Pju
theorem _root_.P2Mf6bd8d28.h717 (coins padding : Polynomial ℕ) (fallback word : Str)
    (index : ℕ) (hi : index < padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word
      ((_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses coins padding fallback (unary word.length))[index]'(by
        simpa only [_Pjv,unary,List.length_replicate] using hi))=
      ((_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)[index]?).getD false := by
  let P := _root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback
  have hcap := _Pk7 coins padding fallback word.length
  let cell : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length) := ⟨padding.eval word.length+1+index,by dsimp only [P]; omega⟩
  have haddr : (_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses coins padding fallback (unary word.length))[index]'(by
        simpa only [_Pjv,unary,List.length_replicate] using hi)=
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary word.length) cell.val := by
    unfold _root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses
    rw [_P69 _ _ _ _ index (by
      simpa only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate] using hi)]
    simp only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate,cell,P]
  rw [haddr,_P6f]
  change decide (some true=(_root_.Integration9_9.LARCoinLayout.bodyQueryOutput coins padding fallback word)[padding.eval word.length+1+index]?)=_
  have hbit := _Pkn (_root_.Integration9_9.LARCoinLayout.queryWireSlots padding word) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) index
    (by simpa only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length] using hi)
  simp only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length] at hbit
  rw [_root_.Integration9_9.LARCoinLayout.bodyQueryOutput,hbit]
  cases hb : ((_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)[index]?).getD false  <;> simp [hb]
open _root_.P2Mf6bd8d28 renaming h717 → _Pjx
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h703 → _Pjj
open _root_.P2Mf6bd8d28 renaming h713 → _Pjt
open _root_.P2Mf6bd8d28 renaming h714 → _Pju
open _root_.P2Mf6bd8d28 renaming h715 → _Pjv
open _root_.P2Mf6bd8d28 renaming h716 → _Pjw
open _root_.P2Mf6bd8d28 renaming h717 → _Pjx
open _root_.P2Mf6bd8d28 renaming h726 → _Pk6
open _root_.P2Mf6bd8d28 renaming h727 → _Pk7
open _root_.P2Mf6bd8d28 renaming h728 → _Pk8
end
end
open _root_.P2Mf6bd8d28 renaming h703 → _Pjj
open _root_.P2Mf6bd8d28 renaming h713 → _Pjt
open _root_.P2Mf6bd8d28 renaming h714 → _Pju
open _root_.P2Mf6bd8d28 renaming h715 → _Pjv
open _root_.P2Mf6bd8d28 renaming h716 → _Pjw
open _root_.P2Mf6bd8d28 renaming h717 → _Pjx
open _root_.P2Mf6bd8d28 renaming h726 → _Pk6
open _root_.P2Mf6bd8d28 renaming h727 → _Pk7
open _root_.P2Mf6bd8d28 renaming h728 → _Pk8
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime
@[fun_prop] theorem _root_.P2Mf6bd8d28.h433 :
    Poly (fun x : List Unit × List Unit => _root_.InfoLossLAR.WorstCase.inputCopySources x.1 x.2) := by
  have hi : Poly (fun x : List Unit × List Unit => List.range x.2.length) :=
    Poly.comp (f := fun xs : List Unit => List.range xs.length) (g := Prod.snd)
      Poly.list_indices Poly.snd
  have hc : Poly (fun x : List Unit × List Unit => (List.range x.2.length).map (fun i => (true,i))) := by
    apply Poly.list_map
    · exact (by fun_prop : Poly (fun x : (List Unit × List Unit) × ℕ => (true,x.2)))
    · exact hi
  have hz : Poly (fun x : List Unit × List Unit => x.1.map (fun _ => (false,(0 : ℕ)))) := by
    fun_prop
  exact Poly.comp (f := fun x : List (Bool × ℕ) × List (Bool × ℕ) => x.1++x.2)
    (g := fun x : List Unit × List Unit =>
      (x.1.map (fun _ => (false,(0 : ℕ))),(List.range x.2.length).map (fun i => (true,i))))
    Poly.list_append (Poly.pair hz hc)
open _root_.P2Mf6bd8d28 renaming h433 → _Pc1
theorem _root_.P2Mf6bd8d28.h434 (coinSlots inputSlots : List Unit) :
    ∀ source∈_root_.InfoLossLAR.WorstCase.inputCopySources coinSlots inputSlots,source.1=true → source.2 < inputSlots.length := by
  intro source hs ht
  rcases List.mem_append.mp hs with hc|hi
  · obtain ⟨_,_,he⟩ := List.mem_map.mp hc
    cases he
    contradiction
  · obtain ⟨index,hindex,heq⟩ := List.mem_map.mp hi
    rw [←heq]
    exact List.mem_range.mp hindex
open _root_.P2Mf6bd8d28 renaming h434 → _Pc2
theorem _root_.P2Mf6bd8d28.h437 (coinSlots inputSlots : List Unit) (state : ℕ → Bool)
    (index : ℕ) (hi : index < coinSlots.length+inputSlots.length) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run inputSlots.length (_root_.InfoLossLAR.WorstCase.registerLoadOps (_root_.InfoLossLAR.WorstCase.inputCopySources coinSlots inputSlots)) state
      (inputSlots.length+index)=if index < coinSlots.length then false else state (index-coinSlots.length) := by
  rw [_Pf7 inputSlots.length _ (_Pc2 coinSlots inputSlots) state index
    (by simpa only [_root_.InfoLossLAR.WorstCase.inputCopySources_length] using hi)]
  unfold _root_.InfoLossLAR.WorstCase.inputCopySources
  by_cases hc : index < coinSlots.length
  · rw [List.getElem_append_left (show index < (coinSlots.map (fun _ => (false,(0 : ℕ)))).length by simpa using hc)]
    simp [_root_.InfoLossLAR.WorstCase.registerLoadValue,List.getElem_map,hc]
  · have hm : (coinSlots.map (fun _ => (false,0))).length ≤ index := by simp; omega
    rw [List.getElem_append_right hm]
    simp only [List.length_map,List.getElem_map,List.getElem_range,_root_.InfoLossLAR.WorstCase.registerLoadValue,ite_true,if_neg hc]
open _root_.P2Mf6bd8d28 renaming h437 → _Pc5
@[fun_prop] theorem _root_.P2Mf6bd8d28.h432 :
    Poly (fun x : List Unit × (List Unit × List Unit) => _root_.InfoLossLAR.WorstCase.inputCopyGateWords x.1 x.2.1 x.2.2) := by
  unfold _root_.InfoLossLAR.WorstCase.inputCopyGateWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h432 → _Pc0
theorem _root_.P2Mf6bd8d28.h431 {total : ℕ} (slots coinSlots inputSlots : List Unit)
    (hn : inputSlots.length+(coinSlots.length+inputSlots.length) ≤ total)
    (hs : inputSlots.length+(coinSlots.length+inputSlots.length) ≤ slots.length) :
    _root_.InfoLossLAR.WorstCase.inputCopyGateWords slots coinSlots inputSlots=
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates inputSlots.length (_root_.InfoLossLAR.WorstCase.registerLoadOps (_root_.InfoLossLAR.WorstCase.inputCopySources coinSlots inputSlots))
        (by simpa only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length,_root_.InfoLossLAR.WorstCase.inputCopySources_length] using hn)).map _root_.InfoLossLAR.WorstCase.BooleanGate.code :=
  _Pf0 slots inputSlots.length (_root_.InfoLossLAR.WorstCase.inputCopySources coinSlots inputSlots)
    (_Pc2 coinSlots inputSlots)
    (by simpa only [_root_.InfoLossLAR.WorstCase.inputCopySources_length] using hn)
    (by simpa only [_root_.InfoLossLAR.WorstCase.inputCopySources_length] using hs)
open _root_.P2Mf6bd8d28 renaming h431 → _Pbz
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h431 → _Pbz
open _root_.P2Mf6bd8d28 renaming h432 → _Pc0
open _root_.P2Mf6bd8d28 renaming h433 → _Pc1
open _root_.P2Mf6bd8d28 renaming h434 → _Pc2
open _root_.P2Mf6bd8d28 renaming h437 → _Pc5
end
open _root_.P2Mf6bd8d28 renaming h431 → _Pbz
open _root_.P2Mf6bd8d28 renaming h432 → _Pc0
open _root_.P2Mf6bd8d28 renaming h433 → _Pc1
open _root_.P2Mf6bd8d28 renaming h434 → _Pc2
open _root_.P2Mf6bd8d28 renaming h437 → _Pc5
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity TM2Boolean
namespace BooleanProgram
theorem _root_.P2Mf6bd8d28.h149 (start : ℕ) (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp) (state : ℕ → Bool) (index : ℕ)
    (hi : start+ops.length ≤ index) : _root_.InfoLossLAR.WorstCase.BooleanProgram.run start ops state index=state index := by
  induction ops generalizing start state with
  | nil => rfl
  | cons op rest ih =>
    change _root_.InfoLossLAR.WorstCase.BooleanProgram.run (start+1) rest (op.assign start state) index=state index
    rw [ih (start+1) _ (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi)]
    exact Function.update_of_ne (by simp only [List.length_cons] at hi; omega) _ _
open _root_.P2Mf6bd8d28 renaming h149 → _P45
end BooleanProgram
open _root_.P2Mf6bd8d28 renaming h149 → _P45
theorem _root_.P2Mf6bd8d28.h436 (word : Str) (coins index : ℕ) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length
      (_root_.InfoLossLAR.WorstCase.registerLoadOps (_root_.InfoLossLAR.WorstCase.inputCopySources (List.replicate coins ()) (List.replicate word.length ())))
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) index=_root_.InfoLossLAR.WorstCase.inputCopyResult word coins index := by
  by_cases hi : index < word.length
  · rw [_P47 _ _ _ _ hi]
    simp [_root_.InfoLossLAR.WorstCase.inputCopyResult,hi]
  · by_cases hm : index < word.length+coins+word.length
    · have hj : index-word.length < coins+word.length := by omega
      have h := _Pc5 (List.replicate coins ()) (List.replicate word.length ())
        (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) (index-word.length) (by simpa only [List.length_replicate] using hj)
      simp only [List.length_replicate,Nat.add_sub_of_le (by omega : word.length ≤ index)] at h
      rw [h]
      by_cases hc : index < word.length+coins
      · simp only [_root_.InfoLossLAR.WorstCase.inputCopyResult,if_neg hi,if_pos hc,if_pos (by omega : index-word.length < coins)]
      · simp only [_root_.InfoLossLAR.WorstCase.inputCopyResult,if_neg hi,if_neg hc,if_pos hm,if_neg (by omega : ¬index-word.length < coins)]
        rw [Nat.sub_sub]
    · rw [_P45 _ _ _ _ (by
        simp only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length,_root_.InfoLossLAR.WorstCase.inputCopySources_length,List.length_replicate]; omega)]
      rw [_P8o word _ (by omega)]
      simp [_root_.InfoLossLAR.WorstCase.inputCopyResult,hi,hm,show ¬index < word.length+coins by omega]
open _root_.P2Mf6bd8d28 renaming h436 → _Pc4
theorem _root_.P2Mf6bd8d28.h435 (word : Str) (coins extra : ℕ) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates word.length
        (_root_.InfoLossLAR.WorstCase.registerLoadOps (_root_.InfoLossLAR.WorstCase.inputCopySources (List.replicate coins ()) (List.replicate word.length ())))
        (by simp only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length,_root_.InfoLossLAR.WorstCase.inputCopySources_length,List.length_replicate]; omega :
          word.length+(registerLoadOps (inputCopySources (List.replicate coins ())
            (List.replicate word.length ()))).length ≤ word.length+((coins+(word.length+extra))+1)))))
      (basisInput (a := coins+(word.length+extra)) (toBits word))=
        _root_.InfoLossLAR.WorstCase.computationalBasis (fun index : Fin (word.length+((coins+(word.length+extra))+1)) =>
          _root_.InfoLossLAR.WorstCase.inputCopyResult word coins index.val) := by
  rw [_P9k,_P8p]
  have h := _P3y
    (_root_.InfoLossLAR.WorstCase.registerLoadOps (_root_.InfoLossLAR.WorstCase.inputCopySources (List.replicate coins ()) (List.replicate word.length ())))
    (by simp only [_root_.InfoLossLAR.WorstCase.registerLoadOps_length,_root_.InfoLossLAR.WorstCase.inputCopySources_length,List.length_replicate]; omega :
      word.length+(registerLoadOps (inputCopySources (List.replicate coins ())
        (List.replicate word.length ()))).length ≤ word.length+((coins+(word.length+extra))+1))
    (_Pf6 _ _ (by simpa only [List.length_replicate] using
      (_Pc2 (List.replicate coins ()) (List.replicate word.length ())))) (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word)
    (fun index hi _ => _P8o word index hi)
  unfold _root_.InfoLossLAR.WorstCase.computationalBasis
  simpa only [_Pc4] using h
open _root_.P2Mf6bd8d28 renaming h435 → _Pc3
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h149 → _P45
open _root_.P2Mf6bd8d28 renaming h435 → _Pc3
open _root_.P2Mf6bd8d28 renaming h436 → _Pc4
end
open _root_.P2Mf6bd8d28 renaming h149 → _P45
open _root_.P2Mf6bd8d28 renaming h435 → _Pc3
open _root_.P2Mf6bd8d28 renaming h436 → _Pc4
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
theorem _root_.P2Mf6bd8d28.h238 {f : Str → Str} (P : PolyProgram id id f)
    (length : ℕ) (sources : List (Bool × ℕ))
    (hs : ∀ source∈sources,source.1=true → source.2 < length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P length).ops.length+1)) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid length (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps P length sources) := by
  classical
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps,_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append]
  refine ⟨(_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram_valid (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity_pos P length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval length) length).1,?_⟩
  change (BooleanOp.constant false).Valid (length+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P length).ops.length) ∧
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid (length+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P length).ops.length+1) (_root_.InfoLossLAR.WorstCase.registerLoadOps sources)
  constructor
  · simp [_root_.InfoLossLAR.WorstCase.BooleanOp.Valid,_root_.InfoLossLAR.WorstCase.BooleanOp.sources]
  · convert _Pf6 _ sources hs using 1  <;> omega
open _root_.P2Mf6bd8d28 renaming h238 → _P6m
theorem _root_.P2Mf6bd8d28.h236 {f : Str → Str} (P : PolyProgram id id f) (word : Str) (index : ℕ)
    (hi : index < word.length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length+1)) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedCoreBits P word index=_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits P word index := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedCoreBits _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits _root_.InfoLossLAR.WorstCase.selectorBitsExtension _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result
  simp only [dif_pos hi,Fin.val_mk]
  by_cases he : index=word.length+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length
  · subst index
    rw [Function.update_self,_P45 _ _ _ _ le_rfl,
      _P8o word _ (by omega)]
  · exact Function.update_of_ne he _ _
open _root_.P2Mf6bd8d28 renaming h236 → _P6k
theorem _root_.P2Mf6bd8d28.h237 {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (sources : List (Bool × ℕ)) (index : ℕ)
    (hi : index < word.length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length+1)) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps P word.length sources) (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) index=
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits P word index := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps,_P46]
  simp only [_root_.InfoLossLAR.WorstCase.BooleanProgram.run,_root_.InfoLossLAR.WorstCase.BooleanOp.assign,_root_.InfoLossLAR.WorstCase.BooleanOp.eval]
  rw [_P47 _ _ _ _ (by omega)]
  exact _P6k P word index hi
open _root_.P2Mf6bd8d28 renaming h237 → _P6l
theorem _root_.P2Mf6bd8d28.h239 {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (sources : List (Bool × ℕ))
    (hs : ∀ source∈sources,source.1=true → source.2 < word.length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length+1))
    (index : ℕ) (hi : index < sources.length) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps P word.length sources) (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word)
      (word.length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length+1)+index)=
        _root_.InfoLossLAR.WorstCase.registerLoadValue sources[index] (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits P word) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps,_P46]
  simp only [_root_.InfoLossLAR.WorstCase.BooleanProgram.run,_root_.InfoLossLAR.WorstCase.BooleanOp.assign,_root_.InfoLossLAR.WorstCase.BooleanOp.eval]
  have he : word.length+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length+1=
      word.length+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P word.length).ops.length+1) := by omega
  rw [he]
  change _root_.InfoLossLAR.WorstCase.BooleanProgram.run _ (_root_.InfoLossLAR.WorstCase.registerLoadOps sources) (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedCoreBits P word) _=_
  rw [_Pf7 _ sources hs _ index hi]
  unfold _root_.InfoLossLAR.WorstCase.registerLoadValue
  cases ht : sources[index].1
  · simp
  · simp only [ite_true]
    exact _P6k P word _ (hs sources[index] (List.getElem_mem hi) ht)
open _root_.P2Mf6bd8d28 renaming h239 → _P6n
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h236 → _P6k
open _root_.P2Mf6bd8d28 renaming h237 → _P6l
open _root_.P2Mf6bd8d28 renaming h238 → _P6m
open _root_.P2Mf6bd8d28 renaming h239 → _P6n
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
end Integration9_9.LARCoinLayout
end
end
open _root_.P2Mf6bd8d28 renaming h236 → _P6k
open _root_.P2Mf6bd8d28 renaming h237 → _P6l
open _root_.P2Mf6bd8d28 renaming h238 → _P6m
open _root_.P2Mf6bd8d28 renaming h239 → _P6n
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h531 : Poly _root_.InfoLossLAR.WorstCase.readRawBooleanWord := by
  have hr : Poly (fun xs : Str => (_root_.InfoLossLAR.WorstCase.readBooleanInstruction xs).1) :=
    Poly.comp Poly.fst _Pec
  have hn : Poly (fun xs : Str => xs.length-(_root_.InfoLossLAR.WorstCase.readBooleanInstruction xs).1.length) :=
    Poly.comp Poly.nat_sub (Poly.pair Poly.list_length (Poly.comp Poly.list_length hr))
  have hc : Poly (fun xs : Str => xs.take (xs.length-(_root_.InfoLossLAR.WorstCase.readBooleanInstruction xs).1.length)) :=
    Poly.comp (f := fun x : Str × ℕ => x.1.take x.2)
      (g := fun xs : Str => (xs,xs.length-(_root_.InfoLossLAR.WorstCase.readBooleanInstruction xs).1.length))
      parser_take_poly (Poly.pair Poly.identity hn)
  exact Poly.pair hr hc
open _root_.P2Mf6bd8d28 renaming h531 → _Per
theorem _root_.P2Mf6bd8d28.h532 (xs : Str) : (_root_.InfoLossLAR.WorstCase.readRawBooleanWord xs).1.length ≤ xs.length :=
  _Ped xs
open _root_.P2Mf6bd8d28 renaming h532 → _Pes
theorem _root_.P2Mf6bd8d28.h530 {n : ℕ} (gate : _root_.InfoLossLAR.WorstCase.BooleanGate n) (suffix : Str) :
    _root_.InfoLossLAR.WorstCase.readRawBooleanWord (gate.code++suffix)=(suffix,gate.code) := by
  unfold _root_.InfoLossLAR.WorstCase.readRawBooleanWord
  rw [_Peb]
  simp only [List.length_append,Nat.add_sub_cancel_right,List.take_left]
open _root_.P2Mf6bd8d28 renaming h530 → _Peq
@[fun_prop] theorem _root_.P2Mf6bd8d28.h534 : Poly _root_.InfoLossLAR.WorstCase.readRawBooleanWords :=
  _Pmy _root_.InfoLossLAR.WorstCase.readRawBooleanWord _Per _Pes
open _root_.P2Mf6bd8d28 renaming h534 → _Peu
theorem _root_.P2Mf6bd8d28.h533 {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) (suffix : Str) :
    _root_.InfoLossLAR.WorstCase.readRawBooleanWords (encStr (gates.map _root_.InfoLossLAR.WorstCase.BooleanGate.code)++suffix)=(suffix,gates.map _root_.InfoLossLAR.WorstCase.BooleanGate.code) :=
  _root_.Integration9_9.TM2PlatformSerialization.readList_append_mapped _root_.InfoLossLAR.WorstCase.readRawBooleanWord _root_.InfoLossLAR.WorstCase.BooleanGate.code _root_.InfoLossLAR.WorstCase.BooleanGate.code _Peq gates suffix
open _root_.P2Mf6bd8d28 renaming h533 → _Pet
@[fun_prop] theorem _root_.P2Mf6bd8d28.h529 : Poly _root_.InfoLossLAR.WorstCase.readRawBooleanFamilyWords := by
  have hr : Poly (fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2) := Poly.comp Poly.snd _Pn0
  have ht : Poly (fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2) :=
    Poly.comp (f := fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2) (g := fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2) hr hr
  have hp : Poly (fun xs : Str => _root_.InfoLossLAR.WorstCase.readRawBooleanWords ((_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2)) :=
    Poly.comp (f := _root_.InfoLossLAR.WorstCase.readRawBooleanWords) (g := fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2)
      _Peu ht
  exact Poly.comp (f := fun x : Str × List Str => x.2)
    (g := fun xs : Str => _root_.InfoLossLAR.WorstCase.readRawBooleanWords ((_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2)) Poly.snd hp
open _root_.P2Mf6bd8d28 renaming h529 → _Pep
theorem _root_.P2Mf6bd8d28.h528 (F : _root_.InfoLossLAR.WorstCase.BooleanFamily) (n : ℕ) :
    _root_.InfoLossLAR.WorstCase.readRawBooleanFamilyWords (F.code n)=(F.gates n).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  unfold _root_.InfoLossLAR.WorstCase.readRawBooleanFamilyWords _root_.InfoLossLAR.WorstCase.BooleanFamily.code
  simp only [List.append_assoc,_root_.Integration9_9.TM2PlatformSerialization.readUnary_append]
  have h := _Pet (F.gates n) []
  simpa only [List.append_nil] using congrArg Prod.snd h
open _root_.P2Mf6bd8d28 renaming h528 → _Peo
namespace BooleanProgram
theorem _root_.P2Mf6bd8d28.h147 {total start : ℕ} (first second : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start+(first++second).length ≤ total) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (first++second) h=
      _root_.InfoLossLAR.WorstCase.BooleanProgram.gates start first (by simp only [List.length_append] at h; omega) ++
        _root_.InfoLossLAR.WorstCase.BooleanProgram.gates (start+first.length) second (by simpa only [List.length_append,Nat.add_assoc] using h) := by
  induction first generalizing start with
  | nil => simp only [List.nil_append,_root_.InfoLossLAR.WorstCase.BooleanProgram.gates,List.length_nil,Nat.add_zero]
  | cons op rest ih =>
    simp only [List.cons_append,_root_.InfoLossLAR.WorstCase.BooleanProgram.gates,List.length_cons]
    congr 1
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (start := start+1) (by simp only [List.length_cons,List.length_append] at h ⊢; omega)
open _root_.P2Mf6bd8d28 renaming h147 → _P43
theorem _root_.P2Mf6bd8d28.h146 {left right start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (hl : start+ops.length ≤ left) (hr : start+ops.length ≤ right) (hv : _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start ops) :
    (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops hl).map _root_.InfoLossLAR.WorstCase.BooleanGate.code=(_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops hr).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  let slots := List.replicate (start+ops.length) ()
  have hs : start+ops.length ≤ slots.length := by simp [slots]
  exact (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWords_gates slots start ops hl hv hs).symm.trans
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.instructionWords_gates slots start ops hr hv hs)
open _root_.P2Mf6bd8d28 renaming h146 → _P42
end BooleanProgram
open _root_.P2Mf6bd8d28 renaming h146 → _P42
open _root_.P2Mf6bd8d28 renaming h147 → _P43
namespace TM2Boolean.PolyProgramCircuit
theorem _root_.P2Mf6bd8d28.h221 {f : Str → Str} (P : PolyProgram id id f) (n total : ℕ)
    (hn : n+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops.length ≤ total) :
    _root_.InfoLossLAR.WorstCase.readRawBooleanFamilyWords (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.descriptionGenerator P (unary n))=
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates n (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops hn).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  classical
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.descriptionGenerator_code,_Peo]
  change (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates n (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops _).map _root_.InfoLossLAR.WorstCase.BooleanGate.code=_
  exact _P42 _ _ hn
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram_valid (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity_pos P n) P.machine.code P.machine.input P.machine.main P.machine.initial
      (P.time.eval n) n).1
open _root_.P2Mf6bd8d28 renaming h221 → _P65
end TM2Boolean.PolyProgramCircuit
open _root_.P2Mf6bd8d28 renaming h221 → _P65
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h146 → _P42
open _root_.P2Mf6bd8d28 renaming h147 → _P43
open _root_.P2Mf6bd8d28 renaming h221 → _P65
open _root_.P2Mf6bd8d28 renaming h528 → _Peo
open _root_.P2Mf6bd8d28 renaming h529 → _Pep
open _root_.P2Mf6bd8d28 renaming h530 → _Peq
open _root_.P2Mf6bd8d28 renaming h531 → _Per
open _root_.P2Mf6bd8d28 renaming h532 → _Pes
open _root_.P2Mf6bd8d28 renaming h533 → _Pet
open _root_.P2Mf6bd8d28 renaming h534 → _Peu
end
open _root_.P2Mf6bd8d28 renaming h146 → _P42
open _root_.P2Mf6bd8d28 renaming h147 → _P43
open _root_.P2Mf6bd8d28 renaming h221 → _P65
open _root_.P2Mf6bd8d28 renaming h528 → _Peo
open _root_.P2Mf6bd8d28 renaming h529 → _Pep
open _root_.P2Mf6bd8d28 renaming h530 → _Peq
open _root_.P2Mf6bd8d28 renaming h531 → _Per
open _root_.P2Mf6bd8d28 renaming h532 → _Pes
open _root_.P2Mf6bd8d28 renaming h533 → _Pet
open _root_.P2Mf6bd8d28 renaming h534 → _Peu
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime TM2PlatformSerialization
theorem _root_.P2Mf6bd8d28.h718 (coins padding : Polynomial ℕ) (fallback : Str) (n : ℕ) :
    (_root_.Integration9_9.LARCoinLayout.bodyPreSlots coins padding fallback (unary n)).length=n+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n).ops.length+1) := by
  simp only [_root_.Integration9_9.LARCoinLayout.bodyPreSlots,List.length_append,List.length_map,List.length_singleton,_root_.Integration9_9.LARCoinLayout.bodyPreAncSlots_length]
  simp only [unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h718 → _Pjy
theorem _root_.P2Mf6bd8d28.h729 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family) (n : ℕ) :
    ∀ choice∈_root_.Integration9_9.LARCoinLayout.bodySelectorChoices coins padding fallback (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval n)),
      choice.1 < (_root_.Integration9_9.LARCoinLayout.bodyPreSlots coins padding fallback (unary n)).length+
          (_root_.Integration9_9.LARCoinLayout.bodyDBundleSlots (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval n))).length ∧
      choice.2 < (_root_.Integration9_9.LARCoinLayout.bodyPreSlots coins padding fallback (unary n)).length+
          (_root_.Integration9_9.LARCoinLayout.bodyDBundleSlots (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval n))).length := by
  intro choice hc
  obtain ⟨hf,ho⟩ := List.of_mem_zip hc
  have hflag := _Pjt coins padding fallback n choice.1 hf
  rw [←_Pjy coins padding fallback n] at hflag
  obtain ⟨token,ht,he⟩ := List.mem_map.mp ho
  have hout := _Pkm D (padding.eval n) [] (inputWidth token)
    (List.mem_map.mpr ⟨token,ht,rfl⟩)
  rw [_root_.Integration9_9.LARCoinLayout.bodyDBundleSlots_length D _ []]
  constructor
  · omega
  · rw [←he]
    omega
open _root_.P2Mf6bd8d28 renaming h729 → _Pk9
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h718 → _Pjy
open _root_.P2Mf6bd8d28 renaming h729 → _Pk9
end
end
open _root_.P2Mf6bd8d28 renaming h718 → _Pjy
open _root_.P2Mf6bd8d28 renaming h729 → _Pk9
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
theorem _root_.P2Mf6bd8d28.h725 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family) (n : ℕ) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid n (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) n
      (_root_.Integration9_9.LARCoinLayout.bodySources coins padding fallback D n)) :=
  _P6m _ _ _ (_Pjj coins padding fallback D n)
open _root_.P2Mf6bd8d28 renaming h725 → _Pk5
theorem _root_.P2Mf6bd8d28.h731 {left right : ℕ} (h : left=right) (circuit : Layered left) :
    depth (_root_.Integration9_9.LARCoinLayout.castBodyCircuit h circuit)=depth circuit := by cases h; rfl
open _root_.P2Mf6bd8d28 renaming h731 → _Pkb
theorem _root_.P2Mf6bd8d28.h733 {left right : ℕ} (h : left=right) (circuit : Layered left)
    (hc : ∀ layer∈circuit,LayerOk layer) : ∀ layer∈_root_.Integration9_9.LARCoinLayout.castBodyCircuit h circuit,LayerOk layer := by
  cases h; exact hc
open _root_.P2Mf6bd8d28 renaming h733 → _Pkd
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h725 → _Pk5
open _root_.P2Mf6bd8d28 renaming h731 → _Pkb
open _root_.P2Mf6bd8d28 renaming h733 → _Pkd
end
end
open _root_.P2Mf6bd8d28 renaming h725 → _Pk5
open _root_.P2Mf6bd8d28 renaming h731 → _Pkb
open _root_.P2Mf6bd8d28 renaming h733 → _Pkd
namespace Integration9_9.LARCoinLayout.bodyAncPolynomial
end Integration9_9.LARCoinLayout.bodyAncPolynomial
namespace Integration9_9.LARCoinLayout.bodyDWidth
end Integration9_9.LARCoinLayout.bodyDWidth
namespace Integration9_9.LARCoinLayout.bodyDWidthPolynomial
end Integration9_9.LARCoinLayout.bodyDWidthPolynomial
namespace Integration9_9.LARCoinLayout.bodyDepthPolynomial
end Integration9_9.LARCoinLayout.bodyDepthPolynomial
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9 Integration9_9.TM2StockLists
theorem _root_.P2Mf6bd8d28.h583 (D : Family) (hD : Uniform D) (padding : Polynomial ℕ)
    (builder : Str × List (Str × Str) → Str) (hbuilder : Poly builder) :
    PolyTimeComputable (fun word : Str => builder (word,_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval word.length))) := by
  obtain ⟨source,hsource,hcorrect⟩ := hD
  obtain ⟨table⟩ := _root_.InfoLossLAR.WorstCase.generatedBundleDescriptions_stock source hsource padding
  obtain ⟨quotedTable⟩ := _root_.Integration9_9.TM2Composition.comp BooleanLists.unpackProgram.stock table
  obtain ⟨paired⟩ := _root_.InfoLossLAR.WorstCase.stock_pairWithInput quotedTable
  obtain ⟨built⟩ := _root_.Integration9_9.TM2Composition.comp paired hbuilder.program.stock
  obtain ⟨output⟩ := _root_.Integration9_9.TM2Composition.comp built BooleanLists.unpackProgram.stock
  obtain ⟨whole⟩ := _root_.Integration9_9.TM2Composition.comp BooleanLists.packProgram.stock output
  refine ⟨_root_.Integration9_9.TM2StockLists.congrProgram whole _ ?_⟩
  intro word
  simp only [Function.comp_apply,id_eq]
  rw [_Pbx D source hcorrect]
open _root_.P2Mf6bd8d28 renaming h583 → _Pg7
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h583 → _Pg7
end
open _root_.P2Mf6bd8d28 renaming h583 → _Pg7
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase.BooleanProgram
open QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h145 {total left right : ℕ} (he : left=right) (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (hl : left+ops.length ≤ total) (hr : right+ops.length ≤ total) :
    (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates left ops hl).map _root_.InfoLossLAR.WorstCase.BooleanGate.code=(_root_.InfoLossLAR.WorstCase.BooleanProgram.gates right ops hr).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by cases he; rfl
open _root_.P2Mf6bd8d28 renaming h145 → _P41
end InfoLossLAR.WorstCase.BooleanProgram
open _root_.P2Mf6bd8d28 renaming h145 → _P41
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime TM2PlatformSerialization TM2Boolean.RPN
end Integration9_9.LARCoinLayout
end
end
open _root_.P2Mf6bd8d28 renaming h145 → _P41
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h457 {n m : ℕ} (circuit : Layered n) :
    (_root_.InfoLossLAR.WorstCase.leftCircuit (m := m) circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by
  have hg (gate : Instr n) : encInstr (_root_.InfoLossLAR.WorstCase.leftInstruction (m := m) gate)=encInstr gate := by cases gate <;> rfl
  simp only [_root_.InfoLossLAR.WorstCase.leftCircuit,List.map_map,Function.comp_def,hg]
open _root_.P2Mf6bd8d28 renaming h457 → _Pcp
theorem _root_.P2Mf6bd8d28.h551 {n : ℕ} (left right : ℕ) (he : left=right) (circuit : Layered n) :
    (_root_.InfoLossLAR.WorstCase.rightCircuit (n := left) circuit).map (List.map encInstr)=
      (_root_.InfoLossLAR.WorstCase.rightCircuit (n := right) circuit).map (List.map encInstr) := by cases he; rfl
open _root_.P2Mf6bd8d28 renaming h551 → _Pfb
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h457 → _Pcp
open _root_.P2Mf6bd8d28 renaming h551 → _Pfb
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2PlatformSerialization
theorem _root_.P2Mf6bd8d28.h732 {left right : ℕ} (he : left=right) (circuit : Layered left) :
    (_root_.Integration9_9.LARCoinLayout.castBodyCircuit he circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by cases he; rfl
open _root_.P2Mf6bd8d28 renaming h732 → _Pkc
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h732 → _Pkc
end
end
open _root_.P2Mf6bd8d28 renaming h457 → _Pcp
open _root_.P2Mf6bd8d28 renaming h551 → _Pfb
open _root_.P2Mf6bd8d28 renaming h732 → _Pkc
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h526 : Poly _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers := by
  have hr : Poly (fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2) := Poly.comp Poly.snd _Pn0
  have ht : Poly (fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2) :=
    Poly.comp (f := fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2) (g := fun xs : Str => (_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2) hr hr
  have hp : Poly (fun xs : Str => _root_.InfoLossLAR.WorstCase.readCircuitLayers ((_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2)) :=
    Poly.comp _Pek ht
  exact Poly.comp (f := fun x : Str × List (List Str) => x.2)
    (g := fun xs : Str => _root_.InfoLossLAR.WorstCase.readCircuitLayers ((_root_.Integration9_9.TM2PlatformSerialization.readUnary ((_root_.Integration9_9.TM2PlatformSerialization.readUnary xs).2)).2)) Poly.snd hp
open _root_.P2Mf6bd8d28 renaming h526 → _Pem
theorem _root_.P2Mf6bd8d28.h525 (F : Family) (n : ℕ) :
    _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (encFamilyAt F n)=(F.circ n).map (List.map encInstr) := by
  unfold _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers encFamilyAt
  simp only [List.append_assoc,_root_.Integration9_9.TM2PlatformSerialization.readUnary_append]
  have h := _root_.InfoLossLAR.WorstCase.readCircuitLayers_append (F.circ n) []
  simpa only [List.append_nil] using congrArg Prod.snd h
open _root_.P2Mf6bd8d28 renaming h525 → _Pel
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h525 → _Pel
open _root_.P2Mf6bd8d28 renaming h526 → _Pem
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2PlatformSerialization InfoLossLAR.WorstCase.TM2Boolean.RPN
attribute [local irreducible] bodyPreparedQuantumDescription bodySelectorQuantumDescription bodyDWordLayers
end Integration9_9.LARCoinLayout
end
end
open _root_.P2Mf6bd8d28 renaming h525 → _Pel
open _root_.P2Mf6bd8d28 renaming h526 → _Pem
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.LARCoinLayout
theorem _root_.P2Mf6bd8d28.h646 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (n : ℕ) :
    2 * Q.padding.eval n + 1 < _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n := by
  have h := _P63 (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) (unary n)
  change (Q.f (unary n)).length < _ at h
  rw [Q.output_length] at h
  simpa only [unary,List.length_replicate] using h
open _root_.P2Mf6bd8d28 renaming h646 → _Phy
@[fun_prop] theorem _root_.P2Mf6bd8d28.h624 (Q : _root_.Integration9_9.GenericBody.QueryProgram) : Poly (_root_.Integration9_9.GenericBody.bodyFlagAddresses Q) := by
  unfold _root_.Integration9_9.GenericBody.bodyFlagAddresses
  fun_prop
open _root_.P2Mf6bd8d28 renaming h624 → _Phc
@[fun_prop] theorem _root_.P2Mf6bd8d28.h630 (Q : _root_.Integration9_9.GenericBody.QueryProgram) : Poly (_root_.Integration9_9.GenericBody.bodyPayloadAddresses Q) := by
  unfold _root_.Integration9_9.GenericBody.bodyPayloadAddresses
  fun_prop
open _root_.P2Mf6bd8d28 renaming h630 → _Phi
theorem _root_.P2Mf6bd8d28.h629 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (word : Str) :
    (_root_.Integration9_9.GenericBody.bodyPayloadAddresses Q word).length = Q.padding.eval word.length := by
  simp only [_root_.Integration9_9.GenericBody.bodyPayloadAddresses,_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedAddressRange,List.length_map,List.length_range,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length]
open _root_.P2Mf6bd8d28 renaming h629 → _Phh
theorem _root_.P2Mf6bd8d28.h631 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (n : ℕ) :
    ∀ address ∈ _root_.Integration9_9.GenericBody.bodyPayloadAddresses Q (unary n),
      address < n + ((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n).ops.length + 1) := by
  intro address ha
  apply _P68 (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n
    (_root_.Integration9_9.LARCoinLayout.queryWireSlots Q.padding (unary n)) ((_root_.Integration9_9.LARCoinLayout.queryWireSlots Q.padding (unary n)).length + 1) _ address ha
  have h := _Phy Q n
  simp only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h631 → _Phj
theorem _root_.P2Mf6bd8d28.h625 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (n : ℕ) :
    ∀ address ∈ _root_.Integration9_9.GenericBody.bodyFlagAddresses Q (unary n),
      address < n + ((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n).ops.length + 1) := by
  intro address ha
  apply _P68 (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n
    (_root_.Integration9_9.LARCoinLayout.queryWireSlots Q.padding (unary n) ++ [()]) 0 _ address ha
  have h := _Phy Q n
  simp only [zero_add,List.length_append,List.length_singleton,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h625 → _Phd
theorem _root_.P2Mf6bd8d28.h614 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    ∀ source ∈ _root_.InfoLossLAR.WorstCase.dBundleLoadSources (_root_.Integration9_9.GenericBody.bodyPayloadAddresses Q (unary n))
      (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n)), source.1 = true →
        source.2 < n + ((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n).ops.length + 1) :=
  _Pb9 _ D _ _
    (by simp only [_Phh,unary,List.length_replicate])
    (_Phj Q n)
open _root_.P2Mf6bd8d28 renaming h614 → _Ph2
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h614 → _Ph2
open _root_.P2Mf6bd8d28 renaming h624 → _Phc
open _root_.P2Mf6bd8d28 renaming h625 → _Phd
open _root_.P2Mf6bd8d28 renaming h629 → _Phh
open _root_.P2Mf6bd8d28 renaming h630 → _Phi
open _root_.P2Mf6bd8d28 renaming h631 → _Phj
open _root_.P2Mf6bd8d28 renaming h646 → _Phy
end
end
open _root_.P2Mf6bd8d28 renaming h614 → _Ph2
open _root_.P2Mf6bd8d28 renaming h624 → _Phc
open _root_.P2Mf6bd8d28 renaming h625 → _Phd
open _root_.P2Mf6bd8d28 renaming h629 → _Phh
open _root_.P2Mf6bd8d28 renaming h630 → _Phi
open _root_.P2Mf6bd8d28 renaming h631 → _Phj
open _root_.P2Mf6bd8d28 renaming h646 → _Phy
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h633 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (_root_.Integration9_9.GenericBody.bodyPreAncSlots Q) := by
  unfold _root_.Integration9_9.GenericBody.bodyPreAncSlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h633 → _Phl
@[fun_prop] theorem _root_.P2Mf6bd8d28.h635 (Q : _root_.Integration9_9.GenericBody.QueryProgram) : Poly (_root_.Integration9_9.GenericBody.bodyPreSlots Q) := by
  unfold _root_.Integration9_9.GenericBody.bodyPreSlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h635 → _Phn
theorem _root_.P2Mf6bd8d28.h634 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (n : ℕ) :
    (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length=n+((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n).ops.length+1) := by
  simp only [_root_.Integration9_9.GenericBody.bodyPreSlots,List.length_append,List.length_map,List.length_singleton,_root_.Integration9_9.GenericBody.bodyPreAncSlots_length]
  simp only [unary,List.length_replicate]
  omega
open _root_.P2Mf6bd8d28 renaming h634 → _Phm
@[fun_prop] theorem _root_.P2Mf6bd8d28.h612 : Poly _root_.Integration9_9.GenericBody.bodyDBundleSlots := by
  unfold _root_.Integration9_9.GenericBody.bodyDBundleSlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h612 → _Ph0
@[fun_prop] theorem _root_.P2Mf6bd8d28.h649 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodySelectorChoices Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorChoices
  fun_prop
open _root_.P2Mf6bd8d28 renaming h649 → _Pi1
theorem _root_.P2Mf6bd8d28.h650 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    ∀ choice∈_root_.Integration9_9.GenericBody.bodySelectorChoices Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n)),
      choice.1 < (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length+
          (_root_.Integration9_9.GenericBody.bodyDBundleSlots (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))).length ∧
      choice.2 < (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length+
          (_root_.Integration9_9.GenericBody.bodyDBundleSlots (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))).length := by
  intro choice hc
  obtain ⟨hf,ho⟩ := List.of_mem_zip hc
  have hflag := _Phd Q n choice.1 hf
  rw [←_Phm Q n] at hflag
  obtain ⟨token,ht,he⟩ := List.mem_map.mp ho
  have hout := _Pkm D (Q.padding.eval n) [] (inputWidth token)
    (List.mem_map.mpr ⟨token,ht,rfl⟩)
  rw [_root_.Integration9_9.GenericBody.bodyDBundleSlots_length D _ []]
  constructor
  · omega
  · rw [←he]
    omega
open _root_.P2Mf6bd8d28 renaming h650 → _Pi2
@[fun_prop] theorem _root_.P2Mf6bd8d28.h609 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyAncSlots Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyAncSlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h609 → _Pgx
@[fun_prop] theorem _root_.P2Mf6bd8d28.h608 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyAllSlots Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyAllSlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h608 → _Pgw
theorem _root_.P2Mf6bd8d28.h607 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (word : Str) (descriptions : List (Str × Str)) :
    (_root_.Integration9_9.GenericBody.bodyAllSlots Q word descriptions).length=
      (_root_.Integration9_9.GenericBody.bodyPreSlots Q word).length+(_root_.Integration9_9.GenericBody.bodyDBundleSlots descriptions).length+
        4*(_root_.Integration9_9.GenericBody.bodySelectorChoices Q word descriptions).length+1 := by
  simp only [_root_.Integration9_9.GenericBody.bodyAllSlots,_root_.Integration9_9.GenericBody.bodyAncSlots,_root_.Integration9_9.GenericBody.bodyPreSlots,List.length_append,List.length_map,List.length_singleton,
    _root_.InfoLossLAR.WorstCase.multiSelectorScratch_length]
  omega
open _root_.P2Mf6bd8d28 renaming h607 → _Pgv
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h607 → _Pgv
open _root_.P2Mf6bd8d28 renaming h608 → _Pgw
open _root_.P2Mf6bd8d28 renaming h609 → _Pgx
open _root_.P2Mf6bd8d28 renaming h612 → _Ph0
open _root_.P2Mf6bd8d28 renaming h633 → _Phl
open _root_.P2Mf6bd8d28 renaming h634 → _Phm
open _root_.P2Mf6bd8d28 renaming h635 → _Phn
open _root_.P2Mf6bd8d28 renaming h649 → _Pi1
open _root_.P2Mf6bd8d28 renaming h650 → _Pi2
end
end
open _root_.P2Mf6bd8d28 renaming h607 → _Pgv
open _root_.P2Mf6bd8d28 renaming h608 → _Pgw
open _root_.P2Mf6bd8d28 renaming h609 → _Pgx
open _root_.P2Mf6bd8d28 renaming h612 → _Ph0
open _root_.P2Mf6bd8d28 renaming h633 → _Phl
open _root_.P2Mf6bd8d28 renaming h634 → _Phm
open _root_.P2Mf6bd8d28 renaming h635 → _Phn
open _root_.P2Mf6bd8d28 renaming h649 → _Pi1
open _root_.P2Mf6bd8d28 renaming h650 → _Pi2
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
theorem _root_.P2Mf6bd8d28.h643 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid n (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n
      (_root_.Integration9_9.GenericBody.bodySources Q D n)) :=
  _P6m _ _ _ (_Ph2 Q D n)
open _root_.P2Mf6bd8d28 renaming h643 → _Phv
theorem _root_.P2Mf6bd8d28.h658 {left right : ℕ} (h : left=right) (circuit : Layered left) :
    depth (_root_.Integration9_9.GenericBody.castBodyCircuit h circuit)=depth circuit := by cases h; rfl
open _root_.P2Mf6bd8d28 renaming h658 → _Pia
theorem _root_.P2Mf6bd8d28.h660 {left right : ℕ} (h : left=right) (circuit : Layered left)
    (hc : ∀ layer∈circuit,LayerOk layer) : ∀ layer∈_root_.Integration9_9.GenericBody.castBodyCircuit h circuit,LayerOk layer := by
  cases h; exact hc
open _root_.P2Mf6bd8d28 renaming h660 → _Pic
theorem _root_.P2Mf6bd8d28.h613 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family)
    (hD : WellFormed D) (n : ℕ) : ∀ layer∈_root_.Integration9_9.GenericBody.bodyDCircuit Q D n,LayerOk layer :=
  _Pic _ _ (_Pcr _
    (_Pfd _ (_Pe4 D hD (Q.padding.eval n) [])))
open _root_.P2Mf6bd8d28 renaming h613 → _Ph1
theorem _root_.P2Mf6bd8d28.h623 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family)
    (hD : WellFormed D) : WellFormed (_root_.Integration9_9.GenericBody.bodyFamily Q D) := by
  intro n layer hl
  simp only [_root_.Integration9_9.GenericBody.bodyFamily,_root_.Integration9_9.GenericBody.bodyCircuit,List.mem_append] at hl
  rcases hl with (hp|hd)|hs
  · exact _Paw _ layer hp
  · exact _Ph1 Q D hD n layer hd
  · exact _Paw _ layer hs
open _root_.P2Mf6bd8d28 renaming h623 → _Phb
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h613 → _Ph1
open _root_.P2Mf6bd8d28 renaming h623 → _Phb
open _root_.P2Mf6bd8d28 renaming h643 → _Phv
open _root_.P2Mf6bd8d28 renaming h658 → _Pia
open _root_.P2Mf6bd8d28 renaming h660 → _Pic
end
end
open _root_.P2Mf6bd8d28 renaming h613 → _Ph1
open _root_.P2Mf6bd8d28 renaming h623 → _Phb
open _root_.P2Mf6bd8d28 renaming h643 → _Phv
open _root_.P2Mf6bd8d28 renaming h658 → _Pia
open _root_.P2Mf6bd8d28 renaming h660 → _Pic
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
theorem _root_.P2Mf6bd8d28.h610 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (Dbound : Polynomial ℕ)
    (hanc : ∀ n,D.anc n ≤ Dbound.eval n) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyAnc Q D n ≤ (_root_.Integration9_9.GenericBody.bodyAncPolynomial Q Dbound).eval n := by
  have hp := _P64 (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n
  have hd := _Pe6 D Dbound hanc (Q.padding.eval n) []
  rw [_root_.Integration9_9.GenericBody.bodyAnc_formula]
  simp only [_root_.Integration9_9.GenericBody.bodyAncPolynomial,_root_.Integration9_9.GenericBody.bodyDWidthPolynomial,eval_add,eval_mul,eval_one,eval_ofNat,eval_comp]
  change _ ≤ _
  dsimp only [_root_.Integration9_9.GenericBody.bodyDWidth]
  omega
open _root_.P2Mf6bd8d28 renaming h610 → _Pgy
theorem _root_.P2Mf6bd8d28.h642 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.GenericBody.bodyPreparedGates Q D n))) ≤
      74*((_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n).ops.length+1+_root_.Integration9_9.GenericBody.bodyDWidth Q D n) := by
  have h := _P3z
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n (_root_.Integration9_9.GenericBody.bodySources Q D n))
    (_root_.Integration9_9.GenericBody.bodyPrepared_bound Q D n)
  unfold _root_.Integration9_9.GenericBody.bodyPreparedGates
  exact h.trans (by rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps_length,_root_.Integration9_9.GenericBody.bodySources_length])
open _root_.P2Mf6bd8d28 renaming h642 → _Phu
theorem _root_.P2Mf6bd8d28.h655 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.GenericBody.bodySelectorGates Q D n))) ≤ 296*(Q.padding.eval n+1) := by
  have h := _P3z
    (_root_.InfoLossLAR.WorstCase.multiSelectorOps (_root_.Integration9_9.GenericBody.bodyPreWidth Q n+_root_.Integration9_9.GenericBody.bodyDWidth Q D n) 0
      (_root_.Integration9_9.GenericBody.bodyChoices Q D n))
    (by simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] using _root_.Integration9_9.GenericBody.bodySelected_bound Q D n)
  unfold _root_.Integration9_9.GenericBody.bodySelectorGates
  exact h.trans (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length,_root_.Integration9_9.GenericBody.bodyChoices_length]; omega)
open _root_.P2Mf6bd8d28 renaming h655 → _Pi7
theorem _root_.P2Mf6bd8d28.h617 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (Dbound : Polynomial ℕ)
    (hdepth : ∀ n,depth (D.circ n) ≤ Dbound.eval n) (n : ℕ) :
    depth (_root_.Integration9_9.GenericBody.bodyDCircuit Q D n) ≤ (Q.padding.eval n+1)*Dbound.eval (Q.padding.eval n) := by
  unfold _root_.Integration9_9.GenericBody.bodyDCircuit
  rw [_Pia,_root_.InfoLossLAR.WorstCase.leftCircuit_depth,_root_.InfoLossLAR.WorstCase.rightCircuit_depth]
  exact _Pdz D Dbound hdepth (Q.padding.eval n) []
open _root_.P2Mf6bd8d28 renaming h617 → _Ph5
theorem _root_.P2Mf6bd8d28.h611 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (Dbound : Polynomial ℕ)
    (hdepth : ∀ n,depth (D.circ n) ≤ Dbound.eval n) (hanc : ∀ n,D.anc n ≤ Dbound.eval n) (n : ℕ) :
    depth (_root_.Integration9_9.GenericBody.bodyCircuit Q D n) ≤ (_root_.Integration9_9.GenericBody.bodyDepthPolynomial Q Dbound).eval n := by
  have hp := _P64 (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n
  have hd := _Pe6 D Dbound hanc (Q.padding.eval n) []
  have hprep := _Phu Q D n
  have hselect := _Pi7 Q D n
  have hddepth := _Ph5 Q D Dbound hdepth n
  simp only [_root_.Integration9_9.GenericBody.bodyCircuit,depth,List.length_append]
  simp only [depth,_root_.Integration9_9.GenericBody.bodyDWidth] at hprep hselect hddepth
  simp only [_root_.Integration9_9.GenericBody.bodyDepthPolynomial,_root_.Integration9_9.GenericBody.bodyDWidthPolynomial,eval_add,eval_mul,eval_one,eval_ofNat,eval_comp]
  omega
open _root_.P2Mf6bd8d28 renaming h611 → _Pgz
theorem _root_.P2Mf6bd8d28.h621 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family)
    (hD : PolyBounded D) : PolyBounded (_root_.Integration9_9.GenericBody.bodyFamily Q D) := by
  obtain ⟨Dbound,hdepth,hanc⟩ := hD
  refine ⟨_root_.Integration9_9.GenericBody.bodyDepthPolynomial Q Dbound+_root_.Integration9_9.GenericBody.bodyAncPolynomial Q Dbound,?_,?_⟩
  · intro n
    have h := _Pgz Q D Dbound hdepth hanc n
    change depth (_root_.Integration9_9.GenericBody.bodyCircuit Q D n) ≤ _
    simp only [eval_add]
    omega
  · intro n
    have h := _Pgy Q D Dbound hanc n
    change _root_.Integration9_9.GenericBody.bodyAnc Q D n ≤ _
    simp only [eval_add]
    omega
open _root_.P2Mf6bd8d28 renaming h621 → _Ph9
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h610 → _Pgy
open _root_.P2Mf6bd8d28 renaming h611 → _Pgz
open _root_.P2Mf6bd8d28 renaming h617 → _Ph5
open _root_.P2Mf6bd8d28 renaming h621 → _Ph9
open _root_.P2Mf6bd8d28 renaming h642 → _Phu
open _root_.P2Mf6bd8d28 renaming h655 → _Pi7
end
end
open _root_.P2Mf6bd8d28 renaming h610 → _Pgy
open _root_.P2Mf6bd8d28 renaming h611 → _Pgz
open _root_.P2Mf6bd8d28 renaming h617 → _Ph5
open _root_.P2Mf6bd8d28 renaming h621 → _Ph9
open _root_.P2Mf6bd8d28 renaming h642 → _Phu
open _root_.P2Mf6bd8d28 renaming h655 → _Pi7
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime TM2PlatformSerialization TM2Boolean.RPN
theorem _root_.P2Mf6bd8d28.h606 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    (_root_.Integration9_9.GenericBody.bodyAllSlots Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))).length=
      _root_.Integration9_9.GenericBody.bodyWidth Q D n := by
  rw [_Pgv,_Phm,_root_.Integration9_9.GenericBody.bodyDBundleSlots_length D _ [],_root_.Integration9_9.GenericBody.bodySelectorChoices_length,
    _root_.Integration9_9.GenericBody.bodyWidth_formula]
  rfl
open _root_.P2Mf6bd8d28 renaming h606 → _Pgu
@[fun_prop] theorem _root_.P2Mf6bd8d28.h657 (Q : _root_.Integration9_9.GenericBody.QueryProgram) : Poly (_root_.Integration9_9.GenericBody.bodyZeroWord Q) := by
  unfold _root_.Integration9_9.GenericBody.bodyZeroWord
  fun_prop
open _root_.P2Mf6bd8d28 renaming h657 → _Pi9
theorem _root_.P2Mf6bd8d28.h656 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyZeroWord Q (unary n)=
      encNat 0++encNat (n+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) n).ops.length) := by
  simp only [_root_.Integration9_9.GenericBody.bodyZeroWord,_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,List.length_append,List.length_map,_root_.Integration9_9.GenericBody.bodyPreAncSlots_length]
  simp only [unary,List.length_replicate]
open _root_.P2Mf6bd8d28 renaming h656 → _Pi8
@[fun_prop] theorem _root_.P2Mf6bd8d28.h641 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyPreparedWords Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyPreparedWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h641 → _Pht
theorem _root_.P2Mf6bd8d28.h640 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyPreparedWords Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      (_root_.Integration9_9.GenericBody.bodyPreparedGates Q D n).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  let P := _root_.Integration9_9.GenericBody.bodyQueryProgram Q
  let total := _root_.Integration9_9.GenericBody.bodyWidth Q D n
  let sources := _root_.Integration9_9.GenericBody.bodySources Q D n
  have hp : n+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops.length ≤ total := by
    have h := _root_.Integration9_9.GenericBody.bodyPrepared_bound Q D n
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps_length] at h
    dsimp only [P,total]
    omega
  have hstart : (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length=n+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops.length+1 := by
    rw [_Phm]; dsimp only [P]; omega
  have hd : (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length+sources.length ≤ total := by
    rw [_Phm]
    dsimp only [sources,total]
    rw [_root_.Integration9_9.GenericBody.bodySources_length,_root_.Integration9_9.GenericBody.bodyWidth_formula]
    dsimp only [_root_.Integration9_9.GenericBody.bodyPreWidth,P]
    omega
  have hold : n+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops.length+1+(_root_.InfoLossLAR.WorstCase.registerLoadOps sources).length ≤ total := by
    rw [_root_.InfoLossLAR.WorstCase.registerLoadOps_length]
    rw [hstart] at hd
    exact hd
  have hs : ∀ source∈sources,source.1=true → source.2 < (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length := by
    rw [_Phm]
    exact _Ph2 Q D n
  have hload := _Pf0
    (_root_.Integration9_9.GenericBody.bodyAllSlots Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n)))
    (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length sources hs hd
    (by rw [_Pgu]; exact hd)
  have hload' :
      _root_.InfoLossLAR.WorstCase.registerLoadGateWords (_root_.Integration9_9.GenericBody.bodyAllSlots Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n)))
        (_root_.Integration9_9.GenericBody.bodyPreSlots Q (unary n)).length sources=
      (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates (n+(_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled P n).ops.length+1) (_root_.InfoLossLAR.WorstCase.registerLoadOps sources) hold).map _root_.InfoLossLAR.WorstCase.BooleanGate.code :=
    hload.trans (_P41 hstart (_root_.InfoLossLAR.WorstCase.registerLoadOps sources) _ hold)
  unfold _root_.Integration9_9.GenericBody.bodyPreparedWords
  change _root_.InfoLossLAR.WorstCase.readRawBooleanFamilyWords (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.descriptionGenerator P (unary n))++[_root_.Integration9_9.GenericBody.bodyZeroWord Q (unary n)]++
    _root_.InfoLossLAR.WorstCase.registerLoadGateWords _ _ sources=_
  rw [_P65 P n total hp,_Pi8,hload']
  unfold _root_.Integration9_9.GenericBody.bodyPreparedGates _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps
  rw [_P43]
  simp only [List.map_append,_root_.InfoLossLAR.WorstCase.BooleanProgram.gates,List.map_cons,_root_.InfoLossLAR.WorstCase.BooleanGate.code,Bool.false_eq_true,ite_false,
    List.singleton_append,List.append_assoc]
  rfl
open _root_.P2Mf6bd8d28 renaming h640 → _Phs
@[fun_prop] theorem _root_.P2Mf6bd8d28.h654 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodySelectorWords Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h654 → _Pi6
theorem _root_.P2Mf6bd8d28.h653 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodySelectorWords Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      (_root_.Integration9_9.GenericBody.bodySelectorGates Q D n).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorWords
  rw [_Phm,_root_.Integration9_9.GenericBody.bodyDBundleSlots_length D _ []]
  change _root_.InfoLossLAR.WorstCase.multiSelectorGateWords _ (_root_.Integration9_9.GenericBody.bodyPreWidth Q n+_root_.Integration9_9.GenericBody.bodyDWidth Q D n) 0
    (_root_.Integration9_9.GenericBody.bodyChoices Q D n)=_
  apply _Pcz
  · unfold _root_.Integration9_9.GenericBody.bodyPreWidth; omega
  · have h := _Pi2 Q D n
    rw [_Phm,_root_.Integration9_9.GenericBody.bodyDBundleSlots_length D _ []] at h
    exact h
  · exact _root_.Integration9_9.GenericBody.bodySelected_bound Q D n
  · rw [_Pgu]
    exact _root_.Integration9_9.GenericBody.bodySelected_bound Q D n
open _root_.P2Mf6bd8d28 renaming h653 → _Pi5
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h606 → _Pgu
open _root_.P2Mf6bd8d28 renaming h640 → _Phs
open _root_.P2Mf6bd8d28 renaming h641 → _Pht
open _root_.P2Mf6bd8d28 renaming h653 → _Pi5
open _root_.P2Mf6bd8d28 renaming h654 → _Pi6
open _root_.P2Mf6bd8d28 renaming h656 → _Pi8
open _root_.P2Mf6bd8d28 renaming h657 → _Pi9
end
end
open _root_.P2Mf6bd8d28 renaming h606 → _Pgu
open _root_.P2Mf6bd8d28 renaming h640 → _Phs
open _root_.P2Mf6bd8d28 renaming h641 → _Pht
open _root_.P2Mf6bd8d28 renaming h653 → _Pi5
open _root_.P2Mf6bd8d28 renaming h654 → _Pi6
open _root_.P2Mf6bd8d28 renaming h656 → _Pi8
open _root_.P2Mf6bd8d28 renaming h657 → _Pi9
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2PlatformSerialization
theorem _root_.P2Mf6bd8d28.h659 {left right : ℕ} (he : left=right) (circuit : Layered left) :
    (_root_.Integration9_9.GenericBody.castBodyCircuit he circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by cases he; rfl
open _root_.P2Mf6bd8d28 renaming h659 → _Pib
@[fun_prop] theorem _root_.P2Mf6bd8d28.h616 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyDWordLayers Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyDWordLayers
  fun_prop
open _root_.P2Mf6bd8d28 renaming h616 → _Ph4
theorem _root_.P2Mf6bd8d28.h615 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyDWordLayers Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      (_root_.Integration9_9.GenericBody.bodyDCircuit Q D n).map (List.map encInstr) := by
  unfold _root_.Integration9_9.GenericBody.bodyDWordLayers
  rw [_root_.InfoLossLAR.WorstCase.describedQueryBlocks_frames D _ [],_Pa7,_Pfm]
  unfold _root_.Integration9_9.GenericBody.bodyDCircuit
  rw [_Pib,_Pcp]
  apply _Pfb
  simp only [List.length_map]
  exact _Phm Q n
open _root_.P2Mf6bd8d28 renaming h615 → _Ph3
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h615 → _Ph3
open _root_.P2Mf6bd8d28 renaming h616 → _Ph4
open _root_.P2Mf6bd8d28 renaming h659 → _Pib
end
end
open _root_.P2Mf6bd8d28 renaming h615 → _Ph3
open _root_.P2Mf6bd8d28 renaming h616 → _Ph4
open _root_.P2Mf6bd8d28 renaming h659 → _Pib
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open TM2PlatformSerialization InfoLossLAR.WorstCase.TM2Boolean.RPN
@[fun_prop] theorem _root_.P2Mf6bd8d28.h628 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyOutputWord Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyOutputWord
  fun_prop
open _root_.P2Mf6bd8d28 renaming h628 → _Phg
theorem _root_.P2Mf6bd8d28.h627 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyOutputWord Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      encNat (_root_.Integration9_9.GenericBody.bodyOutput Q D n).val := by
  unfold _root_.Integration9_9.GenericBody.bodyOutputWord
  rw [_Phm,_root_.Integration9_9.GenericBody.bodyDBundleSlots_length D _ [],_Pcx]
  change _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.boundedNat _ (_root_.Integration9_9.GenericBody.bodyOutput Q D n).val=_
  apply _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.boundedNat_eq
  rw [_Pgu]
  exact (_root_.Integration9_9.GenericBody.bodyOutput Q D n).isLt.le
open _root_.P2Mf6bd8d28 renaming h627 → _Phf
@[fun_prop] theorem _root_.P2Mf6bd8d28.h637 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyPreparedBooleanDescription Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyPreparedBooleanDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h637 → _Php
theorem _root_.P2Mf6bd8d28.h636 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyPreparedBooleanDescription Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      (_root_.Integration9_9.GenericBody.bodyPreparedBooleanFamily Q D).code n := by
  unfold _root_.Integration9_9.GenericBody.bodyPreparedBooleanDescription
  rw [_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,_Phf,_Phs,_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq]
  rfl
open _root_.P2Mf6bd8d28 renaming h636 → _Pho
@[fun_prop] theorem _root_.P2Mf6bd8d28.h648 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodySelectorBooleanDescription Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorBooleanDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h648 → _Pi0
theorem _root_.P2Mf6bd8d28.h647 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodySelectorBooleanDescription Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      (_root_.Integration9_9.GenericBody.bodySelectorBooleanFamily Q D).code n := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorBooleanDescription
  rw [_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,_Phf,_Pi5,_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq]
  rfl
open _root_.P2Mf6bd8d28 renaming h647 → _Phz
@[fun_prop] theorem _root_.P2Mf6bd8d28.h639 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h639 → _Phr
theorem _root_.P2Mf6bd8d28.h638 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      encFamilyAt (_root_.Integration9_9.GenericBody.bodyPreparedBooleanFamily Q D).reversible.compile n := by
  unfold _root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription
  rw [_Pho,_Pap,_Par]
open _root_.P2Mf6bd8d28 renaming h638 → _Phq
@[fun_prop] theorem _root_.P2Mf6bd8d28.h652 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorQuantumDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h652 → _Pi4
theorem _root_.P2Mf6bd8d28.h651 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      encFamilyAt (_root_.Integration9_9.GenericBody.bodySelectorBooleanFamily Q D).reversible.compile n := by
  unfold _root_.Integration9_9.GenericBody.bodySelectorQuantumDescription
  rw [_Phz,_Pap,_Par]
open _root_.P2Mf6bd8d28 renaming h651 → _Pi3
attribute [local irreducible] bodyPreparedQuantumDescription bodySelectorQuantumDescription bodyDWordLayers
@[fun_prop] theorem _root_.P2Mf6bd8d28.h645 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyQuantumWordLayers Q x.1 x.2) := by
  have hp : Poly (fun x : Str × List (Str × Str) =>
      _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (_root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription Q x.1 x.2)) :=
    Poly.comp (f := _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers)
      (g := fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription Q x.1 x.2)
      _Pem (_Phr Q)
  have hs : Poly (fun x : Str × List (Str × Str) =>
      _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (_root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q x.1 x.2)) :=
    Poly.comp (f := _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers)
      (g := fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q x.1 x.2)
      _Pem (_Pi4 Q)
  have hd := _Ph4 Q
  have htail : Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyDWordLayers Q x.1 x.2++
      _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (_root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q x.1 x.2)) :=
    Poly.comp (f := fun x : List (List Str) × List (List Str) => x.1++x.2)
      (g := fun x : Str × List (Str × Str) => (_root_.Integration9_9.GenericBody.bodyDWordLayers Q x.1 x.2,
        _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (_root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q x.1 x.2)))
      Poly.list_append (Poly.pair hd hs)
  have h := Poly.comp (f := fun x : List (List Str) × List (List Str) => x.1++x.2)
    (g := fun x : Str × List (Str × Str) =>
      (_root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (_root_.Integration9_9.GenericBody.bodyPreparedQuantumDescription Q x.1 x.2),
        _root_.Integration9_9.GenericBody.bodyDWordLayers Q x.1 x.2++
          _root_.InfoLossLAR.WorstCase.readFamilyCircuitLayers (_root_.Integration9_9.GenericBody.bodySelectorQuantumDescription Q x.1 x.2)))
    Poly.list_append (Poly.pair hp htail)
  simpa only [_root_.Integration9_9.GenericBody.bodyQuantumWordLayers,List.append_assoc] using h
open _root_.P2Mf6bd8d28 renaming h645 → _Phx
theorem _root_.P2Mf6bd8d28.h644 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyQuantumWordLayers Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      (_root_.Integration9_9.GenericBody.bodyCircuit Q D n).map (List.map encInstr) := by
  unfold _root_.Integration9_9.GenericBody.bodyQuantumWordLayers
  rw [_Phq,_Pel,
    _Ph3,_Pi3,_Pel]
  simp only [_root_.Integration9_9.GenericBody.bodyPreparedBooleanFamily,_root_.Integration9_9.GenericBody.bodySelectorBooleanFamily,_root_.InfoLossLAR.WorstCase.BooleanFamily.reversible,_root_.InfoLossLAR.WorstCase.ReversibleFamily.compile,
    _root_.Integration9_9.GenericBody.bodyCircuit,List.map_append]
open _root_.P2Mf6bd8d28 renaming h644 → _Phw
@[fun_prop] theorem _root_.P2Mf6bd8d28.h619 (Q : _root_.Integration9_9.GenericBody.QueryProgram) :
    Poly (fun x : Str × List (Str × Str) => _root_.Integration9_9.GenericBody.bodyDescription Q x.1 x.2) := by
  unfold _root_.Integration9_9.GenericBody.bodyDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h619 → _Ph7
theorem _root_.P2Mf6bd8d28.h618 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (n : ℕ) :
    _root_.Integration9_9.GenericBody.bodyDescription Q (unary n) (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval n))=
      encFamilyAt (_root_.Integration9_9.GenericBody.bodyFamily Q D) n := by
  unfold _root_.Integration9_9.GenericBody.bodyDescription
  rw [_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,_Phf,_Phw]
  simp only [_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq,List.map_map,Function.comp_def]
  rfl
open _root_.P2Mf6bd8d28 renaming h618 → _Ph6
theorem _root_.P2Mf6bd8d28.h622 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (hD : Uniform D) :
    Uniform (_root_.Integration9_9.GenericBody.bodyFamily Q D) := by
  let builder : Str × List (Str × Str) → Str := fun x => _root_.Integration9_9.GenericBody.bodyDescription Q x.1 x.2
  let generator : Str → Str := fun word => builder (word,_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval word.length))
  have hg : PolyTimeComputable generator := _Pg7 D hD Q.padding builder
    (_Ph7 Q)
  refine ⟨generator,hg,?_⟩
  intro n
  change _root_.Integration9_9.GenericBody.bodyDescription Q (unary n)
    (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (Q.padding.eval (unary n).length))=_
  rw [show (unary n).length=n by simp [unary]]
  exact _Ph6 Q D n
open _root_.P2Mf6bd8d28 renaming h622 → _Pha
theorem _root_.P2Mf6bd8d28.h620 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (D : Family) (hD : IsQPT D) :
    IsQPT (_root_.Integration9_9.GenericBody.bodyFamily Q D) :=
  ⟨_Pha Q D hD.1,
    _Phb Q D hD.2.1,
    _Ph9 Q D hD.2.2⟩
open _root_.P2Mf6bd8d28 renaming h620 → _Ph8
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h618 → _Ph6
open _root_.P2Mf6bd8d28 renaming h619 → _Ph7
open _root_.P2Mf6bd8d28 renaming h620 → _Ph8
open _root_.P2Mf6bd8d28 renaming h622 → _Pha
open _root_.P2Mf6bd8d28 renaming h627 → _Phf
open _root_.P2Mf6bd8d28 renaming h628 → _Phg
open _root_.P2Mf6bd8d28 renaming h636 → _Pho
open _root_.P2Mf6bd8d28 renaming h637 → _Php
open _root_.P2Mf6bd8d28 renaming h638 → _Phq
open _root_.P2Mf6bd8d28 renaming h639 → _Phr
open _root_.P2Mf6bd8d28 renaming h644 → _Phw
open _root_.P2Mf6bd8d28 renaming h645 → _Phx
open _root_.P2Mf6bd8d28 renaming h647 → _Phz
open _root_.P2Mf6bd8d28 renaming h648 → _Pi0
open _root_.P2Mf6bd8d28 renaming h651 → _Pi3
open _root_.P2Mf6bd8d28 renaming h652 → _Pi4
end
end
open _root_.P2Mf6bd8d28 renaming h618 → _Ph6
open _root_.P2Mf6bd8d28 renaming h619 → _Ph7
open _root_.P2Mf6bd8d28 renaming h620 → _Ph8
open _root_.P2Mf6bd8d28 renaming h622 → _Pha
open _root_.P2Mf6bd8d28 renaming h627 → _Phf
open _root_.P2Mf6bd8d28 renaming h628 → _Phg
open _root_.P2Mf6bd8d28 renaming h636 → _Pho
open _root_.P2Mf6bd8d28 renaming h637 → _Php
open _root_.P2Mf6bd8d28 renaming h638 → _Phq
open _root_.P2Mf6bd8d28 renaming h639 → _Phr
open _root_.P2Mf6bd8d28 renaming h644 → _Phw
open _root_.P2Mf6bd8d28 renaming h645 → _Phx
open _root_.P2Mf6bd8d28 renaming h647 → _Phz
open _root_.P2Mf6bd8d28 renaming h648 → _Pi0
open _root_.P2Mf6bd8d28 renaming h651 → _Pi3
open _root_.P2Mf6bd8d28 renaming h652 → _Pi4
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBody
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
open Integration9_9.LARCoinLayout
theorem _root_.P2Mf6bd8d28.h626 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (query : Str → Str)
    (hquery : ∀ word, Q.f word = _root_.Integration9_9.LARCoinLayout.encodeQueryOutput
      (List.replicate (Q.padding.eval word.length) ()) (query word))
    (word : Str) (index : ℕ) (hi : index ≤ Q.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) word
      ((_root_.Integration9_9.GenericBody.bodyFlagAddresses Q (unary word.length))[index]'(by
        simp only [_root_.Integration9_9.GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega)) =
      decide ((query word).length = index) := by
  let P := _root_.Integration9_9.GenericBody.bodyQueryProgram Q
  have hcap := _Phy Q word.length
  let cell : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length) := ⟨index,by dsimp only [P]; omega⟩
  have haddr : (_root_.Integration9_9.GenericBody.bodyFlagAddresses Q (unary word.length))[index]'(by
      simp only [_root_.Integration9_9.GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega) =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary word.length) cell.val := by
    unfold _root_.Integration9_9.GenericBody.bodyFlagAddresses
    rw [_P69 _ _ _ 0 index (by
      simp only [List.length_append,List.length_singleton,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]; omega)]
    simp only [zero_add,P,cell]
  rw [haddr,_P6f]
  change decide (some true = (Q.f word)[index]?) = _
  rw [hquery word]
  rw [_Pko _ _ index (by simpa only [List.length_replicate] using hi)]
  by_cases he : (query word).length = index <;> simp [he]
open _root_.P2Mf6bd8d28 renaming h626 → _Phe
theorem _root_.P2Mf6bd8d28.h632 (Q : _root_.Integration9_9.GenericBody.QueryProgram) (query : Str → Str)
    (hquery : ∀ word, Q.f word = _root_.Integration9_9.LARCoinLayout.encodeQueryOutput
      (List.replicate (Q.padding.eval word.length) ()) (query word))
    (word : Str) (index : ℕ) (hi : index < Q.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.GenericBody.bodyQueryProgram Q) word
      ((_root_.Integration9_9.GenericBody.bodyPayloadAddresses Q (unary word.length))[index]'(by
        simpa only [_Phh,unary,List.length_replicate] using hi)) =
      ((query word)[index]?).getD false := by
  let P := _root_.Integration9_9.GenericBody.bodyQueryProgram Q
  have hcap := _Phy Q word.length
  let cell : Fin (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.capacity P word.length) := ⟨Q.padding.eval word.length + 1 + index,by dsimp only [P]; omega⟩
  have haddr : (_root_.Integration9_9.GenericBody.bodyPayloadAddresses Q (unary word.length))[index]'(by
      simpa only [_Phh,unary,List.length_replicate] using hi) =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedProgramOutputAddress P (unary word.length) cell.val := by
    unfold _root_.Integration9_9.GenericBody.bodyPayloadAddresses
    rw [_P69 _ _ _ _ index (by
      simpa only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate] using hi)]
    simp only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate,cell,P]
  rw [haddr,_P6f]
  change decide (some true = (Q.f word)[Q.padding.eval word.length + 1 + index]?) = _
  have hbit := _Pkn (List.replicate (Q.padding.eval word.length) ()) (query word) index
    (by simpa only [List.length_replicate] using hi)
  simp only [List.length_replicate] at hbit
  rw [hquery word,hbit]
  cases hb : ((query word)[index]?).getD false <;> simp [hb]
open _root_.P2Mf6bd8d28 renaming h632 → _Phk
end Integration9_9.GenericBody
open _root_.P2Mf6bd8d28 renaming h626 → _Phe
open _root_.P2Mf6bd8d28 renaming h632 → _Phk
end
end
open _root_.P2Mf6bd8d28 renaming h626 → _Phe
open _root_.P2Mf6bd8d28 renaming h632 → _Phk
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h417 (D : Family) (query : Str) (length : ℕ) :
    (_root_.InfoLossLAR.WorstCase.familyBlock D length (fun index => (query[index.val]?).getD false)).input=
      _root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.familyInputBits D query length) := by
  change basisInput (a := D.anc length) (fun index => (query[index.val]?).getD false)=_
  rw [_P9k]
  apply congrArg _root_.InfoLossLAR.WorstCase.computationalBasis
  funext index
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp [_root_.InfoLossLAR.WorstCase.familyInputBits,i.isLt]
  · simp (disch := omega) [_root_.InfoLossLAR.WorstCase.familyInputBits]
open _root_.P2Mf6bd8d28 renaming h417 → _Pbl
theorem _root_.P2Mf6bd8d28.h430 (D : Family) (query : Str) (lengths : List ℕ) :
    _root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.indexedQueryBlocks D query lengths)=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.InfoLossLAR.WorstCase.bundleNaturalBits D query lengths index.val) := by
  induction lengths with
  | nil =>
    change (fun _ : Bits 0 => (1 : ℂ))=_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ : Fin 0 => false)
    funext output
    have he : output=(fun _ : Fin 0 => false) := Subsingleton.elim _ _
    simp only [_root_.InfoLossLAR.WorstCase.computationalBasis,if_pos he]
  | cons length rest ih =>
    change _root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.familyBlock D length (fun index => (query[index.val]?).getD false)).input
      (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.indexedQueryBlocks D query rest))=_
    rw [_Pbl,ih,←_Pb5]
    apply congrArg _root_.InfoLossLAR.WorstCase.computationalBasis
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · have hi : i.val<length+(D.anc length+1) := i.isLt
      simp [_root_.InfoLossLAR.WorstCase.bundleNaturalBits,_root_.InfoLossLAR.WorstCase.familyInputBits,hi]
    · simp (disch := omega) [_root_.InfoLossLAR.WorstCase.bundleNaturalBits,_root_.InfoLossLAR.WorstCase.familyBlock]
open _root_.P2Mf6bd8d28 renaming h430 → _Pby
theorem _root_.P2Mf6bd8d28.h504 (D : Family) (maximum : ℕ) (query : Str) :
    _root_.InfoLossLAR.WorstCase.queryBlocks D maximum query=_root_.InfoLossLAR.WorstCase.indexedQueryBlocks D query (List.range (maximum+1)) := by
  have hmap {α : Type} (f : ℕ → α) :
      List.ofFn (fun index : Fin (maximum+1) => f index.val)=(List.range (maximum+1)).map f := by
    apply List.ext_getElem
    · simp
    · intro index hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  exact hmap (fun length => _root_.InfoLossLAR.WorstCase.familyBlock D length (fun index => (query[index.val]?).getD false))
open _root_.P2Mf6bd8d28 renaming h504 → _Pe0
theorem _root_.P2Mf6bd8d28.h511 (D : Family) (maximum : ℕ) (query : Str) :
    _root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query)=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.InfoLossLAR.WorstCase.bundleNaturalBits D query (List.range (maximum+1)) index.val) := by
  have h := _Pby D query (List.range (maximum+1))
  rw [←_Pe0 D maximum query] at h
  exact h
open _root_.P2Mf6bd8d28 renaming h511 → _Pe7
theorem _root_.P2Mf6bd8d28.h573 (sources : List (Bool × ℕ)) (state : ℕ → Bool) (index : ℕ)
    (hi : index < sources.length) :
    _root_.InfoLossLAR.WorstCase.sourceValueAt sources state index=_root_.InfoLossLAR.WorstCase.registerLoadValue sources[index] state := by
  simp only [_root_.InfoLossLAR.WorstCase.sourceValueAt,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]
open _root_.P2Mf6bd8d28 renaming h573 → _Pfx
theorem _root_.P2Mf6bd8d28.h572 (first second : List (Bool × ℕ)) (state : ℕ → Bool) (index : ℕ) :
    _root_.InfoLossLAR.WorstCase.sourceValueAt (first++second) state index=
      if index < first.length then _root_.InfoLossLAR.WorstCase.sourceValueAt first state index else _root_.InfoLossLAR.WorstCase.sourceValueAt second state (index-first.length) := by
  unfold _root_.InfoLossLAR.WorstCase.sourceValueAt
  by_cases hi : index < first.length
  · rw [List.getElem?_append_left hi,if_pos hi]
  · rw [List.getElem?_append_right (by omega),if_neg hi]
open _root_.P2Mf6bd8d28 renaming h572 → _Pfw
theorem _root_.P2Mf6bd8d28.h404 (querySources : List ℕ) (request slots : List Unit) (state : ℕ → Bool) (index : ℕ) :
    _root_.InfoLossLAR.WorstCase.sourceValueAt (_root_.InfoLossLAR.WorstCase.dBlockLoadSources querySources request slots) state index=
      if index < slots.length then
        (if index < request.length then state ((querySources[index]?).getD 0) else false)
      else false := by
  unfold _root_.InfoLossLAR.WorstCase.sourceValueAt _root_.InfoLossLAR.WorstCase.dBlockLoadSources
  by_cases hi : index < slots.length
  · rw [List.getElem?_map,List.getElem?_range hi]
    simp only [Option.map_some,Option.getD_some,_root_.InfoLossLAR.WorstCase.registerLoadValue,decide_eq_true_eq,if_pos hi]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [hi]
open _root_.P2Mf6bd8d28 renaming h404 → _Pb8
theorem _root_.P2Mf6bd8d28.h409 (D : Family) (maximum : ℕ) :
    _root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum=_root_.InfoLossLAR.WorstCase.lengthDescriptions D (List.range (maximum+1)) := by
  apply List.ext_getElem
  · simp [_root_.InfoLossLAR.WorstCase.describedQueryBlocks,_root_.InfoLossLAR.WorstCase.lengthDescriptions]
  · intro index hi hj
    simp only [_root_.InfoLossLAR.WorstCase.describedQueryBlocks,_root_.InfoLossLAR.WorstCase.lengthDescriptions,List.getElem_map,List.getElem_range,List.getElem_ofFn]
open _root_.P2Mf6bd8d28 renaming h409 → _Pbd
theorem _root_.P2Mf6bd8d28.h408 (D : Family) (query : Str) (lengths : List ℕ)
    (querySources : List ℕ) (state : ℕ → Bool)
    (hq : ∀ length∈lengths,∀ index < length,state ((querySources[index]?).getD 0)=(query[index]?).getD false)
    (index : ℕ) :
    _root_.InfoLossLAR.WorstCase.sourceValueAt (_root_.InfoLossLAR.WorstCase.dBundleLoadSources querySources (_root_.InfoLossLAR.WorstCase.lengthDescriptions D lengths)) state index=
      _root_.InfoLossLAR.WorstCase.bundleNaturalBits D query lengths index := by
  induction lengths generalizing index with
  | nil => rfl
  | cons length rest ih =>
    unfold _root_.InfoLossLAR.WorstCase.lengthDescriptions _root_.InfoLossLAR.WorstCase.dBundleLoadSources
    simp only [List.map_cons,List.flatMap_cons,_root_.InfoLossLAR.WorstCase.readFamilyFrame_correct]
    simp only [unary,List.map_replicate]
    rw [_Pfw,_root_.InfoLossLAR.WorstCase.dBlockLoadSources_length]
    simp only [List.length_replicate]
    by_cases hi : index < length+(D.anc length+1)
    · rw [if_pos hi,_Pb8]
      simp only [List.length_replicate,if_pos hi,_root_.InfoLossLAR.WorstCase.bundleNaturalBits]
      by_cases hj : index < length
      · rw [if_pos hj,if_pos hj,hq length (by simp) index hj]
      · rw [if_neg hj,if_neg hj]
    · rw [if_neg hi]
      change _root_.InfoLossLAR.WorstCase.sourceValueAt (_root_.InfoLossLAR.WorstCase.dBundleLoadSources querySources (_root_.InfoLossLAR.WorstCase.lengthDescriptions D rest)) state
        (index-(length+(D.anc length+1)))=_
      rw [ih (fun other ho => hq other (by simp [ho]))]
      simp only [_root_.InfoLossLAR.WorstCase.bundleNaturalBits,if_neg hi]
open _root_.P2Mf6bd8d28 renaming h408 → _Pbc
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h404 → _Pb8
open _root_.P2Mf6bd8d28 renaming h408 → _Pbc
open _root_.P2Mf6bd8d28 renaming h409 → _Pbd
open _root_.P2Mf6bd8d28 renaming h417 → _Pbl
open _root_.P2Mf6bd8d28 renaming h430 → _Pby
open _root_.P2Mf6bd8d28 renaming h504 → _Pe0
open _root_.P2Mf6bd8d28 renaming h511 → _Pe7
open _root_.P2Mf6bd8d28 renaming h572 → _Pfw
open _root_.P2Mf6bd8d28 renaming h573 → _Pfx
end
open _root_.P2Mf6bd8d28 renaming h404 → _Pb8
open _root_.P2Mf6bd8d28 renaming h408 → _Pbc
open _root_.P2Mf6bd8d28 renaming h409 → _Pbd
open _root_.P2Mf6bd8d28 renaming h417 → _Pbl
open _root_.P2Mf6bd8d28 renaming h430 → _Pby
open _root_.P2Mf6bd8d28 renaming h504 → _Pe0
open _root_.P2Mf6bd8d28 renaming h511 → _Pe7
open _root_.P2Mf6bd8d28 renaming h572 → _Pfw
open _root_.P2Mf6bd8d28 renaming h573 → _Pfx
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
theorem _root_.P2Mf6bd8d28.h704 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (index : ℕ) :
    _root_.InfoLossLAR.WorstCase.sourceValueAt (_root_.Integration9_9.LARCoinLayout.bodySources coins padding fallback D word.length)
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word) index=
      _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) (List.range (padding.eval word.length+1)) index := by
  unfold _root_.Integration9_9.LARCoinLayout.bodySources
  rw [_Pbd]
  apply _Pbc
  intro length hl j hj
  have hlen : length ≤ padding.eval word.length := by
    have := List.mem_range.mp hl
    omega
  have hjp : j < padding.eval word.length := by omega
  have hjs : j < (_root_.Integration9_9.LARCoinLayout.bodyPayloadAddresses coins padding fallback (unary word.length)).length := by
    simpa only [_Pjv,unary,List.length_replicate] using hjp
  rw [List.getElem?_eq_getElem hjs,Option.getD_some]
  exact _Pjx coins padding fallback word j hjp
open _root_.P2Mf6bd8d28 renaming h704 → _Pjk
theorem _root_.P2Mf6bd8d28.h721 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (index : ℕ) (hi : index < _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length) :
    _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word index=
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word index :=
  _P6l _ _ _ _ hi
open _root_.P2Mf6bd8d28 renaming h721 → _Pk1
theorem _root_.P2Mf6bd8d28.h719 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (index : ℕ) (hi : index < _root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length) :
    _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word
      (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+index)=
      _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) (List.range (padding.eval word.length+1)) index := by
  have his : index < (_root_.Integration9_9.LARCoinLayout.bodySources coins padding fallback D word.length).length := by
    simpa only [_root_.Integration9_9.LARCoinLayout.bodySources_length] using hi
  unfold _root_.Integration9_9.LARCoinLayout.bodyPreparedBits _root_.Integration9_9.LARCoinLayout.bodyPreWidth
  rw [_P6n (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word
    (_root_.Integration9_9.LARCoinLayout.bodySources coins padding fallback D word.length)
    (_Pjj coins padding fallback D word.length) index his]
  rw [←_Pfx _ _ index his,_Pjk]
open _root_.P2Mf6bd8d28 renaming h719 → _Pjz
theorem _root_.P2Mf6bd8d28.h720 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (index : ℕ)
    (hi : _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length ≤ index) :
    _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word index=false := by
  unfold _root_.Integration9_9.LARCoinLayout.bodyPreparedBits
  rw [_P45]
  · exact _P8o word index (by unfold _root_.Integration9_9.LARCoinLayout.bodyPreWidth at hi; omega)
  · rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps_length,_root_.Integration9_9.LARCoinLayout.bodySources_length]
    unfold _root_.Integration9_9.LARCoinLayout.bodyPreWidth at hi
    omega
open _root_.P2Mf6bd8d28 renaming h720 → _Pk0
theorem _root_.P2Mf6bd8d28.h722 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.LARCoinLayout.bodyPreparedGates coins padding fallback D word.length)))
      (basisInput (a := _root_.Integration9_9.LARCoinLayout.bodyAnc coins padding fallback D word.length) (toBits word))=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word index.val) := by
  rw [_P9k,_P8p]
  unfold _root_.Integration9_9.LARCoinLayout.bodyPreparedGates _root_.Integration9_9.LARCoinLayout.bodyPreparedBits _root_.InfoLossLAR.WorstCase.computationalBasis
  exact _P3y _ _ (_Pk5 coins padding fallback D word.length)
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) (fun index hi _ => _P8o word index hi)
open _root_.P2Mf6bd8d28 renaming h722 → _Pk2
theorem _root_.P2Mf6bd8d28.h734 {left right : ℕ} (h : left=right) (bits : Bits left) :
    _root_.Integration9_9.LARCoinLayout.castBodyState h (_root_.InfoLossLAR.WorstCase.computationalBasis bits)=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => bits (Fin.cast h.symm index)) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h734 → _Pke
theorem _root_.P2Mf6bd8d28.h751 {left right : ℕ} (h : left=right)
    (circuit : Layered left) (state : QState left) :
    runLayered (_root_.Integration9_9.LARCoinLayout.castBodyCircuit h circuit) (_root_.Integration9_9.LARCoinLayout.castBodyState h state)=
      _root_.Integration9_9.LARCoinLayout.castBodyState h (runLayered circuit state) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h751 → _Pkv
theorem _root_.P2Mf6bd8d28.h724 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+
      _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))+
      (4*(padding.eval word.length+1)+1)=_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length := by
  rw [_Pe5 D _ (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) [],_root_.Integration9_9.LARCoinLayout.bodyWidth_formula]
  rfl
open _root_.P2Mf6bd8d28 renaming h724 → _Pk4
theorem _root_.P2Mf6bd8d28.h723 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    _root_.InfoLossLAR.WorstCase.computationalBasis (fun index : Fin (_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length) =>
      _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word index.val)=
      _root_.Integration9_9.LARCoinLayout.castBodyState (_Pk4 coins padding fallback D word)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word))
            (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) := by
  rw [_Pe7,←_Pb5,←_Pb5,_Pke]
  apply congrArg _root_.InfoLossLAR.WorstCase.computationalBasis
  have hwidth := _Pe5 D (padding.eval word.length)
    (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) []
  have hbits (index : Fin ((_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+
      _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))+
      (4*(padding.eval word.length+1)+1))) :
      _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word index.val=
        (Fin.append (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word)
          (fun index => _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)
            (List.range (padding.eval word.length+1)) index.val)) (fun _ => false)) index := by
    refine Fin.addCases (fun block => ?_) (fun scratch => ?_) index
    · refine Fin.addCases (fun previous => ?_) (fun data => ?_) block
      · simp only [Fin.val_castAdd,Fin.append_left]
        rw [_Pk1 _ _ _ _ _ _ previous.isLt]
        exact _root_.InfoLossLAR.WorstCase.selectorBitsExtension_get _ previous
      · simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left]
        dsimp only [_root_.Integration9_9.LARCoinLayout.bodyPreWidth] at *
        rw [Fin.append_right]
        change _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word
          (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+data.val)=
          _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)
            (List.range (padding.eval word.length+1)) data.val
        exact _Pjz coins padding fallback D word data.val (by
          change data.val < _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) [])
          rw [←hwidth]
          exact data.isLt)
    · simp only [Fin.val_natAdd]
      dsimp only [_root_.Integration9_9.LARCoinLayout.bodyPreWidth] at *
      rw [Fin.append_right]
      change _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word
        (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+
          _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word))+scratch.val)=false
      apply _Pk0
      change _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+
        _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) []) ≤ _
      rw [←hwidth]
      omega
  funext index
  simpa only [Fin.val_cast] using hbits (Fin.cast (_Pk4 coins padding fallback D word).symm index)
open _root_.P2Mf6bd8d28 renaming h723 → _Pk3
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h704 → _Pjk
open _root_.P2Mf6bd8d28 renaming h719 → _Pjz
open _root_.P2Mf6bd8d28 renaming h720 → _Pk0
open _root_.P2Mf6bd8d28 renaming h721 → _Pk1
open _root_.P2Mf6bd8d28 renaming h722 → _Pk2
open _root_.P2Mf6bd8d28 renaming h723 → _Pk3
open _root_.P2Mf6bd8d28 renaming h724 → _Pk4
open _root_.P2Mf6bd8d28 renaming h734 → _Pke
open _root_.P2Mf6bd8d28 renaming h751 → _Pkv
end
end
open _root_.P2Mf6bd8d28 renaming h704 → _Pjk
open _root_.P2Mf6bd8d28 renaming h719 → _Pjz
open _root_.P2Mf6bd8d28 renaming h720 → _Pk0
open _root_.P2Mf6bd8d28 renaming h721 → _Pk1
open _root_.P2Mf6bd8d28 renaming h722 → _Pk2
open _root_.P2Mf6bd8d28 renaming h723 → _Pk3
open _root_.P2Mf6bd8d28 renaming h724 → _Pk4
open _root_.P2Mf6bd8d28 renaming h734 → _Pke
open _root_.P2Mf6bd8d28 renaming h751 → _Pkv
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
theorem _root_.P2Mf6bd8d28.h747 {left right total : ℕ} (first : Layered left) (second : Layered right)
    (h : (⟨left,first⟩ : Σ width : ℕ,Layered width)=⟨right,second⟩)
    (hf : left=total) (hs : right=total) :
    _root_.Integration9_9.LARCoinLayout.castBodyCircuit hf first=_root_.Integration9_9.LARCoinLayout.castBodyCircuit hs second := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h747 → _Pkr
theorem _root_.P2Mf6bd8d28.h702 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    _root_.Integration9_9.LARCoinLayout.bodyDCircuit coins padding fallback D word.length=
      _root_.Integration9_9.LARCoinLayout.castBodyCircuit (_Pk4 coins padding fallback D word)
        (_root_.InfoLossLAR.WorstCase.leftCircuit (m := 4*(padding.eval word.length+1)+1)
          (_root_.InfoLossLAR.WorstCase.rightCircuit (n := _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length)
            (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word))))) := by
  have h := congrArg (fun circuit : (Σ width : ℕ,Layered width) =>
      (⟨(_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+circuit.1)+(4*(padding.eval word.length+1)+1),
        _root_.InfoLossLAR.WorstCase.leftCircuit (m := 4*(padding.eval word.length+1)+1)
          (_root_.InfoLossLAR.WorstCase.rightCircuit (n := _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length) circuit.2)⟩ :
        Σ width : ℕ,Layered width))
    (_Pe2 D (padding.eval word.length) [] (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word))
  unfold _root_.Integration9_9.LARCoinLayout.bodyDCircuit
  exact _Pkr _ _ h _ _
open _root_.P2Mf6bd8d28 renaming h702 → _Pji
theorem _root_.P2Mf6bd8d28.h705 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    runLayered (_root_.Integration9_9.LARCoinLayout.bodyDCircuit coins padding fallback D word.length)
      (_root_.InfoLossLAR.WorstCase.computationalBasis (fun index : Fin (_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length) =>
        _root_.Integration9_9.LARCoinLayout.bodyPreparedBits coins padding fallback D word index.val))=
      _root_.Integration9_9.LARCoinLayout.castBodyState (_Pk4 coins padding fallback D word)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word))
            (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))
              (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) := by
  rw [_Pk3,_Pji,_Pkv,_Pcq,_Pfc]
open _root_.P2Mf6bd8d28 renaming h705 → _Pjl
theorem _root_.P2Mf6bd8d28.h750 {width : ℕ} (first second : Layered width) (state : QState width) :
    runLayered (first++second) state=runLayered second (runLayered first state) := List.foldl_append
open _root_.P2Mf6bd8d28 renaming h750 → _Pku
theorem _root_.P2Mf6bd8d28.h712 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.LARCoinLayout.bodyPreparedGates coins padding fallback D word.length))++
        _root_.Integration9_9.LARCoinLayout.bodyDCircuit coins padding fallback D word.length)
      (basisInput (a := _root_.Integration9_9.LARCoinLayout.bodyAnc coins padding fallback D word.length) (toBits word))=
      _root_.Integration9_9.LARCoinLayout.castBodyState (_Pk4 coins padding fallback D word)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word))
            (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))
              (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) := by
  rw [_Pku,_Pk2,_Pjl]
open _root_.P2Mf6bd8d28 renaming h712 → _Pjs
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h702 → _Pji
open _root_.P2Mf6bd8d28 renaming h705 → _Pjl
open _root_.P2Mf6bd8d28 renaming h712 → _Pjs
open _root_.P2Mf6bd8d28 renaming h747 → _Pkr
open _root_.P2Mf6bd8d28 renaming h750 → _Pku
end
end
open _root_.P2Mf6bd8d28 renaming h702 → _Pji
open _root_.P2Mf6bd8d28 renaming h705 → _Pjl
open _root_.P2Mf6bd8d28 renaming h712 → _Pjs
open _root_.P2Mf6bd8d28 renaming h747 → _Pkr
open _root_.P2Mf6bd8d28 renaming h750 → _Pku
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h575 {left right : ℕ} (state : QState left)
    (bits : Bits right) (event : Bits (left+right) → Bool) :
    (∑ input : Bits (left+right),if event input then
      ‖_root_.InfoLossLAR.WorstCase.tensorState state (_root_.InfoLossLAR.WorstCase.computationalBasis bits) input‖^2 else 0)=
      ∑ input : Bits left,if event (Fin.append input bits) then ‖state input‖^2 else 0 := by
  classical
  have hsplit (input : Bits (left+right)) :
      Fin.append (_root_.InfoLossLAR.WorstCase.leftRegister input) (_root_.InfoLossLAR.WorstCase.rightRegister input)=input := by
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,_root_.InfoLossLAR.WorstCase.leftRegister]
    · simp only [Fin.append_right,_root_.InfoLossLAR.WorstCase.rightRegister]
  have hsum := _Pfy (fun first : Bits left => fun second : Bits right =>
    if event (Fin.append first second) then ‖state first*_root_.InfoLossLAR.WorstCase.computationalBasis bits second‖^2 else 0)
  simp only [hsplit] at hsum
  change (∑ input : Bits (left+right),if event input then
    ‖state (_root_.InfoLossLAR.WorstCase.leftRegister input)*_root_.InfoLossLAR.WorstCase.computationalBasis bits (_root_.InfoLossLAR.WorstCase.rightRegister input)‖^2 else 0)=_
  rw [hsum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_eq_single bits]
  · simp [_root_.InfoLossLAR.WorstCase.computationalBasis]
  · intro second _ hne
    simp [_root_.InfoLossLAR.WorstCase.computationalBasis,hne]
  · simp
open _root_.P2Mf6bd8d28 renaming h575 → _Pfz
theorem _root_.P2Mf6bd8d28.h560 {left right : ℕ} (first : Bits left) (second : Bits right)
    (index : ℕ) (hi : index < left) :
    _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append first second) index=_root_.InfoLossLAR.WorstCase.selectorBitsExtension first index := by
  have htotal : index < left+right := by omega
  change (if h : index < left+right then _ else false)=_
  rw [dif_pos htotal]
  have hindex : (⟨index,htotal⟩ : Fin (left+right))=Fin.castAdd right ⟨index,hi⟩ := rfl
  rw [hindex,Fin.append_left]
  simp [_root_.InfoLossLAR.WorstCase.selectorBitsExtension,hi]
open _root_.P2Mf6bd8d28 renaming h560 → _Pfk
theorem _root_.P2Mf6bd8d28.h480 {start left : ℕ} (choices : List (ℕ × ℕ))
    (hl : left < start) (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (state : QState start) :
    (∑ output : Bits (start+(4*choices.length+1)),if output
        ⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,by
          have := _root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
        (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
          (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; omega))))
        (_root_.InfoLossLAR.WorstCase.tensorState state (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) output‖^2 else 0)=
      ∑ input : Bits start,if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
        (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  classical
  rw [_Pdb choices hl hc (by omega)]
  · rw [_Pfz]
    apply Finset.sum_congr rfl
    intro input _
    rw [_Pfk input _ left hl]
    rw [_Pd8 choices _ (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input) _ (fun choice hm => by
      have h := hc choice hm
      exact ⟨_Pfk input _ choice.1 h.1,
        _Pfk input _ choice.2 h.2⟩)]
  · intro input hi index hlow hhigh
    have hright : _root_.InfoLossLAR.WorstCase.rightRegister input=(fun _ : Fin (4*choices.length+1) => false) := by
      by_contra hn
      apply hi
      simp [_root_.InfoLossLAR.WorstCase.tensorState,_root_.InfoLossLAR.WorstCase.computationalBasis,hn]
    have hindex : index < start+(4*choices.length+1) := by omega
    have hoffset : index-start < 4*choices.length+1 := by omega
    change (if h : index < start+(4*choices.length+1) then input ⟨index,h⟩ else false)=false
    rw [dif_pos hindex]
    have heq : (⟨index,hindex⟩ : Fin (start+(4*choices.length+1)))=
        Fin.natAdd start ⟨index-start,hoffset⟩ := by apply Fin.ext; simp; omega
    rw [heq]
    exact congrFun hright ⟨index-start,hoffset⟩
open _root_.P2Mf6bd8d28 renaming h480 → _Pdc
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h480 → _Pdc
open _root_.P2Mf6bd8d28 renaming h560 → _Pfk
open _root_.P2Mf6bd8d28 renaming h575 → _Pfz
end
open _root_.P2Mf6bd8d28 renaming h480 → _Pdc
open _root_.P2Mf6bd8d28 renaming h560 → _Pfk
open _root_.P2Mf6bd8d28 renaming h575 → _Pfz
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h736 {left first second right total : ℕ}
    (h : first=second) (hfirst : (left+first)+right=total)
    (hsecond : (left+second)+right=total)
    (prefixState : QState left) (middleState : QState first) (suffixState : QState right) :
    _root_.Integration9_9.LARCoinLayout.castBodyState hfirst (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.tensorState prefixState middleState) suffixState)=
      _root_.Integration9_9.LARCoinLayout.castBodyState hsecond (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.tensorState prefixState (_root_.Integration9_9.LARCoinLayout.castBodyState h middleState)) suffixState) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h736 → _Pkg
theorem _root_.P2Mf6bd8d28.h745 {start left total : ℕ} (choices : List (ℕ × ℕ))
    (hl : left < start) (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (h : start+(4*choices.length+1)=total) (state : QState start) :
    (∑ output : Bits total,if output
        ⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,by
          have := _root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
        (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
          (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; omega))))
        (_root_.Integration9_9.LARCoinLayout.castBodyState h (_root_.InfoLossLAR.WorstCase.tensorState state (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false)))) output‖^2 else 0)=
      ∑ input : Bits start,if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
        (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  cases h
  exact _Pdc choices hl hc state
open _root_.P2Mf6bd8d28 renaming h745 → _Pkp
theorem _root_.P2Mf6bd8d28.h746 {start left total scratch : ℕ}
    (choices : List (ℕ × ℕ)) (hl : left < start)
    (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (hsize : scratch=4*choices.length+1) (h : start+scratch=total) (state : QState start) :
    (∑ output : Bits total,if output
        ⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,by
          have := _root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
        (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
          (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; omega))))
        (_root_.Integration9_9.LARCoinLayout.castBodyState h (_root_.InfoLossLAR.WorstCase.tensorState state (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false)))) output‖^2 else 0)=
      ∑ input : Bits start,if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
        (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  subst scratch
  exact _Pkp choices hl hc h state
open _root_.P2Mf6bd8d28 renaming h746 → _Pkq
theorem _root_.P2Mf6bd8d28.h711 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.LARCoinLayout.bodyPreparedGates coins padding fallback D word.length))++
        _root_.Integration9_9.LARCoinLayout.bodyDCircuit coins padding fallback D word.length)
      (basisInput (a := _root_.Integration9_9.LARCoinLayout.bodyAnc coins padding fallback D word.length) (toBits word))=
      _root_.Integration9_9.LARCoinLayout.castBodyState (by rw [_root_.Integration9_9.LARCoinLayout.bodyWidth_formula]; rfl)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word))
            (_root_.Integration9_9.LARCoinLayout.castBodyState (_Pe5 D _ (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) [])
              (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))
                (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word))))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ : Fin (4*(padding.eval word.length+1)+1) => false))) := by
  rw [_Pjs]
  exact _Pkg (_Pe5 D _ (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) [])
    _ _ _ _ _
open _root_.P2Mf6bd8d28 renaming h711 → _Pjr
theorem _root_.P2Mf6bd8d28.h707 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) :
    acceptProb (_root_.Integration9_9.LARCoinLayout.bodyFamily coins padding fallback D) word=
      ∑ input : Bits (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length),
        if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input) (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input 0)
          (_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length) then
          ‖_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word))
            (_root_.Integration9_9.LARCoinLayout.castBodyState (_Pe5 D _ (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) [])
              (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word)))
                (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word))))) input‖^2 else 0 := by
  change (∑ output : Bits (_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length),if output
    (_root_.Integration9_9.LARCoinLayout.bodyOutput coins padding fallback D word.length) then
    ‖runLayered (_root_.Integration9_9.LARCoinLayout.bodyCircuit coins padding fallback D word.length)
      (basisInput (a := _root_.Integration9_9.LARCoinLayout.bodyAnc coins padding fallback D word.length) (toBits word)) output‖^2 else 0)=_
  unfold _root_.Integration9_9.LARCoinLayout.bodyCircuit
  rw [_Pku,_Pjr]
  apply _Pkq
  · unfold _root_.Integration9_9.LARCoinLayout.bodyPreWidth
    omega
  · have h := _Pk9 coins padding fallback D word.length
    rw [_Pjy,_root_.Integration9_9.LARCoinLayout.bodyDBundleSlots_length D _ []] at h
    exact h
  · rw [_root_.Integration9_9.LARCoinLayout.bodyChoices_length]
open _root_.P2Mf6bd8d28 renaming h707 → _Pjn
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h707 → _Pjn
open _root_.P2Mf6bd8d28 renaming h711 → _Pjr
open _root_.P2Mf6bd8d28 renaming h736 → _Pkg
open _root_.P2Mf6bd8d28 renaming h745 → _Pkp
open _root_.P2Mf6bd8d28 renaming h746 → _Pkq
end
end
open _root_.P2Mf6bd8d28 renaming h707 → _Pjn
open _root_.P2Mf6bd8d28 renaming h711 → _Pjr
open _root_.P2Mf6bd8d28 renaming h736 → _Pkg
open _root_.P2Mf6bd8d28 renaming h745 → _Pkp
open _root_.P2Mf6bd8d28 renaming h746 → _Pkq
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h345 {left right : ℕ} (bits : Bits left)
    (state : QState right) (event : Bits (left+right) → Bool) :
    (∑ input : Bits (left+right),if event input then
      ‖_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis bits) state input‖^2 else 0)=
      ∑ input : Bits right,if event (Fin.append bits input) then ‖state input‖^2 else 0 := by
  classical
  have hsplit (input : Bits (left+right)) :
      Fin.append (_root_.InfoLossLAR.WorstCase.leftRegister input) (_root_.InfoLossLAR.WorstCase.rightRegister input)=input := by
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,_root_.InfoLossLAR.WorstCase.leftRegister]
    · simp only [Fin.append_right,_root_.InfoLossLAR.WorstCase.rightRegister]
  have hsum := _Pfy (fun first : Bits left => fun second : Bits right =>
    if event (Fin.append first second) then ‖_root_.InfoLossLAR.WorstCase.computationalBasis bits first*state second‖^2 else 0)
  simp only [hsplit] at hsum
  change (∑ input : Bits (left+right),if event input then
    ‖_root_.InfoLossLAR.WorstCase.computationalBasis bits (_root_.InfoLossLAR.WorstCase.leftRegister input)*state (_root_.InfoLossLAR.WorstCase.rightRegister input)‖^2 else 0)=_
  rw [hsum,Finset.sum_eq_single bits]
  · simp [_root_.InfoLossLAR.WorstCase.computationalBasis]
  · intro first _ hne
    simp [_root_.InfoLossLAR.WorstCase.computationalBasis,hne]
  · simp
open _root_.P2Mf6bd8d28 renaming h345 → _P9l
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h345 → _P9l
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial QMCNumericRuntime TM2PlatformSerialization
open scoped BigOperators
private theorem _root_.P2Mf6bd8d28.h851 {α : Type} {length : ℕ} (items : List α)
    (f : Fin length → α) (h : items=List.ofFn f) (index : ℕ)
    (hi : index < items.length) (hn : index < length) : items[index]=f ⟨index,hn⟩ := by
  subst items
  simp only [List.getElem_ofFn]
open _root_.P2Mf6bd8d28 renaming h851 → _Pnn
theorem _root_.P2Mf6bd8d28.h701 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (n index : ℕ) (hi : index ≤ padding.eval n) :
    (_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D n)[index]'(by rw [_root_.Integration9_9.LARCoinLayout.bodyChoices_length]; omega)=
      ((_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses coins padding fallback (unary n))[index]'(by
        simp only [_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses_length,unary,List.length_replicate]; omega),
      _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback n+
        (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval n) [])
          ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val) := by
  have htoken (hit : index < (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval n))).length) :
      (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (padding.eval n)))[index]=
        encNat (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval n) [])
          ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val :=
    _Pnn _ _ (_root_.InfoLossLAR.WorstCase.emitDOutputs_correct D (padding.eval n) []) index hit _
  have hn (number : ℕ) : QMCNumericRuntime.inputWidth (encNat number)=number := by
    rw [←_root_.InfoLossLAR.WorstCase.unaryPayload_length,_root_.InfoLossLAR.WorstCase.unaryPayload_number]
    simp only [unary,List.length_replicate]
  unfold _root_.Integration9_9.LARCoinLayout.bodyChoices _root_.Integration9_9.LARCoinLayout.bodySelectorChoices
  simp only [List.getElem_zip,List.getElem_map,_Pjy,htoken,hn]
  rfl
open _root_.P2Mf6bd8d28 renaming h701 → _Pjh
theorem _root_.P2Mf6bd8d28.h699 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (data : Bits (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length)) (index : ℕ)
    (hi : index ≤ padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word) data)
      ((_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length)[index]'(by rw [_root_.Integration9_9.LARCoinLayout.bodyChoices_length]; omega)).1=
      decide ((_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length=index) := by
  rw [_Pjh coins padding fallback D word.length index hi]
  have hb := _Pjt coins padding fallback word.length
    ((_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses coins padding fallback (unary word.length))[index]'(by
      simp only [_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses_length,unary,List.length_replicate]; omega))
    (List.getElem_mem (by simp only [_root_.Integration9_9.LARCoinLayout.bodyFlagAddresses_length,unary,List.length_replicate]; omega))
  rw [_Pfk _ data _ hb]
  exact _Pju coins padding fallback word index hi
open _root_.P2Mf6bd8d28 renaming h699 → _Pjf
theorem _root_.P2Mf6bd8d28.h700 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (data : Bits (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length)) (index : ℕ)
    (hi : index ≤ padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word) data)
      ((_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length)[index]'(by rw [_root_.Integration9_9.LARCoinLayout.bodyChoices_length]; omega)).2=
      data (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) [])
        ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩) := by
  rw [_Pjh coins padding fallback D word.length index hi]
  let output := _root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) [])
    (⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩ : Fin _)
  change _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word) data)
    (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+output.val)=data output
  have heq : _root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+output.val=
      (Fin.natAdd (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length) output).val := rfl
  rw [heq,_root_.InfoLossLAR.WorstCase.selectorBitsExtension_get]
  dsimp only [_root_.Integration9_9.LARCoinLayout.bodyPreWidth] at *
  rw [Fin.append_right]
open _root_.P2Mf6bd8d28 renaming h700 → _Pjg
theorem _root_.P2Mf6bd8d28.h730 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (data : Bits (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length))
    (hq : (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length ≤ padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.multiSelectorValue
      (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word) data))
      (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word) data) 0)
      (_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length)=
      data (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) [])
        ⟨(_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩) := by
  apply _Pda
  · intro choice hc htrue
    obtain ⟨index,hi,he⟩ := List.getElem_of_mem hc
    have himax : index ≤ padding.eval word.length := by rw [_root_.Integration9_9.LARCoinLayout.bodyChoices_length] at hi; omega
    rw [←he,_Pjf _ _ _ _ _ _ _ himax] at htrue
    have heq : (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length=index := of_decide_eq_true htrue
    rw [←he,_Pjg _ _ _ _ _ _ _ himax]
    subst index
    rfl
  · refine ⟨(_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length)[(_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length]'(by
      rw [_root_.Integration9_9.LARCoinLayout.bodyChoices_length]; omega),List.getElem_mem _,?_⟩
    rw [_Pjf _ _ _ _ _ _ _ hq]
    simp
open _root_.P2Mf6bd8d28 renaming h730 → _Pka
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h699 → _Pjf
open _root_.P2Mf6bd8d28 renaming h700 → _Pjg
open _root_.P2Mf6bd8d28 renaming h701 → _Pjh
open _root_.P2Mf6bd8d28 renaming h730 → _Pka
open _root_.P2Mf6bd8d28 renaming h851 → _Pnn
end
end
open _root_.P2Mf6bd8d28 renaming h345 → _P9l
open _root_.P2Mf6bd8d28 renaming h699 → _Pjf
open _root_.P2Mf6bd8d28 renaming h700 → _Pjg
open _root_.P2Mf6bd8d28 renaming h701 → _Pjh
open _root_.P2Mf6bd8d28 renaming h730 → _Pka
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity QMCNumericRuntime Integration9_9.TM2PlatformSerialization
private theorem _root_.P2Mf6bd8d28.h853 {α : Type} {length : ℕ} (items : List α)
    (f : Fin length → α) (h : items=List.ofFn f) (index : ℕ)
    (hi : index < items.length) (hn : index < length) : items[index]=f ⟨index,hn⟩ := by
  subst items
  simp only [List.getElem_ofFn]
open _root_.P2Mf6bd8d28 renaming h853 → _Pnp
private theorem _root_.P2Mf6bd8d28.h852 (D : Family) (maximum : ℕ) (query : Str)
    (index : ℕ) (hi : index ≤ maximum)
    (hit : index < (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum)).length) :
    (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum))[index]=
      encNat (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum query)
        ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val :=
  _Pnp _ _ (_root_.InfoLossLAR.WorstCase.emitDOutputs_correct D maximum query) index hit _
open _root_.P2Mf6bd8d28 renaming h852 → InfoLossLAR.WorstCase.emittedOutput_get
open _root_.P2Mf6bd8d28 renaming h852 → _Pno
theorem _root_.P2Mf6bd8d28.h505 (D : Family) (maximum : ℕ) (first second : Str)
    (index : ℕ) (hi : index ≤ maximum) :
    (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum first) ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val=
      (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D maximum second) ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val := by
  have hit : index < (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D maximum)).length := by
    rw [_root_.InfoLossLAR.WorstCase.emitDOutputs_correct D maximum first]
    simpa only [List.length_ofFn,_root_.InfoLossLAR.WorstCase.queryBlocks] using (show index < maximum+1 by omega)
  have h := (_Pno D maximum first index hi hit).symm.trans
    (_Pno D maximum second index hi hit)
  have hd := congrArg inputWidth h
  have hn (number : ℕ) : inputWidth (encNat number)=number := by
    rw [←_root_.InfoLossLAR.WorstCase.unaryPayload_length,_root_.InfoLossLAR.WorstCase.unaryPayload_number]
    simp only [unary,List.length_replicate]
  simpa only [hn] using hd
open _root_.P2Mf6bd8d28 renaming h505 → _Pe1
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h505 → _Pe1
open _root_.P2Mf6bd8d28 renaming h852 → InfoLossLAR.WorstCase.emittedOutput_get
open _root_.P2Mf6bd8d28 renaming h852 → _Pno
open _root_.P2Mf6bd8d28 renaming h853 → _Pnp
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h735 {left right : ℕ} (h : left=right)
    (state : QState left) (output : Fin left) :
    (∑ input : Bits right,if input (Fin.cast h output) then ‖_root_.Integration9_9.LARCoinLayout.castBodyState h state input‖^2 else 0)=
      ∑ input : Bits left,if input output then ‖state input‖^2 else 0 := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h735 → _Pkf
attribute [local irreducible] coinFirstPre bodyQueryProgram
theorem _root_.P2Mf6bd8d28.h706 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (hq : (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word).length ≤ padding.eval word.length) :
    acceptProb (_root_.Integration9_9.LARCoinLayout.bodyFamily coins padding fallback D) word=acceptProb D (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) := by
  let P := _root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback
  let query := _root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word
  let blocks := _root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) query
  let changeWidth := _Pe5 D (padding.eval word.length) query []
  let dstate := runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks) (_root_.InfoLossLAR.WorstCase.bundleState blocks)
  let choices := _root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length
  let selected : Fin (_root_.InfoLossLAR.WorstCase.bundleWidth blocks) := _root_.InfoLossLAR.WorstCase.bundleOutput blocks
    ⟨query.length,by dsimp only [blocks,query]; simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩
  let physical : Fin (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length) := _root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (padding.eval word.length) [])
    ⟨query.length,by dsimp only [query]; simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩
  have hselected : physical=Fin.cast changeWidth selected := by
    apply Fin.ext
    exact _Pe1 D (padding.eval word.length) [] query query.length hq
  calc
    acceptProb (_root_.Integration9_9.LARCoinLayout.bodyFamily coins padding fallback D) word=
        ∑ input : Bits (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length),
          if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input) (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input 0) choices then
            ‖_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word)) (_root_.Integration9_9.LARCoinLayout.castBodyState changeWidth dstate) input‖^2 else 0 :=
      _Pjn coins padding fallback D word
    _=∑ input : Bits (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length),
        if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) input))
          (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) input) 0) choices then
          ‖_root_.Integration9_9.LARCoinLayout.castBodyState changeWidth dstate input‖^2 else 0 :=
      _P9l (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) (_root_.Integration9_9.LARCoinLayout.castBodyState changeWidth dstate) _
    _=∑ input : Bits (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length),
        if input physical then ‖_root_.Integration9_9.LARCoinLayout.castBodyState changeWidth dstate input‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro input _
      have he := _Pka coins padding fallback D word input hq
      exact congrArg (fun value : Bool => if value then ‖_root_.Integration9_9.LARCoinLayout.castBodyState changeWidth dstate input‖^2 else 0) he
    _=∑ input : Bits (_root_.InfoLossLAR.WorstCase.bundleWidth blocks),if input selected then ‖dstate input‖^2 else 0 := by
      exact (congrArg (fun wire : Fin (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length) =>
        ∑ input : Bits (_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length),if input wire then
          ‖_root_.Integration9_9.LARCoinLayout.castBodyState changeWidth dstate input‖^2 else 0) hselected).trans
        (_Pkf changeWidth dstate selected)
    _=acceptProb D query := _Pe3 D (padding.eval word.length) query hq
open _root_.P2Mf6bd8d28 renaming h706 → _Pjm
theorem _root_.P2Mf6bd8d28.h708 (coins : Polynomial ℕ) (fallback : Str) (D : Family) (word : Str) :
    acceptProb (_root_.Integration9_9.LARCoinLayout.bodyFamily coins (_root_.Integration9_9.LARCoinLayout.bodyQueryBudget coins fallback) fallback D) word=
      acceptProb D (_root_.Integration9_9.LARCoinLayout.coinFirstPre coins fallback word) :=
  _Pjm coins (_root_.Integration9_9.LARCoinLayout.bodyQueryBudget coins fallback) fallback D word
    (_Pk6 coins fallback word)
open _root_.P2Mf6bd8d28 renaming h708 → _Pjo
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h706 → _Pjm
open _root_.P2Mf6bd8d28 renaming h708 → _Pjo
open _root_.P2Mf6bd8d28 renaming h735 → _Pkf
end
end
open _root_.P2Mf6bd8d28 renaming h505 → _Pe1
open _root_.P2Mf6bd8d28 renaming h706 → _Pjm
open _root_.P2Mf6bd8d28 renaming h708 → _Pjo
open _root_.P2Mf6bd8d28 renaming h735 → _Pkf
namespace InfoLossLAR.WorstCase.emittedOutput_get
end InfoLossLAR.WorstCase.emittedOutput_get
namespace Integration9_9.GenericBody
end Integration9_9.GenericBody
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open Integration9_9.GenericBody Integration9_9.LARCoinLayout
theorem _root_.P2Mf6bd8d28.h675 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (word : Str)
    (index : ℕ) (hi : index ≤ R.machine.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word
      ((_root_.Integration9_9.GenericBody.bodyFlagAddresses R.machine (unary word.length))[index]'(by
        simp only [_root_.Integration9_9.GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega))=
      decide ((R.query word).length=index) :=
  _Phe R.machine R.query R.encoding word index hi
open _root_.P2Mf6bd8d28 renaming h675 → _Pir
theorem _root_.P2Mf6bd8d28.h676 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (word : Str)
    (index : ℕ) (hi : index < R.machine.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word
      ((_root_.Integration9_9.GenericBody.bodyPayloadAddresses R.machine (unary word.length))[index]'(by
        simpa only [_Phh,unary,List.length_replicate] using hi))=
      ((R.query word)[index]?).getD false :=
  _Phk R.machine R.query R.encoding word index hi
open _root_.P2Mf6bd8d28 renaming h676 → _Pis
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h675 → _Pir
open _root_.P2Mf6bd8d28 renaming h676 → _Pis
end
end
open _root_.P2Mf6bd8d28 renaming h675 → _Pir
open _root_.P2Mf6bd8d28 renaming h676 → _Pis
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.GenericBody Integration9_9.LARCoinLayout
theorem _root_.P2Mf6bd8d28.h698 {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (tape word : Str) (ht : tape.length=coins.eval word.length) :
    (_root_.Integration9_9.GenericBodySemantics.specificationOfPre P coins).query (tape++word)=pre (encPair tape word) := by
  change pre (_root_.Integration9_9.LARCoinLayout.coinFirstPair coins (tape++word))=_
  rw [_Pkj coins tape word ht]
open _root_.P2Mf6bd8d28 renaming h698 → _Pje
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h698 → _Pje
end
end
open _root_.P2Mf6bd8d28 renaming h698 → _Pje
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open Integration9_9.GenericBody
theorem _root_.P2Mf6bd8d28.h666 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (index : ℕ) :
    _root_.InfoLossLAR.WorstCase.sourceValueAt (_root_.Integration9_9.GenericBody.bodySources R.machine D word.length)
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word) index=
      _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (R.query word) (List.range (R.machine.padding.eval word.length+1)) index := by
  unfold _root_.Integration9_9.GenericBody.bodySources
  rw [_Pbd]
  apply _Pbc
  intro length hl j hj
  have hlen : length ≤ R.machine.padding.eval word.length := by
    have := List.mem_range.mp hl
    omega
  have hjp : j < R.machine.padding.eval word.length := by omega
  have hjs : j < (_root_.Integration9_9.GenericBody.bodyPayloadAddresses R.machine (unary word.length)).length := by
    simpa only [_Phh,unary,List.length_replicate] using hjp
  rw [List.getElem?_eq_getElem hjs,Option.getD_some]
  exact _Pis R word j hjp
open _root_.P2Mf6bd8d28 renaming h666 → _Pii
theorem _root_.P2Mf6bd8d28.h679 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (index : ℕ) (hi : index < _root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length) :
    _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word index=
      _root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.generatedQueryBits (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word index :=
  _P6l _ _ _ _ hi
open _root_.P2Mf6bd8d28 renaming h679 → _Piv
theorem _root_.P2Mf6bd8d28.h677 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (index : ℕ) (hi : index < _root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length) :
    _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word
      (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+index)=
      _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (R.query word) (List.range (R.machine.padding.eval word.length+1)) index := by
  have his : index < (_root_.Integration9_9.GenericBody.bodySources R.machine D word.length).length := by
    simpa only [_root_.Integration9_9.GenericBody.bodySources_length] using hi
  unfold _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits _root_.Integration9_9.GenericBody.bodyPreWidth
  rw [_P6n (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word
    (_root_.Integration9_9.GenericBody.bodySources R.machine D word.length)
    (_Ph2 R.machine D word.length) index his]
  rw [←_Pfx _ _ index his,_Pii]
open _root_.P2Mf6bd8d28 renaming h677 → _Pit
theorem _root_.P2Mf6bd8d28.h678 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (index : ℕ)
    (hi : _root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length ≤ index) :
    _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word index=false := by
  unfold _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits
  rw [_P45]
  · exact _P8o word index (by unfold _root_.Integration9_9.GenericBody.bodyPreWidth at hi; omega)
  · rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.preparedLoadOps_length,_root_.Integration9_9.GenericBody.bodySources_length]
    unfold _root_.Integration9_9.GenericBody.bodyPreWidth at hi
    omega
open _root_.P2Mf6bd8d28 renaming h678 → _Piu
theorem _root_.P2Mf6bd8d28.h680 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.GenericBody.bodyPreparedGates R.machine D word.length)))
      (basisInput (a := _root_.Integration9_9.GenericBody.bodyAnc R.machine D word.length) (toBits word))=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word index.val) := by
  rw [_P9k,_P8p]
  unfold _root_.Integration9_9.GenericBody.bodyPreparedGates _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits _root_.InfoLossLAR.WorstCase.computationalBasis
  exact _P3y _ _ (_Phv R.machine D word.length)
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) (fun index hi _ => _P8o word index hi)
open _root_.P2Mf6bd8d28 renaming h680 → _Piw
theorem _root_.P2Mf6bd8d28.h684 {left right : ℕ} (h : left=right) (bits : Bits left) :
    _root_.Integration9_9.GenericBodySemantics.castBodyState h (_root_.InfoLossLAR.WorstCase.computationalBasis bits)=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => bits (Fin.cast h.symm index)) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h684 → _Pj0
theorem _root_.P2Mf6bd8d28.h697 {left right : ℕ} (h : left=right)
    (circuit : Layered left) (state : QState left) :
    runLayered (_root_.Integration9_9.GenericBody.castBodyCircuit h circuit) (_root_.Integration9_9.GenericBodySemantics.castBodyState h state)=
      _root_.Integration9_9.GenericBodySemantics.castBodyState h (runLayered circuit state) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h697 → _Pjd
theorem _root_.P2Mf6bd8d28.h682 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+
      _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))+
      (4*(R.machine.padding.eval word.length+1)+1)=_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length := by
  rw [_Pe5 D _ (R.query word) [],_root_.Integration9_9.GenericBody.bodyWidth_formula]
  rfl
open _root_.P2Mf6bd8d28 renaming h682 → _Piy
theorem _root_.P2Mf6bd8d28.h681 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    _root_.InfoLossLAR.WorstCase.computationalBasis (fun index : Fin (_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length) =>
      _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word index.val)=
      _root_.Integration9_9.GenericBodySemantics.castBodyState (_Piy R D word)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word))
            (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) := by
  rw [_Pe7,←_Pb5,←_Pb5,_Pj0]
  apply congrArg _root_.InfoLossLAR.WorstCase.computationalBasis
  have hwidth := _Pe5 D (R.machine.padding.eval word.length)
    (R.query word) []
  have hbits (index : Fin ((_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+
      _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))+
      (4*(R.machine.padding.eval word.length+1)+1))) :
      _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word index.val=
        (Fin.append (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word)
          (fun index => _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (R.query word)
            (List.range (R.machine.padding.eval word.length+1)) index.val)) (fun _ => false)) index := by
    refine Fin.addCases (fun block => ?_) (fun scratch => ?_) index
    · refine Fin.addCases (fun previous => ?_) (fun data => ?_) block
      · simp only [Fin.val_castAdd,Fin.append_left]
        rw [_Piv R D word previous.val previous.isLt]
        exact _root_.InfoLossLAR.WorstCase.selectorBitsExtension_get _ previous
      · simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left]
        dsimp only [_root_.Integration9_9.GenericBody.bodyPreWidth] at *
        rw [Fin.append_right]
        change _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word
          (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+data.val)=
          _root_.InfoLossLAR.WorstCase.bundleNaturalBits D (R.query word)
            (List.range (R.machine.padding.eval word.length+1)) data.val
        exact _Pit R D word data.val (by
          change data.val < _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) [])
          rw [←hwidth]
          exact data.isLt)
    · simp only [Fin.val_natAdd]
      dsimp only [_root_.Integration9_9.GenericBody.bodyPreWidth] at *
      rw [Fin.append_right]
      change _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word
        (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+
          _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word))+scratch.val)=false
      apply _Piu
      change _root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+
        _root_.InfoLossLAR.WorstCase.bundleWidth (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) []) ≤ _
      rw [←hwidth]
      omega
  funext index
  simpa only [Fin.val_cast] using hbits (Fin.cast (_Piy R D word).symm index)
open _root_.P2Mf6bd8d28 renaming h681 → _Pix
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h666 → _Pii
open _root_.P2Mf6bd8d28 renaming h677 → _Pit
open _root_.P2Mf6bd8d28 renaming h678 → _Piu
open _root_.P2Mf6bd8d28 renaming h679 → _Piv
open _root_.P2Mf6bd8d28 renaming h680 → _Piw
open _root_.P2Mf6bd8d28 renaming h681 → _Pix
open _root_.P2Mf6bd8d28 renaming h682 → _Piy
open _root_.P2Mf6bd8d28 renaming h684 → _Pj0
open _root_.P2Mf6bd8d28 renaming h697 → _Pjd
end
end
open _root_.P2Mf6bd8d28 renaming h666 → _Pii
open _root_.P2Mf6bd8d28 renaming h677 → _Pit
open _root_.P2Mf6bd8d28 renaming h678 → _Piu
open _root_.P2Mf6bd8d28 renaming h679 → _Piv
open _root_.P2Mf6bd8d28 renaming h680 → _Piw
open _root_.P2Mf6bd8d28 renaming h681 → _Pix
open _root_.P2Mf6bd8d28 renaming h682 → _Piy
open _root_.P2Mf6bd8d28 renaming h684 → _Pj0
open _root_.P2Mf6bd8d28 renaming h697 → _Pjd
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open Integration9_9.GenericBody
theorem _root_.P2Mf6bd8d28.h695 {left right total : ℕ} (first : Layered left) (second : Layered right)
    (h : (⟨left,first⟩ : Σ width : ℕ,Layered width)=⟨right,second⟩)
    (hf : left=total) (hs : right=total) :
    _root_.Integration9_9.GenericBody.castBodyCircuit hf first=_root_.Integration9_9.GenericBody.castBodyCircuit hs second := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h695 → _Pjb
theorem _root_.P2Mf6bd8d28.h665 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    _root_.Integration9_9.GenericBody.bodyDCircuit R.machine D word.length=
      _root_.Integration9_9.GenericBody.castBodyCircuit (_Piy R D word)
        (_root_.InfoLossLAR.WorstCase.leftCircuit (m := 4*(R.machine.padding.eval word.length+1)+1)
          (_root_.InfoLossLAR.WorstCase.rightCircuit (n := _root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length)
            (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word))))) := by
  have h := congrArg (fun circuit : (Σ width : ℕ,Layered width) =>
      (⟨(_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+circuit.1)+(4*(R.machine.padding.eval word.length+1)+1),
        _root_.InfoLossLAR.WorstCase.leftCircuit (m := 4*(R.machine.padding.eval word.length+1)+1)
          (_root_.InfoLossLAR.WorstCase.rightCircuit (n := _root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length) circuit.2)⟩ :
        Σ width : ℕ,Layered width))
    (_Pe2 D (R.machine.padding.eval word.length) [] (R.query word))
  unfold _root_.Integration9_9.GenericBody.bodyDCircuit
  exact _Pjb _ _ h _ _
open _root_.P2Mf6bd8d28 renaming h665 → _Pih
theorem _root_.P2Mf6bd8d28.h667 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    runLayered (_root_.Integration9_9.GenericBody.bodyDCircuit R.machine D word.length)
      (_root_.InfoLossLAR.WorstCase.computationalBasis (fun index : Fin (_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length) =>
        _root_.Integration9_9.GenericBodySemantics.bodyPreparedBits R D word index.val))=
      _root_.Integration9_9.GenericBodySemantics.castBodyState (_Piy R D word)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word))
            (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
              (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) := by
  rw [_Pix,_Pih,_Pjd,_Pcq,_Pfc]
open _root_.P2Mf6bd8d28 renaming h667 → _Pij
theorem _root_.P2Mf6bd8d28.h696 {width : ℕ} (first second : Layered width) (state : QState width) :
    runLayered (first++second) state=runLayered second (runLayered first state) := List.foldl_append
open _root_.P2Mf6bd8d28 renaming h696 → _Pjc
theorem _root_.P2Mf6bd8d28.h674 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.GenericBody.bodyPreparedGates R.machine D word.length))++
        _root_.Integration9_9.GenericBody.bodyDCircuit R.machine D word.length)
      (basisInput (a := _root_.Integration9_9.GenericBody.bodyAnc R.machine D word.length) (toBits word))=
      _root_.Integration9_9.GenericBodySemantics.castBodyState (_Piy R D word)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word))
            (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
              (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))) := by
  rw [_Pjc,_Piw,_Pij]
open _root_.P2Mf6bd8d28 renaming h674 → _Piq
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h665 → _Pih
open _root_.P2Mf6bd8d28 renaming h667 → _Pij
open _root_.P2Mf6bd8d28 renaming h674 → _Piq
open _root_.P2Mf6bd8d28 renaming h695 → _Pjb
open _root_.P2Mf6bd8d28 renaming h696 → _Pjc
end
end
open _root_.P2Mf6bd8d28 renaming h665 → _Pih
open _root_.P2Mf6bd8d28 renaming h667 → _Pij
open _root_.P2Mf6bd8d28 renaming h674 → _Piq
open _root_.P2Mf6bd8d28 renaming h695 → _Pjb
open _root_.P2Mf6bd8d28 renaming h696 → _Pjc
namespace Integration9_9.GenericBodySemantics
end Integration9_9.GenericBodySemantics
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open Integration9_9.GenericBody
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h686 {left first second right total : ℕ}
    (h : first=second) (hfirst : (left+first)+right=total)
    (hsecond : (left+second)+right=total)
    (prefixState : QState left) (middleState : QState first) (suffixState : QState right) :
    _root_.Integration9_9.GenericBodySemantics.castBodyState hfirst (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.tensorState prefixState middleState) suffixState)=
      _root_.Integration9_9.GenericBodySemantics.castBodyState hsecond (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.tensorState prefixState (_root_.Integration9_9.GenericBodySemantics.castBodyState h middleState)) suffixState) := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h686 → _Pj2
theorem _root_.P2Mf6bd8d28.h689 {start left total : ℕ} (choices : List (ℕ × ℕ))
    (hl : left < start) (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (h : start+(4*choices.length+1)=total) (state : QState start) :
    (∑ output : Bits total,if output
        ⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,by
          have := _root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
        (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
          (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; omega))))
        (_root_.Integration9_9.GenericBodySemantics.castBodyState h (_root_.InfoLossLAR.WorstCase.tensorState state (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false)))) output‖^2 else 0)=
      ∑ input : Bits start,if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
        (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  cases h
  exact _Pdc choices hl hc state
open _root_.P2Mf6bd8d28 renaming h689 → _Pj5
theorem _root_.P2Mf6bd8d28.h690 {start left total scratch : ℕ}
    (choices : List (ℕ × ℕ)) (hl : left < start)
    (hc : ∀ choice∈choices,choice.1 < start ∧ choice.2 < start)
    (hsize : scratch=4*choices.length+1) (h : start+scratch=total) (state : QState start) :
    (∑ output : Bits total,if output
        ⟨_root_.InfoLossLAR.WorstCase.multiSelectorOutput start left choices,by
          have := _root_.InfoLossLAR.WorstCase.multiSelectorOutput_lt start left choices hl; omega⟩ then
      ‖runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible
        (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start (_root_.InfoLossLAR.WorstCase.multiSelectorOps start left choices)
          (by rw [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length]; omega))))
        (_root_.Integration9_9.GenericBodySemantics.castBodyState h (_root_.InfoLossLAR.WorstCase.tensorState state (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false)))) output‖^2 else 0)=
      ∑ input : Bits start,if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input)
        (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input left) choices then ‖state input‖^2 else 0 := by
  subst scratch
  exact _Pj5 choices hl hc h state
open _root_.P2Mf6bd8d28 renaming h690 → _Pj6
theorem _root_.P2Mf6bd8d28.h673 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.GenericBody.bodyPreparedGates R.machine D word.length))++
        _root_.Integration9_9.GenericBody.bodyDCircuit R.machine D word.length)
      (basisInput (a := _root_.Integration9_9.GenericBody.bodyAnc R.machine D word.length) (toBits word))=
      _root_.Integration9_9.GenericBodySemantics.castBodyState (by rw [_root_.Integration9_9.GenericBody.bodyWidth_formula]; rfl)
        (_root_.InfoLossLAR.WorstCase.tensorState
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word))
            (_root_.Integration9_9.GenericBodySemantics.castBodyState (_Pe5 D _ (R.query word) [])
              (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
                (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word))))))
          (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ : Fin (4*(R.machine.padding.eval word.length+1)+1) => false))) := by
  rw [_Piq]
  exact _Pj2 (_Pe5 D _ (R.query word) [])
    _ _ _ _ _
open _root_.P2Mf6bd8d28 renaming h673 → _Pip
theorem _root_.P2Mf6bd8d28.h669 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) :
    acceptProb (_root_.Integration9_9.GenericBody.bodyFamily R.machine D) word=
      ∑ input : Bits (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length),
        if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input) (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input 0)
          (_root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length) then
          ‖_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word))
            (_root_.Integration9_9.GenericBodySemantics.castBodyState (_Pe5 D _ (R.query word) [])
              (runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word)))
                (_root_.InfoLossLAR.WorstCase.bundleState (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) (R.query word))))) input‖^2 else 0 := by
  change (∑ output : Bits (_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length),if output
    (_root_.Integration9_9.GenericBody.bodyOutput R.machine D word.length) then
    ‖runLayered (_root_.Integration9_9.GenericBody.bodyCircuit R.machine D word.length)
      (basisInput (a := _root_.Integration9_9.GenericBody.bodyAnc R.machine D word.length) (toBits word)) output‖^2 else 0)=_
  unfold _root_.Integration9_9.GenericBody.bodyCircuit
  rw [_Pjc,_Pip]
  apply _Pj6
  · unfold _root_.Integration9_9.GenericBody.bodyPreWidth
    omega
  · have h := _Pi2 R.machine D word.length
    rw [_Phm,_root_.Integration9_9.GenericBody.bodyDBundleSlots_length D _ []] at h
    exact h
  · rw [_root_.Integration9_9.GenericBody.bodyChoices_length]
open _root_.P2Mf6bd8d28 renaming h669 → _Pil
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h669 → _Pil
open _root_.P2Mf6bd8d28 renaming h673 → _Pip
open _root_.P2Mf6bd8d28 renaming h686 → _Pj2
open _root_.P2Mf6bd8d28 renaming h689 → _Pj5
open _root_.P2Mf6bd8d28 renaming h690 → _Pj6
end
end
open _root_.P2Mf6bd8d28 renaming h669 → _Pil
open _root_.P2Mf6bd8d28 renaming h673 → _Pip
open _root_.P2Mf6bd8d28 renaming h686 → _Pj2
open _root_.P2Mf6bd8d28 renaming h689 → _Pj5
open _root_.P2Mf6bd8d28 renaming h690 → _Pj6
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open Integration9_9.GenericBody
open QAlgorithms.Complexity Polynomial QMCNumericRuntime TM2PlatformSerialization
open scoped BigOperators
private theorem _root_.P2Mf6bd8d28.h880 {α : Type} {length : ℕ} (items : List α)
    (f : Fin length → α) (h : items=List.ofFn f) (index : ℕ)
    (hi : index < items.length) (hn : index < length) : items[index]=f ⟨index,hn⟩ := by
  subst items
  simp only [List.getElem_ofFn]
open _root_.P2Mf6bd8d28 renaming h880 → _Pog
theorem _root_.P2Mf6bd8d28.h664 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (n index : ℕ) (hi : index ≤ R.machine.padding.eval n) :
    (_root_.Integration9_9.GenericBody.bodyChoices R.machine D n)[index]'(by rw [_root_.Integration9_9.GenericBody.bodyChoices_length]; omega)=
      ((_root_.Integration9_9.GenericBody.bodyFlagAddresses R.machine (unary n))[index]'(by
        simp only [_root_.Integration9_9.GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega),
      _root_.Integration9_9.GenericBody.bodyPreWidth R.machine n+
        (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval n) [])
          ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val) := by
  have htoken (hit : index < (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (R.machine.padding.eval n))).length) :
      (_root_.InfoLossLAR.WorstCase.emitDOutputs (_root_.InfoLossLAR.WorstCase.describedQueryBlocks D (R.machine.padding.eval n)))[index]=
        encNat (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval n) [])
          ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩).val :=
    _Pog _ _ (_root_.InfoLossLAR.WorstCase.emitDOutputs_correct D (R.machine.padding.eval n) []) index hit _
  have hn (number : ℕ) : QMCNumericRuntime.inputWidth (encNat number)=number := by
    rw [←_root_.InfoLossLAR.WorstCase.unaryPayload_length,_root_.InfoLossLAR.WorstCase.unaryPayload_number]
    simp only [unary,List.length_replicate]
  unfold _root_.Integration9_9.GenericBody.bodyChoices _root_.Integration9_9.GenericBody.bodySelectorChoices
  simp only [List.getElem_zip,List.getElem_map,_Phm,htoken,hn]
  rfl
open _root_.P2Mf6bd8d28 renaming h664 → _Pig
theorem _root_.P2Mf6bd8d28.h662 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (data : Bits (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length)) (index : ℕ)
    (hi : index ≤ R.machine.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word) data)
      ((_root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length)[index]'(by rw [_root_.Integration9_9.GenericBody.bodyChoices_length]; omega)).1=
      decide ((R.query word).length=index) := by
  rw [_Pig R D word.length index hi]
  have hb := _Phd R.machine word.length
    ((_root_.Integration9_9.GenericBody.bodyFlagAddresses R.machine (unary word.length))[index]'(by
      simp only [_root_.Integration9_9.GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega))
    (List.getElem_mem (by simp only [_root_.Integration9_9.GenericBody.bodyFlagAddresses_length,unary,List.length_replicate]; omega))
  rw [_Pfk _ data _ hb]
  exact _Pir R word index hi
open _root_.P2Mf6bd8d28 renaming h662 → _Pie
theorem _root_.P2Mf6bd8d28.h663 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (data : Bits (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length)) (index : ℕ)
    (hi : index ≤ R.machine.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word) data)
      ((_root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length)[index]'(by rw [_root_.Integration9_9.GenericBody.bodyChoices_length]; omega)).2=
      data (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) [])
        ⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩) := by
  rw [_Pig R D word.length index hi]
  let output := _root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) [])
    (⟨index,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩ : Fin _)
  change _root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word) data)
    (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+output.val)=data output
  have heq : _root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+output.val=
      (Fin.natAdd (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length) output).val := rfl
  rw [heq,_root_.InfoLossLAR.WorstCase.selectorBitsExtension_get]
  dsimp only [_root_.Integration9_9.GenericBody.bodyPreWidth] at *
  rw [Fin.append_right]
open _root_.P2Mf6bd8d28 renaming h663 → _Pif
theorem _root_.P2Mf6bd8d28.h683 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (data : Bits (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length))
    (hq : (R.query word).length ≤ R.machine.padding.eval word.length) :
    _root_.InfoLossLAR.WorstCase.multiSelectorValue
      (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word) data))
      (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word) data) 0)
      (_root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length)=
      data (_root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) [])
        ⟨(R.query word).length,by simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩) := by
  apply _Pda
  · intro choice hc htrue
    obtain ⟨index,hi,he⟩ := List.getElem_of_mem hc
    have himax : index ≤ R.machine.padding.eval word.length := by rw [_root_.Integration9_9.GenericBody.bodyChoices_length] at hi; omega
    rw [←he,_Pie _ _ _ _ _ himax] at htrue
    have heq : (R.query word).length=index := of_decide_eq_true htrue
    rw [←he,_Pif _ _ _ _ _ himax]
    subst index
    rfl
  · refine ⟨(_root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length)[(R.query word).length]'(by
      rw [_root_.Integration9_9.GenericBody.bodyChoices_length]; omega),List.getElem_mem _,?_⟩
    rw [_Pie _ _ _ _ _ hq]
    simp
open _root_.P2Mf6bd8d28 renaming h683 → _Piz
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h662 → _Pie
open _root_.P2Mf6bd8d28 renaming h663 → _Pif
open _root_.P2Mf6bd8d28 renaming h664 → _Pig
open _root_.P2Mf6bd8d28 renaming h683 → _Piz
open _root_.P2Mf6bd8d28 renaming h880 → _Pog
end
end
open _root_.P2Mf6bd8d28 renaming h662 → _Pie
open _root_.P2Mf6bd8d28 renaming h663 → _Pif
open _root_.P2Mf6bd8d28 renaming h664 → _Pig
open _root_.P2Mf6bd8d28 renaming h683 → _Piz
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open Integration9_9.GenericBody
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h685 {left right : ℕ} (h : left=right)
    (state : QState left) (output : Fin left) :
    (∑ input : Bits right,if input (Fin.cast h output) then ‖_root_.Integration9_9.GenericBodySemantics.castBodyState h state input‖^2 else 0)=
      ∑ input : Bits left,if input output then ‖state input‖^2 else 0 := by
  cases h
  rfl
open _root_.P2Mf6bd8d28 renaming h685 → _Pj1
attribute [local irreducible] GenericBody.bodyQueryProgram
theorem _root_.P2Mf6bd8d28.h668 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (hq : (R.query word).length ≤ R.machine.padding.eval word.length) :
    acceptProb (_root_.Integration9_9.GenericBody.bodyFamily R.machine D) word=acceptProb D (R.query word) := by
  let P := _root_.Integration9_9.GenericBody.bodyQueryProgram R.machine
  let query := R.query word
  let blocks := _root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) query
  let changeWidth := _Pe5 D (R.machine.padding.eval word.length) query []
  let dstate := runLayered (_root_.InfoLossLAR.WorstCase.bundleCircuit blocks) (_root_.InfoLossLAR.WorstCase.bundleState blocks)
  let choices := _root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length
  let selected : Fin (_root_.InfoLossLAR.WorstCase.bundleWidth blocks) := _root_.InfoLossLAR.WorstCase.bundleOutput blocks
    ⟨query.length,by dsimp only [blocks,query]; simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩
  let physical : Fin (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length) := _root_.InfoLossLAR.WorstCase.bundleOutput (_root_.InfoLossLAR.WorstCase.queryBlocks D (R.machine.padding.eval word.length) [])
    ⟨query.length,by dsimp only [query]; simp only [_root_.InfoLossLAR.WorstCase.queryBlocks,List.length_ofFn]; omega⟩
  have hselected : physical=Fin.cast changeWidth selected := by
    apply Fin.ext
    exact _Pe1 D (R.machine.padding.eval word.length) [] query query.length hq
  calc
    acceptProb (_root_.Integration9_9.GenericBody.bodyFamily R.machine D) word=
        ∑ input : Bits (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length),
          if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input) (_root_.InfoLossLAR.WorstCase.selectorBitsExtension input 0) choices then
            ‖_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word)) (_root_.Integration9_9.GenericBodySemantics.castBodyState changeWidth dstate) input‖^2 else 0 :=
      _Pil R D word
    _=∑ input : Bits (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length),
        if _root_.InfoLossLAR.WorstCase.multiSelectorValue (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) input))
          (_root_.InfoLossLAR.WorstCase.selectorBitsExtension (Fin.append (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) input) 0) choices then
          ‖_root_.Integration9_9.GenericBodySemantics.castBodyState changeWidth dstate input‖^2 else 0 :=
      _P9l (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.result P word) (_root_.Integration9_9.GenericBodySemantics.castBodyState changeWidth dstate) _
    _=∑ input : Bits (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length),
        if input physical then ‖_root_.Integration9_9.GenericBodySemantics.castBodyState changeWidth dstate input‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro input _
      have he := _Piz R D word input hq
      exact congrArg (fun value : Bool => if value then ‖_root_.Integration9_9.GenericBodySemantics.castBodyState changeWidth dstate input‖^2 else 0) he
    _=∑ input : Bits (_root_.InfoLossLAR.WorstCase.bundleWidth blocks),if input selected then ‖dstate input‖^2 else 0 := by
      exact (congrArg (fun wire : Fin (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length) =>
        ∑ input : Bits (_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length),if input wire then
          ‖_root_.Integration9_9.GenericBodySemantics.castBodyState changeWidth dstate input‖^2 else 0) hselected).trans
        (_Pj1 changeWidth dstate selected)
    _=acceptProb D query := _Pe3 D (R.machine.padding.eval word.length) query hq
open _root_.P2Mf6bd8d28 renaming h668 → _Pik
theorem _root_.P2Mf6bd8d28.h670 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family) (word : Str) :
    acceptProb (_root_.Integration9_9.GenericBody.bodyFamily R.machine D) word=acceptProb D (R.query word) :=
  _Pik R D word (R.query_bound word)
open _root_.P2Mf6bd8d28 renaming h670 → _Pim
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h668 → _Pik
open _root_.P2Mf6bd8d28 renaming h670 → _Pim
open _root_.P2Mf6bd8d28 renaming h685 → _Pj1
end
end
open _root_.P2Mf6bd8d28 renaming h668 → _Pik
open _root_.P2Mf6bd8d28 renaming h670 → _Pim
open _root_.P2Mf6bd8d28 renaming h685 → _Pj1
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h138 {width : ℕ} (gate : _root_.InfoLossLAR.WorstCase.BooleanGate width)
    (state : Bits width) (wire : Fin width) (h : wire ≠ gate.target) :
    _root_.InfoLossLAR.WorstCase.reversibleAction gate.compile state wire=state wire := by
  cases gate with
  | constant target bit =>
    cases bit <;> simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile,_root_.InfoLossLAR.WorstCase.BooleanGate.target,_root_.InfoLossLAR.WorstCase.reversibleAction,
      _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv,_root_.InfoLossLAR.WorstCase.ReversibleGate.act,Function.update_of_ne]
  | copy source target distinct =>
    simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile,_root_.InfoLossLAR.WorstCase.BooleanGate.target,_root_.InfoLossLAR.WorstCase.reversibleAction,
      _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv,_root_.InfoLossLAR.WorstCase.ReversibleGate.act,Function.update_of_ne]
  | negate source target distinct =>
    simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile,_root_.InfoLossLAR.WorstCase.BooleanGate.target,_root_.InfoLossLAR.WorstCase.reversibleAction,
      _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv,_root_.InfoLossLAR.WorstCase.ReversibleGate.act,Function.update_of_ne]
  | xor first second target distinctFirst distinctSecond =>
    simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile,_root_.InfoLossLAR.WorstCase.BooleanGate.target,_root_.InfoLossLAR.WorstCase.reversibleAction,
      _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv,_root_.InfoLossLAR.WorstCase.ReversibleGate.act,Function.update_of_ne]
  | and first second target distinctFirst distinctSecond =>
    by_cases hs : first=second
    · simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile,_root_.InfoLossLAR.WorstCase.BooleanGate.target,_root_.InfoLossLAR.WorstCase.reversibleAction,
        _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv,_root_.InfoLossLAR.WorstCase.ReversibleGate.act,Function.update_of_ne]
    · simp_all [_root_.InfoLossLAR.WorstCase.BooleanGate.compile,_root_.InfoLossLAR.WorstCase.BooleanGate.target,_root_.InfoLossLAR.WorstCase.reversibleAction,
        _root_.InfoLossLAR.WorstCase.ReversibleGate.equiv,_root_.InfoLossLAR.WorstCase.ReversibleGate.act,Function.update_of_ne]
open _root_.P2Mf6bd8d28 renaming h138 → InfoLossLAR.WorstCase.BooleanGate.compile_preserves_wire
open _root_.P2Mf6bd8d28 renaming h138 → _P3u
theorem _root_.P2Mf6bd8d28.h351 {width : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate width))
    (state : Bits width) (wire : Fin width) (h : ∀ gate∈gates,wire ≠ gate.target) :
    _root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates) state wire=state wire := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    simp only [_root_.InfoLossLAR.WorstCase.booleanToReversible,List.flatMap_cons,_Pf9,Equiv.trans_apply]
    change (_root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible rest)) ((_root_.InfoLossLAR.WorstCase.reversibleAction gate.compile) state) wire=state wire
    rw [ih _ (fun other ho => h other (by simp [ho]))]
    exact gate.compile_preserves_wire state wire (h gate (by simp))
open _root_.P2Mf6bd8d28 renaming h351 → _P9r
theorem _root_.P2Mf6bd8d28.h349 {width : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate width))
    (state : Bits width) (wire : Fin width) (h : ∀ gate∈gates,wire ≠ gate.target) :
    (_root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)).symm state wire=state wire := by
  have hf := _P9r gates
    ((_root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)).symm state) wire h
  simpa only [Equiv.apply_symm_apply] using hf.symm
open _root_.P2Mf6bd8d28 renaming h349 → _P9p
theorem _root_.P2Mf6bd8d28.h548 {coins width : ℕ}
    (label : Bits width → Bits coins) (branches : Bits coins → QState width)
    (hsupport : ∀ coin input,branches coin input ≠ 0 → label input=coin)
    (event : Bits width → Bool) :
    (∑ input : Bits width,if event input then
      ‖(∑ coin : Bits coins,_root_.InfoLossLAR.WorstCase.coinAmplitude coins • branches coin) input‖^2 else 0)=
      avg (fun coin : Bits coins => ∑ input : Bits width,if event input then ‖branches coin input‖^2 else 0) := by
  classical
  have hzero (input : Bits width) (coin : Bits coins) (hne : coin ≠ label input) : branches coin input=0 := by
    by_contra hn
    exact hne (hsupport coin input hn).symm
  have hpoint (input : Bits width) :
      (if event input then ‖(∑ coin : Bits coins,_root_.InfoLossLAR.WorstCase.coinAmplitude coins • branches coin) input‖^2 else 0)=
        (Fintype.card (Bits coins) : ℝ)⁻¹*
          ∑ coin : Bits coins,if event input then ‖branches coin input‖^2 else 0 := by
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single (label input)]
    · rw [Finset.sum_eq_single (label input)]
      · cases event input <;> simp [norm_mul,mul_pow,_Pah]
      · intro coin _ hne
        simp [hzero input coin hne]
      · simp
    · intro coin _ hne
      rw [hzero input coin hne,mul_zero]
    · simp
  simp only [hpoint,←Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold avg
  ring
open _root_.P2Mf6bd8d28 renaming h548 → _Pf8
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h138 → InfoLossLAR.WorstCase.BooleanGate.compile_preserves_wire
open _root_.P2Mf6bd8d28 renaming h138 → _P3u
open _root_.P2Mf6bd8d28 renaming h349 → _P9p
open _root_.P2Mf6bd8d28 renaming h351 → _P9r
open _root_.P2Mf6bd8d28 renaming h548 → _Pf8
end
open _root_.P2Mf6bd8d28 renaming h138 → InfoLossLAR.WorstCase.BooleanGate.compile_preserves_wire
open _root_.P2Mf6bd8d28 renaming h138 → _P3u
open _root_.P2Mf6bd8d28 renaming h349 → _P9p
open _root_.P2Mf6bd8d28 renaming h351 → _P9r
open _root_.P2Mf6bd8d28 renaming h548 → _Pf8
namespace InfoLossLAR.WorstCase.BooleanGate
end InfoLossLAR.WorstCase.BooleanGate
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
open Integration9_9.GenericBody
theorem _root_.P2Mf6bd8d28.h687 {first middle last total : ℕ}
    (h : (first+middle)+last=total) (bits : Bits first)
    (middleState : QState middle) (lastState : QState last)
    (input : Bits total)
    (hn : _root_.Integration9_9.GenericBodySemantics.castBodyState h (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis bits) middleState) lastState) input ≠ 0)
    (index : Fin first) :
    input (Fin.cast h (Fin.castAdd last (Fin.castAdd middle index)))=bits index := by
  cases h
  have he : _root_.InfoLossLAR.WorstCase.leftRegister (_root_.InfoLossLAR.WorstCase.leftRegister input)=bits := by
    by_contra hne
    apply hn
    simp [_root_.Integration9_9.GenericBodySemantics.castBodyState,_root_.InfoLossLAR.WorstCase.tensorState,_root_.InfoLossLAR.WorstCase.computationalBasis,hne]
  exact congrFun he index
open _root_.P2Mf6bd8d28 renaming h687 → _Pj3
theorem _root_.P2Mf6bd8d28.h672 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (input : Bits (_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length))
    (hn : runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.GenericBody.bodyPreparedGates R.machine D word.length))++
        _root_.Integration9_9.GenericBody.bodyDCircuit R.machine D word.length)
      (basisInput (a := _root_.Integration9_9.GenericBody.bodyAnc R.machine D word.length) (toBits word)) input ≠ 0)
    (index : Fin word.length) :
    input ⟨index.val,by unfold _root_.Integration9_9.GenericBody.bodyWidth; omega⟩=toBits word index := by
  rw [_Pip] at hn
  let cell : Fin (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length) :=
    ⟨index.val,by unfold _root_.Integration9_9.GenericBody.bodyPreWidth; omega⟩
  have hp := _Pj3 _ _ _ _ input hn cell
  refine hp.trans ?_
  change _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.GenericBody.bodyQueryProgram R.machine) word.length).ops
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) index.val=toBits word index
  rw [_P47 _ _ _ _ index.isLt,_P8q word index.val index.isLt]
  rfl
open _root_.P2Mf6bd8d28 renaming h672 → _Pio
theorem _root_.P2Mf6bd8d28.h671 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family)
    (word : Str) (input : Bits (_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length))
    (hn : runLayered (_root_.Integration9_9.GenericBody.bodyCircuit R.machine D word.length)
      (basisInput (a := _root_.Integration9_9.GenericBody.bodyAnc R.machine D word.length) (toBits word)) input ≠ 0)
    (index : Fin word.length) :
    input ⟨index.val,by unfold _root_.Integration9_9.GenericBody.bodyWidth; omega⟩=toBits word index := by
  let gates := _root_.Integration9_9.GenericBody.bodySelectorGates R.machine D word.length
  let wire : Fin (_root_.Integration9_9.GenericBody.bodyWidth R.machine D word.length) := ⟨index.val,by unfold _root_.Integration9_9.GenericBody.bodyWidth; omega⟩
  have htarget : ∀ gate∈gates,wire ≠ gate.target := by
    intro gate hg he
    have hr := _P49
      (_root_.InfoLossLAR.WorstCase.multiSelectorOps (_root_.Integration9_9.GenericBody.bodyPreWidth R.machine word.length+_root_.Integration9_9.GenericBody.bodyDWidth R.machine D word.length)
        0 (_root_.Integration9_9.GenericBody.bodyChoices R.machine D word.length))
      (by simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] using _root_.Integration9_9.GenericBody.bodySelected_bound R.machine D word.length) gate hg
    have hv := congrArg Fin.val he
    dsimp only [wire] at hv
    unfold _root_.Integration9_9.GenericBody.bodyPreWidth at hr
    omega
  have hretain := _P9p gates input wire htarget
  unfold _root_.Integration9_9.GenericBody.bodyCircuit at hn
  rw [_Pjc,_Pat] at hn
  have hbefore := _Pio R D word
    ((_root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)).symm input) hn index
  exact hretain.symm.trans hbefore
open _root_.P2Mf6bd8d28 renaming h671 → _Pin
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h671 → _Pin
open _root_.P2Mf6bd8d28 renaming h672 → _Pio
open _root_.P2Mf6bd8d28 renaming h687 → _Pj3
end
end
open _root_.P2Mf6bd8d28 renaming h671 → _Pin
open _root_.P2Mf6bd8d28 renaming h672 → _Pio
open _root_.P2Mf6bd8d28 renaming h687 → _Pj3
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open QAlgorithms.Complexity Polynomial
theorem _root_.P2Mf6bd8d28.h737 {first middle last total : ℕ}
    (h : (first+middle)+last=total) (bits : Bits first)
    (middleState : QState middle) (lastState : QState last)
    (input : Bits total)
    (hn : _root_.Integration9_9.LARCoinLayout.castBodyState h (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis bits) middleState) lastState) input ≠ 0)
    (index : Fin first) :
    input (Fin.cast h (Fin.castAdd last (Fin.castAdd middle index)))=bits index := by
  cases h
  have he : _root_.InfoLossLAR.WorstCase.leftRegister (_root_.InfoLossLAR.WorstCase.leftRegister input)=bits := by
    by_contra hne
    apply hn
    simp [_root_.Integration9_9.LARCoinLayout.castBodyState,_root_.InfoLossLAR.WorstCase.tensorState,_root_.InfoLossLAR.WorstCase.computationalBasis,hne]
  exact congrFun he index
open _root_.P2Mf6bd8d28 renaming h737 → _Pkh
theorem _root_.P2Mf6bd8d28.h710 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (input : Bits (_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length))
    (hn : runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.LARCoinLayout.bodyPreparedGates coins padding fallback D word.length))++
        _root_.Integration9_9.LARCoinLayout.bodyDCircuit coins padding fallback D word.length)
      (basisInput (a := _root_.Integration9_9.LARCoinLayout.bodyAnc coins padding fallback D word.length) (toBits word)) input ≠ 0)
    (index : Fin word.length) :
    input ⟨index.val,by unfold _root_.Integration9_9.LARCoinLayout.bodyWidth; omega⟩=toBits word index := by
  rw [_Pjr] at hn
  let cell : Fin (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length) :=
    ⟨index.val,by unfold _root_.Integration9_9.LARCoinLayout.bodyPreWidth; omega⟩
  have hp := _Pkh _ _ _ _ input hn cell
  refine hp.trans ?_
  change _root_.InfoLossLAR.WorstCase.BooleanProgram.run word.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.compiled (_root_.Integration9_9.LARCoinLayout.bodyQueryProgram coins padding fallback) word.length).ops
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word) index.val=toBits word index
  rw [_P47 _ _ _ _ index.isLt,_P8q word index.val index.isLt]
  rfl
open _root_.P2Mf6bd8d28 renaming h710 → _Pjq
theorem _root_.P2Mf6bd8d28.h709 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family)
    (word : Str) (input : Bits (_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length))
    (hn : runLayered (_root_.Integration9_9.LARCoinLayout.bodyCircuit coins padding fallback D word.length)
      (basisInput (a := _root_.Integration9_9.LARCoinLayout.bodyAnc coins padding fallback D word.length) (toBits word)) input ≠ 0)
    (index : Fin word.length) :
    input ⟨index.val,by unfold _root_.Integration9_9.LARCoinLayout.bodyWidth; omega⟩=toBits word index := by
  let gates := _root_.Integration9_9.LARCoinLayout.bodySelectorGates coins padding fallback D word.length
  let wire : Fin (_root_.Integration9_9.LARCoinLayout.bodyWidth coins padding fallback D word.length) := ⟨index.val,by unfold _root_.Integration9_9.LARCoinLayout.bodyWidth; omega⟩
  have htarget : ∀ gate∈gates,wire ≠ gate.target := by
    intro gate hg he
    have hr := _P49
      (_root_.InfoLossLAR.WorstCase.multiSelectorOps (_root_.Integration9_9.LARCoinLayout.bodyPreWidth coins padding fallback word.length+_root_.Integration9_9.LARCoinLayout.bodyDWidth padding D word.length)
        0 (_root_.Integration9_9.LARCoinLayout.bodyChoices coins padding fallback D word.length))
      (by simpa only [_root_.InfoLossLAR.WorstCase.multiSelectorOps_length] using _root_.Integration9_9.LARCoinLayout.bodySelected_bound coins padding fallback D word.length) gate hg
    have hv := congrArg Fin.val he
    dsimp only [wire] at hv
    unfold _root_.Integration9_9.LARCoinLayout.bodyPreWidth at hr
    omega
  have hretain := _P9p gates input wire htarget
  unfold _root_.Integration9_9.LARCoinLayout.bodyCircuit at hn
  rw [_Pku,_Pat] at hn
  have hbefore := _Pjq coins padding fallback D word
    ((_root_.InfoLossLAR.WorstCase.reversibleAction (_root_.InfoLossLAR.WorstCase.booleanToReversible gates)).symm input) hn index
  exact hretain.symm.trans hbefore
open _root_.P2Mf6bd8d28 renaming h709 → _Pjp
end Integration9_9.LARCoinLayout
open _root_.P2Mf6bd8d28 renaming h709 → _Pjp
open _root_.P2Mf6bd8d28 renaming h710 → _Pjq
open _root_.P2Mf6bd8d28 renaming h737 → _Pkh
end
end
open _root_.P2Mf6bd8d28 renaming h709 → _Pjp
open _root_.P2Mf6bd8d28 renaming h710 → _Pjq
open _root_.P2Mf6bd8d28 renaming h737 → _Pkh
namespace Integration9_9.LARCoinLayout.castBodyState
end Integration9_9.LARCoinLayout.castBodyState
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout
open QAlgorithms.Complexity Polynomial
theorem _root_.P2Mf6bd8d28.h801 (coins : Polynomial ℕ) (F : Family) (hF : WellFormed F) :
    WellFormed (_root_.Integration9_9.RandomizedCircuit.family coins F) := by
  intro n layer hl
  simp only [_root_.Integration9_9.RandomizedCircuit.family,_root_.Integration9_9.RandomizedCircuit.circuit,List.mem_append] at hl
  rcases hl with (hc|hh)|hq
  · exact _Paw _ layer hc
  · exact _Pkd _ _ (_Pfd _
      (_Pcr _ (_Pam _))) layer hh
  · exact _Pkd _ _ (_Pfd _ (hF _)) layer hq
open _root_.P2Mf6bd8d28 renaming h801 → _Pm9
theorem _root_.P2Mf6bd8d28.h783 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    depth (_root_.Integration9_9.RandomizedCircuit.circuit coins F n) ≤ 74*(_root_.Integration9_9.RandomizedCircuit.workLength coins n)+coins.eval n+depth (F.circ (_root_.Integration9_9.RandomizedCircuit.workLength coins n)) := by
  unfold _root_.Integration9_9.RandomizedCircuit.circuit
  rw [show depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.RandomizedCircuit.copyGates coins F n))++
      _root_.Integration9_9.RandomizedCircuit.hadamardCircuit coins F n++_root_.Integration9_9.RandomizedCircuit.queryCircuit coins F n)=
    depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.RandomizedCircuit.copyGates coins F n)))+
      depth (_root_.Integration9_9.RandomizedCircuit.hadamardCircuit coins F n)+depth (_root_.Integration9_9.RandomizedCircuit.queryCircuit coins F n) by simp [depth,List.length_append,Nat.add_assoc]]
  have hcopy := _P3z (_root_.InfoLossLAR.WorstCase.registerLoadOps (_root_.Integration9_9.RandomizedCircuit.copySources coins n))
    (by rw [_root_.InfoLossLAR.WorstCase.registerLoadOps_length,_root_.Integration9_9.RandomizedCircuit.copySources_length]; unfold _root_.Integration9_9.RandomizedCircuit.workLength _root_.Integration9_9.RandomizedCircuit.width _root_.Integration9_9.RandomizedCircuit.ancillary; omega :
      n+(registerLoadOps (copySources coins n)).length ≤ width coins F n)
  change depth (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.RandomizedCircuit.copyGates coins F n))) ≤ _ at hcopy
  rw [_root_.InfoLossLAR.WorstCase.registerLoadOps_length,_root_.Integration9_9.RandomizedCircuit.copySources_length] at hcopy
  simp only [_root_.Integration9_9.RandomizedCircuit.hadamardCircuit,_root_.Integration9_9.RandomizedCircuit.queryCircuit,_Pkb,_root_.InfoLossLAR.WorstCase.leftCircuit_depth,_root_.InfoLossLAR.WorstCase.rightCircuit_depth,_root_.InfoLossLAR.WorstCase.coinCircuit_depth]
  omega
open _root_.P2Mf6bd8d28 renaming h783 → _Plr
theorem _root_.P2Mf6bd8d28.h799 (coins : Polynomial ℕ) (F : Family) (hF : PolyBounded F) :
    PolyBounded (_root_.Integration9_9.RandomizedCircuit.family coins F) := by
  obtain ⟨p,hp⟩ := hF
  refine ⟨C 75*(coins+X)+p.comp (coins+X),?_⟩
  constructor
  · intro n
    have hd := _Plr coins F n
    have hf := hp.1 (_root_.Integration9_9.RandomizedCircuit.workLength coins n)
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_comp]
    change depth (_root_.Integration9_9.RandomizedCircuit.circuit coins F n) ≤ 75*(coins.eval n+n)+p.eval (coins.eval n+n)
    unfold _root_.Integration9_9.RandomizedCircuit.workLength at hd hf
    omega
  · intro n
    have hf := hp.2 (_root_.Integration9_9.RandomizedCircuit.workLength coins n)
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_comp]
    change _root_.Integration9_9.RandomizedCircuit.ancillary coins F n ≤ 75*(coins.eval n+n)+p.eval (coins.eval n+n)
    unfold _root_.Integration9_9.RandomizedCircuit.ancillary _root_.Integration9_9.RandomizedCircuit.workLength at *
    omega
open _root_.P2Mf6bd8d28 renaming h799 → _Pm7
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h783 → _Plr
open _root_.P2Mf6bd8d28 renaming h799 → _Pm7
open _root_.P2Mf6bd8d28 renaming h801 → _Pm9
end
end
open _root_.P2Mf6bd8d28 renaming h783 → _Plr
open _root_.P2Mf6bd8d28 renaming h799 → _Pm7
open _root_.P2Mf6bd8d28 renaming h801 → _Pm9
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout
open QAlgorithms.Complexity Polynomial
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h812 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    n+(coins.eval n+(n+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins n)+1)))=_root_.Integration9_9.RandomizedCircuit.width coins F n := by
  unfold _root_.Integration9_9.RandomizedCircuit.width _root_.Integration9_9.RandomizedCircuit.ancillary
  omega
open _root_.P2Mf6bd8d28 renaming h812 → _Pmk
theorem _root_.P2Mf6bd8d28.h793 (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.RandomizedCircuit.copyGates coins F word.length)))
      (basisInput (a := _root_.Integration9_9.RandomizedCircuit.ancillary coins F word.length) (toBits word))=
      _root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.InfoLossLAR.WorstCase.inputCopyResult word (coins.eval word.length) index.val) :=
  _Pc3 word (coins.eval word.length) (F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length))
open _root_.P2Mf6bd8d28 renaming h793 → _Pm1
theorem _root_.P2Mf6bd8d28.h794 (coins : Polynomial ℕ) (F : Family) (word : Str) :
    _root_.InfoLossLAR.WorstCase.computationalBasis (fun index : Fin (_root_.Integration9_9.RandomizedCircuit.width coins F word.length) =>
      _root_.InfoLossLAR.WorstCase.inputCopyResult word (coins.eval word.length) index.val)=
      _root_.Integration9_9.LARCoinLayout.castBodyState (_Pmk coins F word.length)
        (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word))
          (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.coinZero (coins.eval word.length))
            (basisInput (a := F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) (toBits word)))) := by
  change _=_root_.Integration9_9.LARCoinLayout.castBodyState _ (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word))
    (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (fun _ => false))
      (basisInput (a := F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) (toBits word))))
  rw [_P9k,_P8p,
    ←_Pb5,←_Pb5,_Pke]
  apply congrArg _root_.InfoLossLAR.WorstCase.computationalBasis
  have hp (index : Fin (word.length+(coins.eval word.length+
      (word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1))))) :
      _root_.InfoLossLAR.WorstCase.inputCopyResult word (coins.eval word.length) index.val=
        Fin.append (toBits word) (Fin.append (fun _ => false) (fun i => _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word i.val)) index := by
    refine Fin.addCases (fun original => ?_) (fun work => ?_) index
    · simp only [Fin.val_castAdd,Fin.append_left,_root_.InfoLossLAR.WorstCase.inputCopyResult,if_pos original.isLt]
      rw [_P8q word original.val original.isLt]
      rfl
    · refine Fin.addCases (fun coin => ?_) (fun body => ?_) work
      · simp (disch := omega) only [Fin.val_natAdd,Fin.val_castAdd,Fin.append_right,Fin.append_left,
          _root_.InfoLossLAR.WorstCase.inputCopyResult,if_neg,if_pos]
      · simp only [Fin.val_natAdd,Fin.append_right]
        by_cases hi : body.val < word.length
        · simp (disch := omega) only [_root_.InfoLossLAR.WorstCase.inputCopyResult,if_neg,if_pos]
          congr 1
          omega
        · rw [_P8o word body.val (by omega)]
          simp (disch := omega) only [_root_.InfoLossLAR.WorstCase.inputCopyResult,if_neg]
  funext index
  simpa only [Fin.val_cast] using hp (Fin.cast (_Pmk coins F word.length).symm index)
open _root_.P2Mf6bd8d28 renaming h794 → _Pm2
theorem _root_.P2Mf6bd8d28.h804 (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered
      (_root_.InfoLossLAR.WorstCase.compileReversible (_root_.InfoLossLAR.WorstCase.booleanToReversible (_root_.Integration9_9.RandomizedCircuit.copyGates coins F word.length))++_root_.Integration9_9.RandomizedCircuit.hadamardCircuit coins F word.length)
      (basisInput (a := _root_.Integration9_9.RandomizedCircuit.ancillary coins F word.length) (toBits word))=
      _root_.Integration9_9.LARCoinLayout.castBodyState (_Pmk coins F word.length)
        (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word))
          (_root_.InfoLossLAR.WorstCase.tensorState (fun _ => _root_.InfoLossLAR.WorstCase.coinAmplitude (coins.eval word.length))
            (basisInput (a := F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) (toBits word)))) := by
  rw [_Pku,_Pm1,_Pm2]
  unfold _root_.Integration9_9.RandomizedCircuit.hadamardCircuit
  rw [_Pkv,_Pfc,_Pcq,_Pal]
open _root_.P2Mf6bd8d28 renaming h804 → _Pmc
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h793 → _Pm1
open _root_.P2Mf6bd8d28 renaming h794 → _Pm2
open _root_.P2Mf6bd8d28 renaming h804 → _Pmc
open _root_.P2Mf6bd8d28 renaming h812 → _Pmk
end
end
open _root_.P2Mf6bd8d28 renaming h793 → _Pm1
open _root_.P2Mf6bd8d28 renaming h794 → _Pm2
open _root_.P2Mf6bd8d28 renaming h804 → _Pmc
open _root_.P2Mf6bd8d28 renaming h812 → _Pmk
namespace Integration9_9.RandomizedCircuit
end Integration9_9.RandomizedCircuit
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout
open QAlgorithms.Complexity Polynomial
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h815 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    n+(_root_.Integration9_9.RandomizedCircuit.workLength coins n+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins n)+1))=_root_.Integration9_9.RandomizedCircuit.width coins F n := by
  unfold _root_.Integration9_9.RandomizedCircuit.width _root_.Integration9_9.RandomizedCircuit.ancillary _root_.Integration9_9.RandomizedCircuit.workLength
  omega
open _root_.P2Mf6bd8d28 renaming h815 → _Pmn
theorem _root_.P2Mf6bd8d28.h781 {left right : ℕ} {α : Type} [Fintype α] (h : left=right)
    (states : α → QState left) :
    _root_.Integration9_9.LARCoinLayout.castBodyState h (∑ index,states index)=∑ index,_root_.Integration9_9.LARCoinLayout.castBodyState h (states index) := by cases h; rfl
open _root_.P2Mf6bd8d28 renaming h781 → _Plp
theorem _root_.P2Mf6bd8d28.h780 {left right : ℕ} (h : left=right) (scalar : ℂ) (state : QState left) :
    _root_.Integration9_9.LARCoinLayout.castBodyState h (scalar • state)=scalar • _root_.Integration9_9.LARCoinLayout.castBodyState h state := by cases h; rfl
open _root_.P2Mf6bd8d28 renaming h780 → _Plo
theorem _root_.P2Mf6bd8d28.h782 {prefixSize left right total : ℕ}
    (h : left=right) (hl : prefixSize+left=total) (hr : prefixSize+right=total)
    (prefixState : QState prefixSize) (state : QState left) :
    _root_.Integration9_9.LARCoinLayout.castBodyState hl (_root_.InfoLossLAR.WorstCase.tensorState prefixState state)=
      _root_.Integration9_9.LARCoinLayout.castBodyState hr (_root_.InfoLossLAR.WorstCase.tensorState prefixState (_root_.Integration9_9.LARCoinLayout.castBodyState h state)) := by cases h; rfl
open _root_.P2Mf6bd8d28 renaming h782 → _Plq
theorem _root_.P2Mf6bd8d28.h785 (coins : Polynomial ℕ) (F : Family) (word : Str) :
    _root_.Integration9_9.RandomizedCircuit.coherentInput coins F word=
      ∑ coin : Bits (coins.eval word.length),_root_.InfoLossLAR.WorstCase.coinAmplitude (coins.eval word.length) • _root_.Integration9_9.RandomizedCircuit.branchInput coins F word coin := by
  unfold _root_.Integration9_9.RandomizedCircuit.coherentInput _root_.Integration9_9.RandomizedCircuit.branchInput
  rw [_P9k]
  change _root_.Integration9_9.LARCoinLayout.castBodyState _ (_root_.InfoLossLAR.WorstCase.coinBranchState
    (fun _ => _root_.InfoLossLAR.WorstCase.computationalBasis (Fin.append (toBits word) (fun _ => false))))=_
  rw [_Pai,_Plp]
  apply Finset.sum_congr rfl
  intro coin _
  exact _Plo _ _ _
open _root_.P2Mf6bd8d28 renaming h785 → _Plt
theorem _root_.P2Mf6bd8d28.h786 (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered (F.circ (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) (_root_.Integration9_9.RandomizedCircuit.coherentInput coins F word)=
      ∑ coin : Bits (coins.eval word.length),_root_.InfoLossLAR.WorstCase.coinAmplitude (coins.eval word.length) • _root_.Integration9_9.RandomizedCircuit.branchOutput coins F word coin := by
  rw [_Plt,←_root_.InfoLossLAR.WorstCase.runLayeredLinearMap_apply,map_sum]
  simp only [map_smul,_root_.InfoLossLAR.WorstCase.runLayeredLinearMap_apply,_root_.Integration9_9.RandomizedCircuit.branchOutput]
open _root_.P2Mf6bd8d28 renaming h786 → _Plu
theorem _root_.P2Mf6bd8d28.h784 (coins : Polynomial ℕ) (F : Family) (word : Str) :
    runLayered (_root_.Integration9_9.RandomizedCircuit.circuit coins F word.length)
      (basisInput (a := _root_.Integration9_9.RandomizedCircuit.ancillary coins F word.length) (toBits word))=
      _root_.Integration9_9.LARCoinLayout.castBodyState (_Pmn coins F word.length)
        (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word))
          (∑ coin : Bits (coins.eval word.length),
            _root_.InfoLossLAR.WorstCase.coinAmplitude (coins.eval word.length) • _root_.Integration9_9.RandomizedCircuit.branchOutput coins F word coin)) := by
  unfold _root_.Integration9_9.RandomizedCircuit.circuit
  rw [_Pku,_Pmc]
  have ht := _Plq (_root_.Integration9_9.RandomizedCircuit.work_width coins F word.length)
    (_Pmk coins F word.length) (_Pmn coins F word.length)
    (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word))
    (_root_.InfoLossLAR.WorstCase.tensorState (fun _ => _root_.InfoLossLAR.WorstCase.coinAmplitude (coins.eval word.length))
      (basisInput (a := F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) (toBits word)))
  rw [ht]
  unfold _root_.Integration9_9.RandomizedCircuit.queryCircuit
  rw [_Pkv,_Pfc]
  exact congrArg (fun state => _root_.Integration9_9.LARCoinLayout.castBodyState (_Pmn coins F word.length)
    (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word)) state)) (_Plu coins F word)
open _root_.P2Mf6bd8d28 renaming h784 → _Pls
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h780 → _Plo
open _root_.P2Mf6bd8d28 renaming h781 → _Plp
open _root_.P2Mf6bd8d28 renaming h782 → _Plq
open _root_.P2Mf6bd8d28 renaming h784 → _Pls
open _root_.P2Mf6bd8d28 renaming h785 → _Plt
open _root_.P2Mf6bd8d28 renaming h786 → _Plu
open _root_.P2Mf6bd8d28 renaming h815 → _Pmn
end
end
open _root_.P2Mf6bd8d28 renaming h780 → _Plo
open _root_.P2Mf6bd8d28 renaming h781 → _Plp
open _root_.P2Mf6bd8d28 renaming h782 → _Plq
open _root_.P2Mf6bd8d28 renaming h784 → _Pls
open _root_.P2Mf6bd8d28 renaming h785 → _Plt
open _root_.P2Mf6bd8d28 renaming h786 → _Plu
open _root_.P2Mf6bd8d28 renaming h815 → _Pmn
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout
open QAlgorithms.Complexity Polynomial
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h772 (coins padding : Polynomial ℕ) (fallback : Str) (D : Family) :
    _root_.Integration9_9.RandomizedCircuit.PreservesClassicalInput (_root_.Integration9_9.LARCoinLayout.bodyFamily coins padding fallback D) := by
  intro word output hn index
  exact _Pjp coins padding fallback D word output hn index
open _root_.P2Mf6bd8d28 renaming h772 → _Plg
theorem _root_.P2Mf6bd8d28.h777 (coins : Polynomial ℕ) (F : Family) (word : Str)
    (coin : Bits (coins.eval word.length)) :
    _root_.Integration9_9.RandomizedCircuit.branchInput coins F word coin=_root_.InfoLossLAR.WorstCase.computationalBasis
      (fun index => _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension (List.ofFn coin++word) index.val) := by
  unfold _root_.Integration9_9.RandomizedCircuit.branchInput
  rw [_Pke]
  apply congrArg _root_.InfoLossLAR.WorstCase.computationalBasis
  have hp (index : Fin (coins.eval word.length+(word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1)))) :
      Fin.append coin (Fin.append (toBits word) (fun _ => false)) index=
        _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension (List.ofFn coin++word) index.val := by
    rw [_P8p]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,Fin.val_castAdd,_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension]
      rw [List.getElem?_append_left (by simp only [List.length_ofFn]; exact i.isLt)]
      simp only [List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]
    · simp only [Fin.append_right,Fin.val_natAdd,_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension]
      rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  funext index
  simpa only [Fin.val_cast] using hp (Fin.cast (_root_.Integration9_9.RandomizedCircuit.work_width coins F word.length).symm index)
open _root_.P2Mf6bd8d28 renaming h777 → _Pll
theorem _root_.P2Mf6bd8d28.h771 (F : Family) (word : Str) (length : ℕ) (hlen : word.length=length) :
    (∑ input : Bits (length+(F.anc length+1)),if input (F.out length) then
      ‖runLayered (F.circ length) (_root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word index.val)) input‖^2 else 0)=
      acceptProb F word := by
  subst length
  unfold acceptProb
  rw [_P9k,_P8p]
open _root_.P2Mf6bd8d28 renaming h771 → _Plf
theorem _root_.P2Mf6bd8d28.h779 (coins : Polynomial ℕ) (F : Family) (word : Str)
    (coin : Bits (coins.eval word.length)) :
    (∑ input : Bits (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1)),
      if input (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) then ‖_root_.Integration9_9.RandomizedCircuit.branchOutput coins F word coin input‖^2 else 0)=
      acceptProb F (List.ofFn coin++word) := by
  unfold _root_.Integration9_9.RandomizedCircuit.branchOutput
  rw [_Pll]
  exact _Plf F (List.ofFn coin++word) (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)
    (by simp only [List.length_append,List.length_ofFn,_root_.Integration9_9.RandomizedCircuit.workLength])
open _root_.P2Mf6bd8d28 renaming h779 → _Pln
theorem _root_.P2Mf6bd8d28.h806 (F : Family) (hF : _root_.Integration9_9.RandomizedCircuit.PreservesClassicalInput F)
    (word : Str) (length : ℕ) (hlen : word.length=length)
    (output : Bits (length+(F.anc length+1)))
    (hn : runLayered (F.circ length) (_root_.InfoLossLAR.WorstCase.computationalBasis (fun index => _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word index.val)) output ≠ 0)
    (index : ℕ) (hi : index < word.length) :
    output ⟨index,by omega⟩=_root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension word index := by
  subst length
  have h := hF word output
  rw [_P9k,_P8p] at h
  have hv := h hn ⟨index,hi⟩
  rw [_P8q word index hi]
  exact hv
open _root_.P2Mf6bd8d28 renaming h806 → _Pme
theorem _root_.P2Mf6bd8d28.h778 (coins : Polynomial ℕ) (F : Family) (hF : _root_.Integration9_9.RandomizedCircuit.PreservesClassicalInput F)
    (word : Str) (coin : Bits (coins.eval word.length))
    (output : Bits (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1)))
    (hn : _root_.Integration9_9.RandomizedCircuit.branchOutput coins F word coin output ≠ 0) :
    _root_.Integration9_9.RandomizedCircuit.coinLabel coins F word.length output=coin := by
  unfold _root_.Integration9_9.RandomizedCircuit.branchOutput at hn
  rw [_Pll] at hn
  funext index
  have hs := _Pme F hF (List.ofFn coin++word) (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)
    (by simp only [List.length_append,List.length_ofFn,_root_.Integration9_9.RandomizedCircuit.workLength]) output hn index.val
    (by simp only [List.length_append,List.length_ofFn]; omega)
  change output ⟨index.val,_⟩=coin index
  refine hs.trans ?_
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.wordExtension
  rw [List.getElem?_append_left (by simp only [List.length_ofFn]; exact index.isLt)]
  simp only [List.getElem?_ofFn,dif_pos index.isLt,Option.getD_some]
open _root_.P2Mf6bd8d28 renaming h778 → _Plm
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h771 → _Plf
open _root_.P2Mf6bd8d28 renaming h772 → _Plg
open _root_.P2Mf6bd8d28 renaming h777 → _Pll
open _root_.P2Mf6bd8d28 renaming h778 → _Plm
open _root_.P2Mf6bd8d28 renaming h779 → _Pln
open _root_.P2Mf6bd8d28 renaming h806 → _Pme
end
end
open _root_.P2Mf6bd8d28 renaming h771 → _Plf
open _root_.P2Mf6bd8d28 renaming h772 → _Plg
open _root_.P2Mf6bd8d28 renaming h777 → _Pll
open _root_.P2Mf6bd8d28 renaming h778 → _Plm
open _root_.P2Mf6bd8d28 renaming h779 → _Pln
open _root_.P2Mf6bd8d28 renaming h806 → _Pme
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9 Integration9_9.TM2StockLists
theorem _root_.P2Mf6bd8d28.h584 (F : Family) (hF : Uniform F)
    (request : Str → Str) (hrequest : Poly request) (size : ℕ → ℕ)
    (hsize : ∀ word,request word=unary (size word.length))
    (builder : Str × Str → Str) (hbuilder : Poly builder) :
    PolyTimeComputable (fun word : Str => builder (word,encFamilyAt F (size word.length))) := by
  obtain ⟨source,⟨sourceProgram⟩,hsource⟩ := hF
  let requestProgram := _root_.Integration9_9.LARCoinLayout.rawPolyProgram (f := request) hrequest
  obtain ⟨called⟩ := _root_.Integration9_9.TM2Composition.comp requestProgram.stock sourceProgram
  obtain ⟨quoted⟩ := _root_.InfoLossLAR.WorstCase.stock_quoted called
  obtain ⟨paired⟩ := _root_.InfoLossLAR.WorstCase.stock_pairWithInput quoted
  obtain ⟨encoded⟩ := _root_.Integration9_9.TM2Composition.comp BooleanLists.packProgram.stock paired
  obtain ⟨built⟩ := _root_.Integration9_9.TM2Composition.comp encoded hbuilder.program.stock
  obtain ⟨whole⟩ := _root_.Integration9_9.TM2Composition.comp built BooleanLists.unpackProgram.stock
  refine ⟨_root_.Integration9_9.TM2StockLists.congrProgram whole _ ?_⟩
  intro word
  simp only [Function.comp_apply,id_eq]
  rw [hsize,hsource]
open _root_.P2Mf6bd8d28 renaming h584 → _Pg8
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h584 → _Pg8
end
open _root_.P2Mf6bd8d28 renaming h584 → _Pg8
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime TM2PlatformSerialization
@[fun_prop] theorem _root_.P2Mf6bd8d28.h776 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.ancillarySlots coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.ancillarySlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h776 → _Plk
theorem _root_.P2Mf6bd8d28.h775 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    (_root_.Integration9_9.RandomizedCircuit.ancillarySlots coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))).length=_root_.Integration9_9.RandomizedCircuit.ancillary coins F n := by
  unfold _root_.Integration9_9.RandomizedCircuit.ancillarySlots encFamilyAt
  simp only [List.append_assoc,_root_.InfoLossLAR.WorstCase.unaryPayload_encNat,List.length_append,List.length_map,
    _root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate]
  unfold _root_.Integration9_9.RandomizedCircuit.ancillary
  omega
open _root_.P2Mf6bd8d28 renaming h775 → _Plj
@[fun_prop] theorem _root_.P2Mf6bd8d28.h774 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.allSlots coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.allSlots
  fun_prop
open _root_.P2Mf6bd8d28 renaming h774 → _Pli
theorem _root_.P2Mf6bd8d28.h773 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    (_root_.Integration9_9.RandomizedCircuit.allSlots coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))).length=_root_.Integration9_9.RandomizedCircuit.width coins F n := by
  simp only [_root_.Integration9_9.RandomizedCircuit.allSlots,List.length_append,List.length_map,List.length_singleton]
  rw [_Plj]
  simp only [unary,List.length_replicate,_root_.Integration9_9.RandomizedCircuit.width]
  omega
open _root_.P2Mf6bd8d28 renaming h773 → _Plh
@[fun_prop] theorem _root_.P2Mf6bd8d28.h792 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.copyWords coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.copyWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h792 → _Pm0
theorem _root_.P2Mf6bd8d28.h791 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.copyWords coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))=
      (_root_.Integration9_9.RandomizedCircuit.copyGates coins F n).map _root_.InfoLossLAR.WorstCase.BooleanGate.code := by
  unfold _root_.Integration9_9.RandomizedCircuit.copyWords
  have hn : n+(coins.eval n+n) ≤ _root_.Integration9_9.RandomizedCircuit.width coins F n := by unfold _root_.Integration9_9.RandomizedCircuit.width _root_.Integration9_9.RandomizedCircuit.ancillary; omega
  have h := _Pbz
    (_root_.Integration9_9.RandomizedCircuit.allSlots coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n)))
    (_root_.Integration9_9.LARCoinLayout.queryWireSlots coins (unary n)) ((unary n).map (fun _ => ()))
    (by simpa only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate,List.length_map] using hn :
      ((unary n).map (fun _ => ())).length+
        ((queryWireSlots coins (unary n)).length+((unary n).map (fun _ => ())).length) ≤ width coins F n)
    (by rw [_Plh]; simpa only [_root_.Integration9_9.LARCoinLayout.queryWireSlots_length,unary,List.length_replicate,List.length_map] using hn)
  convert h using 1
  simp only [_root_.Integration9_9.LARCoinLayout.queryWireSlots,unary,List.length_replicate,List.map_replicate,_root_.Integration9_9.RandomizedCircuit.copyGates,_root_.Integration9_9.RandomizedCircuit.copySources]
open _root_.P2Mf6bd8d28 renaming h791 → _Plz
@[fun_prop] theorem _root_.P2Mf6bd8d28.h788 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.copyDescription coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.copyDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h788 → _Plw
theorem _root_.P2Mf6bd8d28.h787 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.copyDescription coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))=(_root_.Integration9_9.RandomizedCircuit.copyBooleanFamily coins F).code n := by
  unfold _root_.Integration9_9.RandomizedCircuit.copyDescription
  rw [_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,_Plj,_Plz,_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq]
  rfl
open _root_.P2Mf6bd8d28 renaming h787 → _Plv
@[fun_prop] theorem _root_.P2Mf6bd8d28.h790 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.copyQuantumDescription coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.copyQuantumDescription
  fun_prop
open _root_.P2Mf6bd8d28 renaming h790 → _Ply
theorem _root_.P2Mf6bd8d28.h789 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.copyQuantumDescription coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))=
      encFamilyAt (_root_.Integration9_9.RandomizedCircuit.copyBooleanFamily coins F).reversible.compile n := by
  unfold _root_.Integration9_9.RandomizedCircuit.copyQuantumDescription
  rw [_Plv,_Pap,_Par]
open _root_.P2Mf6bd8d28 renaming h789 → _Plx
@[fun_prop] theorem _root_.P2Mf6bd8d28.h803 (coins : Polynomial ℕ) : Poly (_root_.Integration9_9.RandomizedCircuit.hadamardWords coins) := by
  unfold _root_.Integration9_9.RandomizedCircuit.hadamardWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h803 → _Pmb
private theorem _root_.P2Mf6bd8d28.h896 {left middle right : ℕ} (c : Layered middle) :
    (_root_.InfoLossLAR.WorstCase.rightCircuit (n := left) (_root_.InfoLossLAR.WorstCase.leftCircuit (m := right) c)).map (List.map encInstr)=
      (_root_.InfoLossLAR.WorstCase.rightCircuit (n := left) c).map (List.map encInstr) := by
  have he (gate : Instr middle) :
      encInstr (_root_.InfoLossLAR.WorstCase.rightInstruction (n := left) (_root_.InfoLossLAR.WorstCase.leftInstruction (m := right) gate))=
        encInstr (_root_.InfoLossLAR.WorstCase.rightInstruction (n := left) gate) := by cases gate <;> rfl
  simp only [_root_.InfoLossLAR.WorstCase.leftCircuit,_root_.InfoLossLAR.WorstCase.rightCircuit,List.map_map,Function.comp_def,he]
open _root_.P2Mf6bd8d28 renaming h896 → _Pow
theorem _root_.P2Mf6bd8d28.h802 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.hadamardWords coins (unary n)=(_root_.Integration9_9.RandomizedCircuit.hadamardCircuit coins F n).map (List.map encInstr) := by
  unfold _root_.Integration9_9.RandomizedCircuit.hadamardWords
  rw [_Paj]
  have hlen : ((_root_.Integration9_9.LARCoinLayout.queryWireSlots coins (unary n)).map (fun _ => true)).length=coins.eval n := by
    rw [List.length_map,_root_.Integration9_9.LARCoinLayout.queryWireSlots_length]
    simp only [unary,List.length_replicate]
  rw [hlen]
  have hr := _root_.InfoLossLAR.WorstCase.readCircuitLayers_append (_root_.InfoLossLAR.WorstCase.coinCircuit (coins.eval n)) []
  simp only [List.append_nil] at hr
  rw [hr]
  simp only
  rw [_Pfm]
  unfold _root_.Integration9_9.RandomizedCircuit.hadamardCircuit
  rw [_Pkc,_Pow]
  apply _Pfb
  simp [unary]
open _root_.P2Mf6bd8d28 renaming h802 → _Pma
@[fun_prop] theorem _root_.P2Mf6bd8d28.h814 : Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.queryWords x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.queryWords
  fun_prop
open _root_.P2Mf6bd8d28 renaming h814 → _Pmm
theorem _root_.P2Mf6bd8d28.h813 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.queryWords (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))=(_root_.Integration9_9.RandomizedCircuit.queryCircuit coins F n).map (List.map encInstr) := by
  unfold _root_.Integration9_9.RandomizedCircuit.queryWords
  rw [_Pel,_Pfm]
  unfold _root_.Integration9_9.RandomizedCircuit.queryCircuit
  rw [_Pkc]
  apply _Pfb
  simp [unary]
open _root_.P2Mf6bd8d28 renaming h813 → _Pml
@[fun_prop] theorem _root_.P2Mf6bd8d28.h808 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.outputWord coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.outputWord
  fun_prop
open _root_.P2Mf6bd8d28 renaming h808 → _Pmg
theorem _root_.P2Mf6bd8d28.h807 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.outputWord coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))=encNat (_root_.Integration9_9.RandomizedCircuit.output coins F n).val := by
  unfold _root_.Integration9_9.RandomizedCircuit.outputWord
  rw [_Pkt]
  change _root_.InfoLossLAR.WorstCase.shiftWireWord (unary n) (_root_.InfoLossLAR.WorstCase.readFamilyFrame (unary (_root_.Integration9_9.RandomizedCircuit.workLength coins n),_)).2.1=_
  rw [_root_.InfoLossLAR.WorstCase.readFamilyFrame_correct,_root_.InfoLossLAR.WorstCase.shiftWireWord_spec]
  rw [←_root_.InfoLossLAR.WorstCase.unaryPayload_length,_root_.InfoLossLAR.WorstCase.unaryPayload_number]
  simp only [unary,List.length_replicate,_root_.Integration9_9.RandomizedCircuit.output]
open _root_.P2Mf6bd8d28 renaming h807 → _Pmf
attribute [local irreducible] copyQuantumDescription hadamardWords queryWords
@[fun_prop] theorem _root_.P2Mf6bd8d28.h796 (coins : Polynomial ℕ) :
    Poly (fun x : Str × Str => _root_.Integration9_9.RandomizedCircuit.description coins x.1 x.2) := by
  unfold _root_.Integration9_9.RandomizedCircuit.description
  fun_prop
open _root_.P2Mf6bd8d28 renaming h796 → _Pm4
theorem _root_.P2Mf6bd8d28.h795 (coins : Polynomial ℕ) (F : Family) (n : ℕ) :
    _root_.Integration9_9.RandomizedCircuit.description coins (unary n) (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins n))=encFamilyAt (_root_.Integration9_9.RandomizedCircuit.family coins F) n := by
  unfold _root_.Integration9_9.RandomizedCircuit.description
  rw [_root_.Integration9_9.TM2PlatformSerialization.lengthToken_eq,_Plj,_Pmf,_Plx,
    _Pel,_Pma,_Pml]
  change _=encNat (_root_.Integration9_9.RandomizedCircuit.ancillary coins F n)++encNat (_root_.Integration9_9.RandomizedCircuit.output coins F n).val++encCirc (_root_.Integration9_9.RandomizedCircuit.circuit coins F n)
  unfold _root_.Integration9_9.RandomizedCircuit.circuit
  simp only [_root_.Integration9_9.TM2PlatformSerialization.serializeWords_eq,encCirc,List.map_append,List.map_map,Function.comp_def]
  rfl
open _root_.P2Mf6bd8d28 renaming h795 → _Pm3
theorem _root_.P2Mf6bd8d28.h800 (coins : Polynomial ℕ) (F : Family) (hF : Uniform F) : Uniform (_root_.Integration9_9.RandomizedCircuit.family coins F) := by
  let generator := fun word : Str => _root_.Integration9_9.RandomizedCircuit.description coins word (encFamilyAt F (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length))
  refine ⟨generator,_Pg8 F hF (_root_.Integration9_9.LARCoinLayout.queryWireRequest coins)
    (_Pks coins) (_root_.Integration9_9.RandomizedCircuit.workLength coins) ?_ _ (_Pm4 coins),?_⟩
  · intro word
    simp only [_root_.Integration9_9.LARCoinLayout.queryWireRequest,List.length_map,eval_add,eval_X,List.map_replicate,unary,_root_.Integration9_9.RandomizedCircuit.workLength]
  · intro n
    dsimp only [generator]
    simpa only [unary,List.length_replicate] using _Pm3 coins F n
open _root_.P2Mf6bd8d28 renaming h800 → _Pm8
theorem _root_.P2Mf6bd8d28.h798 (coins : Polynomial ℕ) (F : Family) (hF : IsQPT F) : IsQPT (_root_.Integration9_9.RandomizedCircuit.family coins F) :=
  ⟨_Pm8 coins F hF.1,_Pm9 coins F hF.2.1,_Pm7 coins F hF.2.2⟩
open _root_.P2Mf6bd8d28 renaming h798 → _Pm6
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h773 → _Plh
open _root_.P2Mf6bd8d28 renaming h774 → _Pli
open _root_.P2Mf6bd8d28 renaming h775 → _Plj
open _root_.P2Mf6bd8d28 renaming h776 → _Plk
open _root_.P2Mf6bd8d28 renaming h787 → _Plv
open _root_.P2Mf6bd8d28 renaming h788 → _Plw
open _root_.P2Mf6bd8d28 renaming h789 → _Plx
open _root_.P2Mf6bd8d28 renaming h790 → _Ply
open _root_.P2Mf6bd8d28 renaming h791 → _Plz
open _root_.P2Mf6bd8d28 renaming h792 → _Pm0
open _root_.P2Mf6bd8d28 renaming h795 → _Pm3
open _root_.P2Mf6bd8d28 renaming h796 → _Pm4
open _root_.P2Mf6bd8d28 renaming h798 → _Pm6
open _root_.P2Mf6bd8d28 renaming h800 → _Pm8
open _root_.P2Mf6bd8d28 renaming h802 → _Pma
open _root_.P2Mf6bd8d28 renaming h803 → _Pmb
open _root_.P2Mf6bd8d28 renaming h807 → _Pmf
open _root_.P2Mf6bd8d28 renaming h808 → _Pmg
open _root_.P2Mf6bd8d28 renaming h813 → _Pml
open _root_.P2Mf6bd8d28 renaming h814 → _Pmm
open _root_.P2Mf6bd8d28 renaming h896 → _Pow
end
end
open _root_.P2Mf6bd8d28 renaming h773 → _Plh
open _root_.P2Mf6bd8d28 renaming h774 → _Pli
open _root_.P2Mf6bd8d28 renaming h775 → _Plj
open _root_.P2Mf6bd8d28 renaming h776 → _Plk
open _root_.P2Mf6bd8d28 renaming h787 → _Plv
open _root_.P2Mf6bd8d28 renaming h788 → _Plw
open _root_.P2Mf6bd8d28 renaming h789 → _Plx
open _root_.P2Mf6bd8d28 renaming h790 → _Ply
open _root_.P2Mf6bd8d28 renaming h791 → _Plz
open _root_.P2Mf6bd8d28 renaming h792 → _Pm0
open _root_.P2Mf6bd8d28 renaming h795 → _Pm3
open _root_.P2Mf6bd8d28 renaming h796 → _Pm4
open _root_.P2Mf6bd8d28 renaming h798 → _Pm6
open _root_.P2Mf6bd8d28 renaming h800 → _Pm8
open _root_.P2Mf6bd8d28 renaming h802 → _Pma
open _root_.P2Mf6bd8d28 renaming h803 → _Pmb
open _root_.P2Mf6bd8d28 renaming h807 → _Pmf
open _root_.P2Mf6bd8d28 renaming h808 → _Pmg
open _root_.P2Mf6bd8d28 renaming h813 → _Pml
open _root_.P2Mf6bd8d28 renaming h814 → _Pmm
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout
open QAlgorithms.Complexity Polynomial
open scoped BigOperators
theorem _root_.P2Mf6bd8d28.h797 (coins : Polynomial ℕ) (F : Family) (hF : _root_.Integration9_9.RandomizedCircuit.PreservesClassicalInput F) (word : Str) :
    acceptProb (_root_.Integration9_9.RandomizedCircuit.family coins F) word=
      avg (fun coin : Bits (coins.eval word.length) => acceptProb F (List.ofFn coin++word)) := by
  let branches := _root_.Integration9_9.RandomizedCircuit.branchOutput coins F word
  let superposition := ∑ coin : Bits (coins.eval word.length),_root_.InfoLossLAR.WorstCase.coinAmplitude (coins.eval word.length) • branches coin
  have hcast := _Pkf (_Pmn coins F word.length)
    (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word)) superposition)
    (Fin.natAdd word.length (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)))
  have hnorm :
      (∑ input : Bits (word.length+(_root_.Integration9_9.RandomizedCircuit.workLength coins word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1))),
        if input (Fin.natAdd word.length (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length))) then
          ‖_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word)) superposition input‖^2 else 0)=
      ∑ input : Bits (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1)),
        if input (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) then ‖superposition input‖^2 else 0 := by
    simpa only [Fin.append_right] using
      _P9l (toBits word) superposition
        (fun input => input (Fin.natAdd word.length (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length))))
  calc
    acceptProb (_root_.Integration9_9.RandomizedCircuit.family coins F) word=
        ∑ input : Bits (_root_.Integration9_9.RandomizedCircuit.width coins F word.length),if input (_root_.Integration9_9.RandomizedCircuit.output coins F word.length) then
          ‖_root_.Integration9_9.LARCoinLayout.castBodyState (_Pmn coins F word.length)
            (_root_.InfoLossLAR.WorstCase.tensorState (_root_.InfoLossLAR.WorstCase.computationalBasis (toBits word)) superposition) input‖^2 else 0 := by
      change (∑ input : Bits (_root_.Integration9_9.RandomizedCircuit.width coins F word.length),if input (_root_.Integration9_9.RandomizedCircuit.output coins F word.length) then
        ‖runLayered (_root_.Integration9_9.RandomizedCircuit.circuit coins F word.length)
          (basisInput (a := _root_.Integration9_9.RandomizedCircuit.ancillary coins F word.length) (toBits word)) input‖^2 else 0)=_
      rw [_Pls]
    _=∑ input : Bits (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1)),
        if input (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) then ‖superposition input‖^2 else 0 := hcast.trans hnorm
    _=avg (fun coin : Bits (coins.eval word.length) =>
        ∑ input : Bits (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length+(F.anc (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)+1)),
          if input (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)) then ‖branches coin input‖^2 else 0) :=
      _Pf8 (_root_.Integration9_9.RandomizedCircuit.coinLabel coins F word.length) branches
        (_Plm coins F hF word) (fun input => input (F.out (_root_.Integration9_9.RandomizedCircuit.workLength coins word.length)))
    _=avg (fun coin : Bits (coins.eval word.length) => acceptProb F (List.ofFn coin++word)) := by
      apply congrArg avg
      funext coin
      exact _Pln coins F word coin
open _root_.P2Mf6bd8d28 renaming h797 → _Pm5
theorem _root_.P2Mf6bd8d28.h816 (coins : Polynomial ℕ) (fallback : Str) (D : Family) (word : Str) :
    acceptProb (_root_.Integration9_9.RandomizedCircuit.family coins (_root_.Integration9_9.LARCoinLayout.bodyFamily coins (_root_.Integration9_9.LARCoinLayout.bodyQueryBudget coins fallback) fallback D)) word=
      avg (fun coin : Bits (coins.eval word.length) =>
        acceptProb D (_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback
          (encPair (List.ofFn coin) word))) := by
  rw [_Pm5 coins _ (_Plg _ _ _ _) word]
  apply congrArg avg
  funext coin
  rw [_Pjo,_Pkk coins fallback (List.ofFn coin) word (by simp)]
open _root_.P2Mf6bd8d28 renaming h816 → _Pmo
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h797 → _Pm5
open _root_.P2Mf6bd8d28 renaming h816 → _Pmo
end
end
open _root_.P2Mf6bd8d28 renaming h797 → _Pm5
open _root_.P2Mf6bd8d28 renaming h816 → _Pmo
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase
open Integration9_9.LARCoinLayout Integration9_9.LARRankOneMachine Integration9_9.TM2PlatformSerialization
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
@[fun_prop] theorem _root_.P2Mf6bd8d28.h810 : Poly _root_.Integration9_9.RandomizedCircuit.passOutput := by
  unfold _root_.Integration9_9.RandomizedCircuit.passOutput
  fun_prop
open _root_.P2Mf6bd8d28 renaming h810 → _Pmi
theorem _root_.P2Mf6bd8d28.h811 : PolyTimeComputable _root_.Integration9_9.RandomizedCircuit.passOutput := _Pmx _Pmi
open _root_.P2Mf6bd8d28 renaming h811 → _Pmj
theorem _root_.P2Mf6bd8d28.h809 (word : Str) (bit : Bool) : _root_.Integration9_9.RandomizedCircuit.passOutput (word++[bit])=[bit] := by
  simp [_root_.Integration9_9.RandomizedCircuit.passOutput,List.reverse_append]
open _root_.P2Mf6bd8d28 renaming h809 → _Pmh
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h809 → _Pmh
open _root_.P2Mf6bd8d28 renaming h810 → _Pmi
open _root_.P2Mf6bd8d28 renaming h811 → _Pmj
end
open _root_.P2Mf6bd8d28 renaming h809 → _Pmh
open _root_.P2Mf6bd8d28 renaming h810 → _Pmi
open _root_.P2Mf6bd8d28 renaming h811 → _Pmj
namespace Integration9_9.GenericBodySemantics.castBodyState
end Integration9_9.GenericBodySemantics.castBodyState
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase
open QAlgorithms.Complexity Polynomial
open OAI.MetricKMedian.Binary
open Integration9_9.RandomizedCircuit
theorem _root_.P2Mf6bd8d28.h688 (R : _root_.Integration9_9.GenericBodySemantics.QuerySpecification) (D : Family) :
    _root_.Integration9_9.RandomizedCircuit.PreservesClassicalInput (_root_.Integration9_9.GenericBody.bodyFamily R.machine D) := by
  intro word output hn index
  exact _Pin R D word output hn index
open _root_.P2Mf6bd8d28 renaming h688 → _Pj4
theorem _root_.P2Mf6bd8d28.h694 {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) (hD : IsQPT D) : IsQPT (_root_.Integration9_9.GenericBodySemantics.nativeFamily P coins D) :=
  _Pm6 coins _
    (_Ph8 (_root_.Integration9_9.GenericBodySemantics.specificationOfPre P coins).machine D hD)
open _root_.P2Mf6bd8d28 renaming h694 → _Pja
theorem _root_.P2Mf6bd8d28.h691 {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) (word : Str) :
    acceptProb (_root_.Integration9_9.GenericBodySemantics.nativeFamily P coins D) word=
      avg (fun coin : Bits (coins.eval word.length) => acceptProb D (pre (encPair (List.ofFn coin) word))) := by
  unfold _root_.Integration9_9.GenericBodySemantics.nativeFamily
  rw [_Pm5 coins _
    (_Pj4 (_root_.Integration9_9.GenericBodySemantics.specificationOfPre P coins) D) word]
  apply congrArg avg
  funext coin
  rw [_Pim (_root_.Integration9_9.GenericBodySemantics.specificationOfPre P coins) D]
  exact congrArg (acceptProb D) (_Pje P coins (List.ofFn coin) word (by simp))
open _root_.P2Mf6bd8d28 renaming h691 → _Pj7
theorem _root_.P2Mf6bd8d28.h693 {pre : Str → Str} (P : PolyProgram id id pre) (coins : Polynomial ℕ)
    (D : Family) : CallsOnce (_root_.Integration9_9.GenericBodySemantics.nativeFamily P coins D) D := by
  refine ⟨pre,_root_.Integration9_9.RandomizedCircuit.passOutput,coins,⟨P.stock⟩,_Pmj,?_⟩
  intro word
  rw [_Pj7]
  apply congrArg avg
  funext coin
  simp [_Pmh]
open _root_.P2Mf6bd8d28 renaming h693 → _Pj9
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h688 → _Pj4
open _root_.P2Mf6bd8d28 renaming h691 → _Pj7
open _root_.P2Mf6bd8d28 renaming h693 → _Pj9
open _root_.P2Mf6bd8d28 renaming h694 → _Pja
end
end
open _root_.P2Mf6bd8d28 renaming h688 → _Pj4
open _root_.P2Mf6bd8d28 renaming h691 → _Pj7
open _root_.P2Mf6bd8d28 renaming h693 → _Pj9
open _root_.P2Mf6bd8d28 renaming h694 → _Pja
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity AFT
open scoped BigOperators Classical
theorem _root_.P2Mf6bd8d28.h330 {Index First Second : Type} [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (law : Index → _root_.AFT.FiniteDist First) (kernel : Index → First → _root_.AFT.FiniteDist Second) :
    (_root_.AFT.FiniteDist.independent law).mix (fun seeds => _root_.AFT.FiniteDist.independent (fun index => kernel index (seeds index)))=
      _root_.AFT.FiniteDist.independent (fun index => (law index).mix (kernel index)) := by
  ext word
  simp only [_root_.AFT.FiniteDist.mix_weight,_root_.AFT.FiniteDist.independent,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun index point =>
    (law index).weight point*(kernel index point).weight (word index))).symm
open _root_.P2Mf6bd8d28 renaming h330 → _P96
theorem _root_.P2Mf6bd8d28.h329 {Index Input Output : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Input] [Fintype Output] (law : Index → _root_.AFT.FiniteDist Input)
    (decode : Index → Input → Output) :
    (_root_.AFT.FiniteDist.independent law).map (fun word index => decode index (word index))=
      _root_.AFT.FiniteDist.independent (fun index => (law index).map (decode index)) := by
  ext values
  simp only [_root_.AFT.FiniteDist.map_weight,_root_.AFT.FiniteDist.independent]
  have h := Fintype.prod_sum (fun index point =>
    if decode index point=values index then (law index).weight point else 0)
  apply Eq.trans ?_ h.symm
  apply Finset.sum_congr rfl
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]
open _root_.P2Mf6bd8d28 renaming h329 → _P95
theorem _root_.P2Mf6bd8d28.h331 {Index First Second : Type}
    [Fintype Index] [DecidableEq Index] [Fintype First] [Fintype Second]
    (first : Index → _root_.AFT.FiniteDist First) (second : Index → _root_.AFT.FiniteDist Second)
    (value : (Index → First × Second) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun index => (first index).prod (second index))).expectation value=
      (_root_.AFT.FiniteDist.independent first).expectation (fun left =>
        (_root_.AFT.FiniteDist.independent second).expectation (fun right => value (fun index => (left index,right index)))) := by
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
  rw [←(Equiv.arrowProdEquivProdArrow Index (fun _ => First) (fun _ => Second)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.arrowProdEquivProdArrow,Equiv.coe_fn_symm_mk,_root_.AFT.FiniteDist.prod_weight,
    Finset.prod_mul_distrib,mul_assoc]
open _root_.P2Mf6bd8d28 renaming h331 → _P97
private theorem _root_.P2Mf6bd8d28.h838 {Index State : Type} [Fintype Index] [DecidableEq Index] [Fintype State] [Nonempty State] :
    _root_.AFT.FiniteDist.independent (fun _ : Index => _root_.AFT.FiniteDist.uniform State)=_root_.AFT.FiniteDist.uniform (Index → State) := by
  ext word
  simp only [_root_.AFT.FiniteDist.independent,_root_.AFT.FiniteDist.uniform_weight,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow,inv_pow]
open _root_.P2Mf6bd8d28 renaming h838 → _Pna
private theorem _root_.P2Mf6bd8d28.h837 {α : Type} [Fintype α] [Nonempty α] (test : α → ℝ) :
    (_root_.AFT.FiniteDist.uniform α).expectation test=avg test := by
  simp only [_root_.AFT.FiniteDist.expectation,_root_.AFT.FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h837 → _Pn9
theorem _root_.P2Mf6bd8d28.h499 {q d N : ℕ} [NeZero q] (B : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) :
    prRealLWE B lam pp q N d t source.weight=
      avg (fun secret : Fin N → ZMod q =>
        (_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw q N d t source secret).expectation
          (fun table => acceptProb B (encInput lam pp (encTable table)))) := by
  unfold prRealLWE
  apply congrArg avg
  funext secret
  rw [_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod,_Pn9]
  rfl
open _root_.P2Mf6bd8d28 renaming h499 → _Pdv
theorem _root_.P2Mf6bd8d28.h490 {q d N : ℕ} [NeZero q] (B : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    prIdealLWE B lam pp q N d t=
      (_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw q N d t).expectation
        (fun table => acceptProb B (encInput lam pp (encTable table))) := by
  unfold prIdealLWE
  rw [_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod]
  simp only [_Pn9,Function.comp_def]
open _root_.P2Mf6bd8d28 renaming h490 → _Pdm
theorem _root_.P2Mf6bd8d28.h338 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (D : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q)) :
    _root_.InfoLossLAR.WorstCase.affinePreprocessedReal (N := N) D lam pp t samp source=
      avg (fun secret : Fin N → ZMod q =>
        (_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw q N d t source secret).expectation (fun table =>
          avg (fun seeds : Fin t → Ω => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table)))))) := by
  unfold _root_.InfoLossLAR.WorstCase.affinePreprocessedReal
  apply congrArg avg
  funext secret
  unfold _root_.InfoLossLAR.WorstCase.affineLWEBlockLaw
  rw [←_P96 (fun _ : Fin t => _root_.AFT.FiniteDist.uniform Ω)
    (fun (_ : Fin t) seed =>
      ((_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod source).map
        (fun draw => (matModq q (samp seed).1*draw.1,
          evalAffine (samp seed).1 (samp seed).2 (draw.1.mulVec secret+draw.2)))),
    _root_.AFT.FiniteDist.expectation_mix,_Pna,_Pn9]
  have hs := _root_.AFT.FiniteDist.expectation_comm (_root_.AFT.FiniteDist.uniform (Fin t → Ω))
    (_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw q N d t source secret)
    (fun seeds table => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))))
  simp only [_Pn9] at hs
  rw [←hs]
  apply congrArg avg
  funext seeds
  rw [←_P95,_root_.AFT.FiniteDist.expectation_map,
    _P97,_Pna,_Pn9]
  rw [_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod,_Pn9]
  rfl
open _root_.P2Mf6bd8d28 renaming h338 → _P9e
theorem _root_.P2Mf6bd8d28.h337 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (D : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) :
    _root_.InfoLossLAR.WorstCase.affinePreprocessedIdeal (q := q) (N := N) D lam pp t samp=
      (_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw q N d t).expectation (fun table =>
        avg (fun seeds : Fin t → Ω => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))))) := by
  unfold _root_.InfoLossLAR.WorstCase.affinePreprocessedIdeal _root_.InfoLossLAR.WorstCase.affineMatrixErrorLaw
  rw [←_P96 (fun _ : Fin t => _root_.AFT.FiniteDist.uniform Ω)
    (fun (_ : Fin t) seed =>
      ((_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod
        (_root_.AFT.FiniteDist.uniform (Fin d → ZMod q))).map
        (fun draw => (matModq q (samp seed).1*draw.1,
          evalAffine (samp seed).1 (samp seed).2 draw.2))),
    _root_.AFT.FiniteDist.expectation_mix,_Pna,_Pn9]
  have hs := _root_.AFT.FiniteDist.expectation_comm (_root_.AFT.FiniteDist.uniform (Fin t → Ω))
    (_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw q N d t)
    (fun seeds table => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))))
  simp only [_Pn9] at hs
  rw [←hs]
  apply congrArg avg
  funext seeds
  rw [←_P95,_root_.AFT.FiniteDist.expectation_map,
    _P97,_Pna,_Pn9]
  simp_rw [_Pna,_Pn9]
  rw [_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod]
  simp only [_Pn9,Function.comp_def]
  rfl
open _root_.P2Mf6bd8d28 renaming h337 → _P9d
theorem _root_.P2Mf6bd8d28.h327 {q d N : ℕ} [NeZero q] {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (B D : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hencoded : ∀ table : Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q),
      acceptProb B (encInput lam pp (encTable table))=
        avg (fun seeds : Fin t → Ω => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))))) :
    prRealLWE B lam pp q N d t source.weight=_root_.InfoLossLAR.WorstCase.affinePreprocessedReal (N := N) D lam pp t samp source := by
  rw [_Pdv,_P9e]
  simp_rw [hencoded]
open _root_.P2Mf6bd8d28 renaming h327 → _P93
theorem _root_.P2Mf6bd8d28.h326 {q d N : ℕ} [NeZero q] {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (B D : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ))
    (hencoded : ∀ table : Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q),
      acceptProb B (encInput lam pp (encTable table))=
        avg (fun seeds : Fin t → Ω => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))))) :
    prIdealLWE B lam pp q N d t=_root_.InfoLossLAR.WorstCase.affinePreprocessedIdeal (q := q) (N := N) D lam pp t samp := by
  rw [_Pdm,_P9d]
  simp_rw [hencoded]
open _root_.P2Mf6bd8d28 renaming h326 → _P92
theorem _root_.P2Mf6bd8d28.h328 {q d N : ℕ} [NeZero q] {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (B D : Family) (lam : ℕ) (pp : Str) (t : ℕ)
    (samp : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) (σ : ℝ) (hσ : 0 < σ)
    (hencoded : ∀ table : Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q),
      acceptProb B (encInput lam pp (encTable table))=
        avg (fun seeds : Fin t → Ω => acceptProb D (encInput lam pp (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable samp seeds table))))) :
    advLWE B lam pp q N d t (chiG q d σ)=_root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv (q := q) (N := N) D lam pp t samp σ hσ := by
  have hsource : (_root_.AFT.GaussianSource.residueGaussian d q σ hσ).weight=chiG q d σ :=
    funext (_P4z q d σ hσ)
  rw [←hsource]
  unfold advLWE _root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv _root_.InfoLossLAR.WorstCase.affinePreprocessedAdv
  rw [_P93 B D lam pp t samp _ hencoded,_P92 B D lam pp t samp hencoded]
open _root_.P2Mf6bd8d28 renaming h328 → _P94
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h326 → _P92
open _root_.P2Mf6bd8d28 renaming h327 → _P93
open _root_.P2Mf6bd8d28 renaming h328 → _P94
open _root_.P2Mf6bd8d28 renaming h329 → _P95
open _root_.P2Mf6bd8d28 renaming h330 → _P96
open _root_.P2Mf6bd8d28 renaming h331 → _P97
open _root_.P2Mf6bd8d28 renaming h337 → _P9d
open _root_.P2Mf6bd8d28 renaming h338 → _P9e
open _root_.P2Mf6bd8d28 renaming h490 → _Pdm
open _root_.P2Mf6bd8d28 renaming h499 → _Pdv
open _root_.P2Mf6bd8d28 renaming h837 → _Pn9
open _root_.P2Mf6bd8d28 renaming h838 → _Pna
end
end
open _root_.P2Mf6bd8d28 renaming h326 → _P92
open _root_.P2Mf6bd8d28 renaming h327 → _P93
open _root_.P2Mf6bd8d28 renaming h328 → _P94
open _root_.P2Mf6bd8d28 renaming h329 → _P95
open _root_.P2Mf6bd8d28 renaming h330 → _P96
open _root_.P2Mf6bd8d28 renaming h331 → _P97
open _root_.P2Mf6bd8d28 renaming h337 → _P9d
open _root_.P2Mf6bd8d28 renaming h338 → _P9e
open _root_.P2Mf6bd8d28 renaming h490 → _Pdm
open _root_.P2Mf6bd8d28 renaming h499 → _Pdv
section
set_option autoImplicit false
namespace InfoLossLAR.WorstCase
theorem _root_.P2Mf6bd8d28.h419 (lam : ℕ) :
    famq lam ≤ 2 ^ 17 * (lam + 2) ^ 64 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul
    (2 ^ 16 * famL lam ^ 64) (by unfold famL; positivity)
  have hminimal : famq lam ≤ p :=
    Nat.find_min' (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64)) ⟨hlt.le, hp⟩
  calc
    famq lam ≤ p := hminimal
    _ ≤ 2 * (2 ^ 16 * famL lam ^ 64) := hle
    _ = 2 ^ 17 * (lam + 2) ^ 64 := by unfold famL; norm_num [← mul_assoc]
open _root_.P2Mf6bd8d28 renaming h419 → _Pbn
theorem _root_.P2Mf6bd8d28.h420 : PolyBoundedFn famq := by
  refine ⟨Polynomial.C (2 ^ 17) * (Polynomial.X + Polynomial.C 2) ^ 64, ?_⟩
  intro lam
  simpa using _Pbn lam
open _root_.P2Mf6bd8d28 renaming h420 → _Pbo
theorem _root_.P2Mf6bd8d28.h559 (lam : ℕ) : lam ≤ famq lam := by
  have hspec := (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).1
  have hpow : famL lam ≤ famL lam ^ 64 := le_self_pow (by unfold famL; omega) (by norm_num)
  have hfac : famL lam ^ 64 ≤ 2 ^ 16 * famL lam ^ 64 := by omega
  exact (by unfold famL; omega : lam ≤ famL lam).trans (hpow.trans (hfac.trans hspec))
open _root_.P2Mf6bd8d28 renaming h559 → _Pfj
theorem _root_.P2Mf6bd8d28.h557 (x : ℝ) (hx : 0 ≤ x) (c : ℕ) :
    x ^ (-(c : ℝ)) = (x ^ c)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]
open _root_.P2Mf6bd8d28 renaming h557 → _Pfh
theorem _root_.P2Mf6bd8d28.h483 (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  calc
    p.eval n = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i :=
      p.eval_eq_sum_range n
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _
        (pow_le_pow_right' hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = p.eval 1 * n ^ p.natDegree := by
      rw [← Finset.sum_mul]
      congr 1
      simpa using (p.eval_eq_sum_range 1).symm
open _root_.P2Mf6bd8d28 renaming h483 → _Pdf
theorem _root_.P2Mf6bd8d28.h482 (f : ℕ → ℕ) (hf : PolyBoundedFn f) :
    ∃ k n₀ : ℕ, ∀ n ≥ n₀, f n ≤ n ^ k := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p.natDegree + 1, max 1 (p.eval 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hcoef : p.eval 1 ≤ n := le_trans (le_max_right _ _) hn
  calc
    f n ≤ p.eval n := hp n
    _ ≤ p.eval 1 * n ^ p.natDegree := _Pdf p n hn1
    _ ≤ n * n ^ p.natDegree := Nat.mul_le_mul_right _ hcoef
    _ = n ^ (p.natDegree + 1) := by rw [pow_succ]; ac_rfl
open _root_.P2Mf6bd8d28 renaming h482 → _Pde
theorem _root_.P2Mf6bd8d28.h462 (q n c : ℕ) (hn : 2 ≤ n) (hcn : c + 2 ≤ n)
    (hnq : n ≤ q) :
    ((q : ℝ) ^ n)⁻¹ ≤ (1 / 4) * (n : ℝ) ^ (-(c : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hfour : 4 * (n : ℝ) ^ c ≤ (q : ℝ) ^ n := by
    have hbase : 4 ≤ (n : ℝ) ^ 2 := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    calc
      4 * (n : ℝ) ^ c ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ c := by gcongr
      _ = (n : ℝ) ^ (c + 2) := by rw [pow_add]; ring
      _ ≤ (n : ℝ) ^ n := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ n)) hcn
      _ ≤ (q : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hnq) _
  rw [_Pfh _ (by positivity)]
  have hqnat : 0 < q := by omega
  have hqpos : 0 < (q : ℝ) ^ n := by positivity
  have hrecip := (inv_le_inv₀ hqpos (by positivity : 0 < 4 * (n : ℝ) ^ c)).mpr hfour
  simpa [mul_inv_rev, div_eq_mul_inv, mul_comm] using hrecip
open _root_.P2Mf6bd8d28 renaming h462 → _Pcu
theorem _root_.P2Mf6bd8d28.h439
    (n q t a s c : ℕ) (hn : 2 ≤ n) (hcn : c + 2 ≤ n) (hnq : n ≤ q)
    (hqa : q ≤ n ^ a) (hts : t ≤ n ^ s) (L G : ℝ)
    (hadv : (n : ℝ) ^ (-(c : ℝ)) ≤ L)
    (hcomparison : L ≤ (q : ℝ) * G +
      (q : ℝ) * (t : ℝ) * (n : ℝ) ^ (-((c + a + s + 2 : ℕ) : ℝ)) +
      ((q : ℝ) ^ n)⁻¹) :
    (n : ℝ) ^ (-((c + a + 1 : ℕ) : ℝ)) ≤ G := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hqnat : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqnat
  have hqaR : (q : ℝ) ≤ (n : ℝ) ^ a := by exact_mod_cast hqa
  have htsR : (t : ℝ) ≤ (n : ℝ) ^ s := by exact_mod_cast hts
  have hqt : (q : ℝ) * (t : ℝ) ≤ (n : ℝ) ^ (a + s) := by
    rw [pow_add]
    exact mul_le_mul hqaR htsR (by positivity) (by positivity)
  have hfour : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have herror : (q : ℝ) * (t : ℝ) * (n : ℝ) ^ (-((c + a + s + 2 : ℕ) : ℝ)) ≤
      (1 / 4) * (n : ℝ) ^ (-(c : ℝ)) := by
    rw [_Pfh (n : ℝ) hn0.le (c + a + s + 2),
      _Pfh (n : ℝ) hn0.le c]
    have herr : (q : ℝ) * (t : ℝ) / (n : ℝ) ^ (c + a + s + 2) ≤
        1 / (4 * (n : ℝ) ^ c) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      calc
        (q : ℝ) * (t : ℝ) * (4 * (n : ℝ) ^ c) ≤
          (n : ℝ) ^ (a + s) * ((n : ℝ) ^ 2 * (n : ℝ) ^ c) := by
            exact mul_le_mul hqt (mul_le_mul_of_nonneg_right hfour (by positivity))
              (by positivity) (by positivity)
        _ = 1 * (n : ℝ) ^ (c + a + s + 2) := by
          rw [← pow_add, ← pow_add, one_mul]
          congr 1
          omega
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using herr
  have hzero := _Pcu q n c hn hcn hnq
  have hgap : (1 / 2) * (n : ℝ) ^ (-(c : ℝ)) ≤ (q : ℝ) * G := by
    linarith
  have hhalf : (n : ℝ) ^ (-((c + a + 1 : ℕ) : ℝ)) * (n : ℝ) ^ a ≤
      (1 / 2) * (n : ℝ) ^ (-(c : ℝ)) := by
    rw [_Pfh (n : ℝ) hn0.le (c + a + 1),
      _Pfh (n : ℝ) hn0.le c]
    have heq : ((n : ℝ) ^ (c + a + 1))⁻¹ * (n : ℝ) ^ a =
        ((n : ℝ) ^ c)⁻¹ / (n : ℝ) := by
      rw [show c + a + 1 = c + 1 + a by omega, pow_add, mul_inv_rev]
      field_simp
      rw [pow_succ]
    rw [heq]
    apply (div_le_iff₀ hn0).mpr
    have : 0 ≤ ((n : ℝ) ^ c)⁻¹ := by positivity
    nlinarith
  have hproduct : (q : ℝ) * (n : ℝ) ^ (-((c + a + 1 : ℕ) : ℝ)) ≤ (q : ℝ) * G := by
    calc
      (q : ℝ) * (n : ℝ) ^ (-((c + a + 1 : ℕ) : ℝ)) ≤
        (n : ℝ) ^ a * (n : ℝ) ^ (-((c + a + 1 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hqaR (by positivity)
      _ ≤ (1 / 2) * (n : ℝ) ^ (-(c : ℝ)) := by simpa [mul_comm] using hhalf
      _ ≤ (q : ℝ) * G := hgap
  exact le_of_mul_le_mul_left hproduct hq0
open _root_.P2Mf6bd8d28 renaming h439 → _Pc7
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h419 → _Pbn
open _root_.P2Mf6bd8d28 renaming h420 → _Pbo
open _root_.P2Mf6bd8d28 renaming h439 → _Pc7
open _root_.P2Mf6bd8d28 renaming h462 → _Pcu
open _root_.P2Mf6bd8d28 renaming h482 → _Pde
open _root_.P2Mf6bd8d28 renaming h483 → _Pdf
open _root_.P2Mf6bd8d28 renaming h557 → _Pfh
open _root_.P2Mf6bd8d28 renaming h559 → _Pfj
end
open _root_.P2Mf6bd8d28 renaming h419 → _Pbn
open _root_.P2Mf6bd8d28 renaming h420 → _Pbo
open _root_.P2Mf6bd8d28 renaming h439 → _Pc7
open _root_.P2Mf6bd8d28 renaming h462 → _Pcu
open _root_.P2Mf6bd8d28 renaming h482 → _Pde
open _root_.P2Mf6bd8d28 renaming h483 → _Pdf
open _root_.P2Mf6bd8d28 renaming h557 → _Pfh
open _root_.P2Mf6bd8d28 renaming h559 → _Pfj
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Integration9_9.BlockCoins
open InfoLossLAR.WorstCase QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h587 (blocks bits tail total : ℕ) (h : blocks*bits+tail ≤ total)
    (test : (Fin blocks → Fin bits → Bool) × (Fin tail → Bool) → ℝ) :
    avg (fun tape : Fin total → Bool => test
      ((fun block bit => tape (Fin.castLE h (Fin.castAdd tail (finProdFinEquiv (block,bit))))),
        (fun bit => tape (Fin.castLE h (Fin.natAdd (blocks*bits) bit)))))=avg test := by
  calc
    _=avg (fun tape : Fin (blocks*bits+tail) → Bool => test (_root_.Integration9_9.BlockCoins.blocksAndTailEquiv blocks bits tail tape)) :=
      _Pgg h (fun tape => test (_root_.Integration9_9.BlockCoins.blocksAndTailEquiv blocks bits tail tape))
    _=avg test := _Pgd (_root_.Integration9_9.BlockCoins.blocksAndTailEquiv blocks bits tail) test
open _root_.P2Mf6bd8d28 renaming h587 → _Pgb
end Integration9_9.BlockCoins
open _root_.P2Mf6bd8d28 renaming h587 → _Pgb
end
open _root_.P2Mf6bd8d28 renaming h587 → _Pgb
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Integration9_9.BlockCoins
open InfoLossLAR.WorstCase QAlgorithms.Complexity
theorem _root_.P2Mf6bd8d28.h588 {total : ℕ} (tape : Fin total → Bool) (start count : ℕ)
    (h : start+count ≤ total) :
    ((List.ofFn tape).drop start).take count=
      List.ofFn (fun bit : Fin count => tape ⟨start+bit.val,by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro index hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
open _root_.P2Mf6bd8d28 renaming h588 → _Pgc
end Integration9_9.BlockCoins
open _root_.P2Mf6bd8d28 renaming h588 → _Pgc
end
open _root_.P2Mf6bd8d28 renaming h588 → _Pgc
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GenericBodySemantics
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
theorem _root_.P2Mf6bd8d28.h661 {First Second : Type} [Fintype First] [Fintype Second]
    (test : First × Second → ℝ) : avg test=avg (fun first => avg (fun second => test (first,second))) := by
  simp only [avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,←Finset.sum_div]
  ring
open _root_.P2Mf6bd8d28 renaming h661 → _Pid
theorem _root_.P2Mf6bd8d28.h692 {pre : Str → Str} (P : PolyProgram id id pre)
    (coins : Polynomial ℕ) (D : Family) (word : Str) (blocks bits tail : ℕ)
    (h : blocks*bits+tail ≤ coins.eval word.length)
    (target : (Fin blocks → Fin bits → Bool) × (Fin tail → Bool) → Str)
    (hpre : ∀ tape : Fin (coins.eval word.length) → Bool,
      pre (encPair (List.ofFn tape) word)=target
        ((fun block bit => tape (Fin.castLE h (Fin.castAdd tail (finProdFinEquiv (block,bit))))),
          (fun bit => tape (Fin.castLE h (Fin.natAdd (blocks*bits) bit))))) :
    acceptProb (_root_.Integration9_9.GenericBodySemantics.nativeFamily P coins D) word=
      avg (fun seeds : Fin blocks → Fin bits → Bool => avg (fun rankTape : Fin tail → Bool =>
        acceptProb D (target (seeds,rankTape)))) := by
  rw [_Pj7]
  simp_rw [hpre]
  exact (_Pgb blocks bits tail (coins.eval word.length) h
    (fun draws => acceptProb D (target draws))).trans (_Pid _)
open _root_.P2Mf6bd8d28 renaming h692 → _Pj8
end Integration9_9.GenericBodySemantics
open _root_.P2Mf6bd8d28 renaming h661 → _Pid
open _root_.P2Mf6bd8d28 renaming h692 → _Pj8
end
end
open _root_.P2Mf6bd8d28 renaming h661 → _Pid
open _root_.P2Mf6bd8d28 renaming h692 → _Pj8
namespace Integration9_9.BlockCoins
end Integration9_9.BlockCoins
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GaussianRankOnePre
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
open QAlgorithms.Complexity Polynomial CurrentAFT
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime LARRankOneMachine LARCoinLayout TM2PlatformSerialization LARPlatformEncoding
attribute [local irreducible] TM2NativeAffinePre.fields TM2NativeAffinePre.current TM2NativeAffinePre.blockBits
theorem _root_.P2Mf6bd8d28.h601 (word : Str) :
    Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount word) ≤ _root_.Integration9_9.GaussianRankOnePre.rankCoinBudget.eval word.length := by
  have h := _root_.Integration9_9.LARRankOneMachine.observedTicketCount_poly.program.length_bound word
  change (Nat.bits (_root_.Integration9_9.LARRankOneMachine.observedTicketCount word)).length ≤ _root_.Integration9_9.LARRankOneMachine.observedTicketCount_poly.program.sizeBound.eval
    (encodeList encodeBool word).length at h
  simpa only [_root_.Integration9_9.GaussianRankOnePre.rankCoinBudget,Nat.size_eq_bits_len,BooleanLists.length,eval_comp,eval_mul,eval_ofNat,eval_X] using h
open _root_.P2Mf6bd8d28 renaming h601 → _Pgp
theorem _root_.P2Mf6bd8d28.h605 {q N d count : ℕ} (hd : 0 < d) (ht : 0 < count)
    (security width : ℕ)
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) :
    _root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput security (encB q++encB N++encB d++encB width) (encTable table))=q^(N+count) := by
  cases d with
  | zero => omega
  | succ n => exact _Plb ht security width table
open _root_.P2Mf6bd8d28 renaming h605 → _Pgt
theorem _root_.P2Mf6bd8d28.h595 (m : Polynomial ℕ) {q N d count : ℕ} (hd : 0 < d) (ht : 0 < count)
    (security width : ℕ)
    (table : Fin count → Matrix (Fin d) (Fin N) (ZMod q) × (Fin d → ZMod q)) :
    count*m.eval security+Nat.size (q^(N+count)) ≤
      (_root_.Integration9_9.GaussianRankOnePre.coins m).eval (encInput security (encB q++encB N++encB d++encB width) (encTable table)).length := by
  have hs := _Pmq m security (encB q++encB N++encB d++encB width) table
  have hr := _Pgp (encInput security (encB q++encB N++encB d++encB width) (encTable table))
  rw [_Pgt hd ht security width table] at hr
  simpa only [_root_.Integration9_9.GaussianRankOnePre.coins,eval_add] using Nat.add_le_add hs hr
open _root_.P2Mf6bd8d28 renaming h595 → _Pgj
end Integration9_9.GaussianRankOnePre
open _root_.P2Mf6bd8d28 renaming h595 → _Pgj
open _root_.P2Mf6bd8d28 renaming h601 → _Pgp
open _root_.P2Mf6bd8d28 renaming h605 → _Pgt
end
end
open _root_.P2Mf6bd8d28 renaming h595 → _Pgj
open _root_.P2Mf6bd8d28 renaming h601 → _Pgp
open _root_.P2Mf6bd8d28 renaming h605 → _Pgt
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.RandomizedCircuit
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LARCoinLayout Integration9_9.LARRankOneMachine
open QAlgorithms.Complexity Polynomial AFT
open scoped BigOperators
private theorem _root_.P2Mf6bd8d28.h899 {α : Type} [Fintype α] [Nonempty α] (test : α → ℝ) :
    (_root_.AFT.FiniteDist.uniform α).expectation test=avg test := by
  simp only [_root_.AFT.FiniteDist.expectation,_root_.AFT.FiniteDist.uniform_weight,avg,←Finset.mul_sum]
  ring
open _root_.P2Mf6bd8d28 renaming h899 → Integration9_9.RandomizedCircuit.uniform_expectation_avg
open _root_.P2Mf6bd8d28 renaming h899 → _Poz
theorem _root_.P2Mf6bd8d28.h817 (B D : Family) (fallback : Str) (q N n t : ℕ)
    [Fact q.Prime] [NeZero q] (lam width : ℕ) (source : _root_.AFT.FiniteDist (Fin (n+1) → ZMod q))
    (h : ∀ table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q),
      acceptProb B (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))=
        avg (fun tape : Fin (Nat.size (q^(N+t*1))) → Bool => acceptProb D
          (_root_.InfoLossLAR.WorstCase.boundedRankOnePre lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
            (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) tape table))) :
    prRealLWE B lam (encB q++encB N++encB (n+1)++encB width) q N (n+1) t source.weight=
      _root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR D lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
        source (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) := by
  unfold prRealLWE _root_.InfoLossLAR.WorstCase.prBoundedRankOneRealLAR
  apply congrArg avg
  funext secret
  rw [_root_.InfoLossLAR.WorstCase.larObservedRealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod,_Poz]
  simp only [_root_.AFT.FiniteDist.expectation,_root_.AFT.FiniteDist.independent]
  simp_rw [h]
  rfl
open _root_.P2Mf6bd8d28 renaming h817 → _Pmp
theorem _root_.P2Mf6bd8d28.h805 (B D : Family) (fallback : Str) (q N n t : ℕ)
    [Fact q.Prime] [NeZero q] (lam width : ℕ)
    (h : ∀ table : Fin t → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q),
      acceptProb B (encInput lam (encB q++encB N++encB (n+1)++encB width) (encTable table))=
        avg (fun tape : Fin (Nat.size (q^(N+t*1))) → Bool => acceptProb D
          (_root_.InfoLossLAR.WorstCase.boundedRankOnePre lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
            (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) tape table))) :
    prIdealLWE B lam (encB q++encB N++encB (n+1)++encB width) q N (n+1) t=
      _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR D lam (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 t
        (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) := by
  unfold prIdealLWE _root_.InfoLossLAR.WorstCase.prBoundedRankOneIdealLAR
  rw [_root_.InfoLossLAR.WorstCase.larObservedIdealTableLaw,_root_.AFT.FiniteDist.expectation_map,_root_.AFT.FiniteDist.expectation_prod]
  simp only [_Poz,Function.comp_def]
  simp_rw [h]
open _root_.P2Mf6bd8d28 renaming h805 → _Pmd
end Integration9_9.RandomizedCircuit
open _root_.P2Mf6bd8d28 renaming h805 → _Pmd
open _root_.P2Mf6bd8d28 renaming h817 → _Pmp
open _root_.P2Mf6bd8d28 renaming h899 → Integration9_9.RandomizedCircuit.uniform_expectation_avg
open _root_.P2Mf6bd8d28 renaming h899 → _Poz
end
end
open _root_.P2Mf6bd8d28 renaming h805 → _Pmd
open _root_.P2Mf6bd8d28 renaming h817 → _Pmp
namespace Integration9_9.RandomizedCircuit.uniform_expectation_avg
end Integration9_9.RandomizedCircuit.uniform_expectation_avg
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open Integration9_9.RandomizedCircuit
theorem _root_.P2Mf6bd8d28.h425 (lam : ℕ) : 0 < famd lam := by
  unfold famd famL
  positivity
open _root_.P2Mf6bd8d28 renaming h425 → _Pbt
theorem _root_.P2Mf6bd8d28.h428 (lam : ℕ) : famq lam ≤ famd lam := by
  have hp : 1 ≤ famL lam^96 := one_le_pow₀ (by unfold famL; omega)
  have h := Nat.mul_le_mul_left (famq lam) hp
  unfold famd
  have hbound : famq lam ≤ famq lam*famL lam^96 := by simpa only [Nat.mul_one] using h
  exact hbound.trans (Nat.le_add_right _ _)
open _root_.P2Mf6bd8d28 renaming h428 → _Pbw
attribute [local irreducible] famq famd famL famσ
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h425 → _Pbt
open _root_.P2Mf6bd8d28 renaming h428 → _Pbw
end
open _root_.P2Mf6bd8d28 renaming h425 → _Pbt
open _root_.P2Mf6bd8d28 renaming h428 → _Pbw
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GaussianRankOnePre
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.Integration
open QAlgorithms.Complexity Polynomial CurrentAFT
open OAI.MetricKMedian.Binary
open LARRankOneMachine LARCoinLayout GenericBodySemantics
attribute [local irreducible] famq famd current rankCoinBudget coins currentProgram
  boundedRankOneStringPre observedTicketCount fixedFamilyActualSampler
theorem _root_.P2Mf6bd8d28.h604 (fallback : Str) (D : Family) (word : Str) :
    acceptProb (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D) word=
      avg (fun tape : Fin (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount word)) → Bool =>
        acceptProb D (_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape) word))) := by
  have h := _Pgp word
  have htake (tape : Fin (_root_.Integration9_9.GaussianRankOnePre.rankCoinBudget.eval word.length) → Bool) :
      (List.ofFn tape).take (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount word))=
        List.ofFn (fun index => tape (Fin.castLE h index)) := by
    have ht := _Pgc tape 0 (Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount word)) (by omega)
    simpa only [List.drop_zero,Nat.zero_add,Fin.castLE] using ht
  calc
    acceptProb (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D) word=
        avg (fun tape : Fin (_root_.Integration9_9.GaussianRankOnePre.rankCoinBudget.eval word.length) → Bool =>
          acceptProb D (_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape) word))) :=
      _Pmo _root_.Integration9_9.GaussianRankOnePre.rankCoinBudget fallback D word
    _=avg (fun tape : Fin (_root_.Integration9_9.GaussianRankOnePre.rankCoinBudget.eval word.length) → Bool =>
        acceptProb D (_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn (fun index => tape (Fin.castLE h index))) word))) := by
      apply congrArg avg
      funext tape
      have hp := _Pl8 fallback (List.ofFn tape) word
      exact congrArg (acceptProb D) (hp.trans
        (congrArg (fun bits => _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair bits word)) (htake tape)))
    _=_ := _Pgg h
      (fun tape => acceptProb D (_root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn tape) word)))
open _root_.P2Mf6bd8d28 renaming h604 → _Pgs
theorem _root_.P2Mf6bd8d28.h599 (order : ℕ) (m : Polynomial ℕ) (fallback : Str) (D : Family) (hD : IsQPT D) :
    IsQPT (_root_.Integration9_9.GaussianRankOnePre.combinedFamily order m fallback D) := _Pja _ _ _ hD
open _root_.P2Mf6bd8d28 renaming h599 → _Pgn
theorem _root_.P2Mf6bd8d28.h597 (order : ℕ) (m : Polynomial ℕ) (fallback : Str) (D : Family) :
    CallsOnce (_root_.Integration9_9.GaussianRankOnePre.combinedFamily order m fallback D) D := _Pj9 _ _ _
open _root_.P2Mf6bd8d28 renaming h597 → _Pgl
theorem _root_.P2Mf6bd8d28.h600 (security count : ℕ) (ht : 0 < count)
    (table : Fin count → Matrix (Fin (famd security)) (Fin (famN security)) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    _root_.Integration9_9.LARRankOneMachine.observedTicketCount (encInput security (famPP security) (encTable table))=(famq security)^(famN security+count) := by
  simpa only [famPP] using _Pgt (_Pbt security) ht security (famσ security) table
open _root_.P2Mf6bd8d28 renaming h600 → _Pgo
theorem _root_.P2Mf6bd8d28.h596 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (m : Polynomial ℕ)
    (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (fallback : Str) (D : Family) (security count : ℕ) (ht : 0 < count)
    (table : Fin count → Matrix (Fin (famd security)) (Fin (famN security)) (ZMod (famq security)) ×
      (Fin (famd security) → ZMod (famq security))) :
    acceptProb (_root_.Integration9_9.GaussianRankOnePre.combinedFamily order m fallback D) (encInput security (famPP security) (encTable table))=
      avg (fun seeds : Fin count → Fin (m.eval security) → Bool =>
        acceptProb (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D) (encInput security (famPP security)
          (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security) seeds table)))) := by
  have hc : count*m.eval security+Nat.size ((famq security)^(famN security+count)) ≤
      (_root_.Integration9_9.GaussianRankOnePre.coins m).eval (encInput security (famPP security) (encTable table)).length := by
    simpa only [famPP] using _Pgj m (_Pbt security) ht security (famσ security) table
  have h := _Pj8 (_root_.Integration9_9.GaussianRankOnePre.currentProgram order m fallback) (_root_.Integration9_9.GaussianRankOnePre.coins m) D
    (encInput security (famPP security) (encTable table)) count (m.eval security)
    (Nat.size ((famq security)^(famN security+count))) hc
    (fun draws => _root_.Integration9_9.LARRankOneMachine.boundedRankOneStringPre fallback (encPair (List.ofFn draws.2)
      (encInput security (famPP security) (encTable (_root_.InfoLossLAR.WorstCase.affineObservedTable
        (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security) draws.1 table)))))
    (fun tape => current_value_clipped order data hdata m hbits fallback security count _ ht hc tape table)
  refine h.trans ?_
  apply congrArg avg
  funext seeds
  rw [_Pgs,_Pgo security count ht]
open _root_.P2Mf6bd8d28 renaming h596 → _Pgk
theorem _root_.P2Mf6bd8d28.h598 (order : ℕ) (data : _root_.CurrentAFT.BinaryFullResponseData.Data order)
    (hdata : _root_.CurrentAFT.BinaryFullResponseData.Correct data) (m : Polynomial ℕ)
    (hbits : ∀ security,(_root_.CurrentAFT.PublicBitTapes.current security).bits ≤ m.eval security)
    (fallback : Str) (D : Family) (security count : ℕ) (ht : 0 < count) :
    advLWE (_root_.Integration9_9.GaussianRankOnePre.combinedFamily order m fallback D) security (famPP security) (famq security) (famN security)
      (famd security) count (chiG (famq security) (famd security) (famσ security))=
      _root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv (q := famq security) (N := famN security)
        (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D) security (famPP security) count
        (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler order data m hbits security) (famσ security) (by unfold famσ famL; positivity) := by
  apply _P94
  exact _Pgk order data hdata m hbits fallback D security count ht
open _root_.P2Mf6bd8d28 renaming h598 → _Pgm
end Integration9_9.GaussianRankOnePre
open _root_.P2Mf6bd8d28 renaming h596 → _Pgk
open _root_.P2Mf6bd8d28 renaming h597 → _Pgl
open _root_.P2Mf6bd8d28 renaming h598 → _Pgm
open _root_.P2Mf6bd8d28 renaming h599 → _Pgn
open _root_.P2Mf6bd8d28 renaming h600 → _Pgo
open _root_.P2Mf6bd8d28 renaming h604 → _Pgs
end
end
open _root_.P2Mf6bd8d28 renaming h596 → _Pgk
open _root_.P2Mf6bd8d28 renaming h597 → _Pgl
open _root_.P2Mf6bd8d28 renaming h598 → _Pgm
open _root_.P2Mf6bd8d28 renaming h599 → _Pgn
open _root_.P2Mf6bd8d28 renaming h600 → _Pgo
open _root_.P2Mf6bd8d28 renaming h604 → _Pgs
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Integration9_9.GaussianRankOnePre
open InfoLossLAR.WorstCase
open QAlgorithms.Complexity AFT
open LARRankOneMachine RandomizedCircuit
attribute [local irreducible] rankCoinBudget famq famd
theorem _root_.P2Mf6bd8d28.h602 (D : Family) (fallback : Str) (q N d count : ℕ)
    [Fact q.Prime] [NeZero q] (hd : 0 < d) (hq : q ≤ d) (ht : 0 < count) (security width : ℕ) :
    advLAR D security (encB q++encB N++encB d++encB width) q N d 1 count
      (fun input => fun _ : Fin 1 => fT63 q d input) ≤
      (2*(q : ℝ))*advLWE (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D) security
        (encB q++encB N++encB d++encB width) q N d count
        (unifZeroFiber (fun input => fun _ : Fin 1 => fT63 q d input))+((q : ℝ)^N)⁻¹ := by
  cases d with
  | zero => omega
  | succ n =>
    let B := _root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D
    have htable (table : Fin count → Matrix (Fin (n+1)) (Fin N) (ZMod q) × (Fin (n+1) → ZMod q)) :
        acceptProb B (encInput security (encB q++encB N++encB (n+1)++encB width) (encTable table))=
          avg (fun tape : Fin (Nat.size (q^(N+count*1))) → Bool => acceptProb D
            (_root_.InfoLossLAR.WorstCase.boundedRankOnePre security (encB q++encB N++encB (n+1)++encB width) fallback q N (n+1) 1 count
              (_root_.InfoLossLAR.WorstCase.computableFixedVectorDirection q n) tape table)) := by
      let input := encInput security (encB q++encB N++encB (n+1)++encB width) (encTable table)
      have hb := _Pgp input
      change Nat.size (_root_.Integration9_9.LARRankOneMachine.observedTicketCount
        (encInput security (encB q++encB N++encB (n+1)++encB width) (encTable table))) ≤ _ at hb
      rw [_Plb ht security width table] at hb
      have hbits : Nat.size (q^(N+count*1)) ≤ _root_.Integration9_9.GaussianRankOnePre.rankCoinBudget.eval input.length := by
        simpa only [Nat.mul_one] using hb
      exact (_Pmo _root_.Integration9_9.GaussianRankOnePre.rankCoinBudget fallback D input).trans
        (_Pl6 D fallback q N n count hq ht security width _ hbits table)
    have hr := _Pmp B D fallback q N n count security width (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q (n+1)) htable
    have hi := _Pmd B D fallback q N n count security width htable
    have hw : (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw q (n+1)).weight=
        unifZeroFiber (fun input => fun _ : Fin 1 => fT63 q (n+1) input) := funext (_Pbs q (n+1))
    rw [←hw]
    unfold advLWE
    rw [hr,hi]
    exact _P99 D security _ fallback q N n count hq
open _root_.P2Mf6bd8d28 renaming h602 → _Pgq
theorem _root_.P2Mf6bd8d28.h603 (D : Family) (fallback : Str) (security count : ℕ)
    (ht : 0 < count) :
    famAdvLAR D security count ≤ (2*(famq security : ℝ))*
      advLWE (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily fallback D) security (famPP security) (famq security)
        (famN security) (famd security) count (unifZeroFiber (famLabel security))+
      ((famq security : ℝ)^famN security)⁻¹ := by
  haveI : Fact (famq security).Prime :=
    ⟨by unfold famq; exact (Nat.find_spec (Nat.exists_infinite_primes (2^16*famL security^64))).2⟩
  unfold famAdvLAR famPP famLabel
  exact _Pgq D fallback
    (famq security) (famN security) (famd security) count (_Pbt security)
    (_Pbw security) ht security (famσ security)
open _root_.P2Mf6bd8d28 renaming h603 → _Pgr
end Integration9_9.GaussianRankOnePre
open _root_.P2Mf6bd8d28 renaming h602 → _Pgq
open _root_.P2Mf6bd8d28 renaming h603 → _Pgr
end
end
open _root_.P2Mf6bd8d28 renaming h602 → _Pgq
open _root_.P2Mf6bd8d28 renaming h603 → _Pgr
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.UnitAffineProbability
open QAlgorithms.Complexity AFT
open scoped Classical
noncomputable section
theorem _root_.P2Mf6bd8d28.h316 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det) :
    _root_.InfoLossLAR.WorstCase.affineMatrixErrorLaw (N:=N) samp source=
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod (_root_.InfoLossLAR.WorstCase.affineSourceLaw samp source) := by
  let e (seed : Ω) := _root_.InfoLossLAR.WorstCase.UnitAffineProbability.leftMatrixEquiv (N:=N) (matModq q (samp seed).1) (hinv seed)
  let f (seed : Ω) := _root_.InfoLossLAR.WorstCase.UnitAffineProbability.affineVectorEquiv (samp seed).1 (samp seed).2 (hinv seed)
  have hfixed (seed : Ω) :
      ((_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod source).map
        (fun draw=>(matModq q (samp seed).1*draw.1,evalAffine (samp seed).1 (samp seed).2 draw.2))=
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod (source.map (f seed)) := by
    change ((_root_.AFT.FiniteDist.uniform _).prod source).map ((e seed).prodCongr (f seed))=_
    rw [_Pc,_root_.AFT.FiniteDist.uniform_map_equiv]
  unfold _root_.InfoLossLAR.WorstCase.affineMatrixErrorLaw
  simp_rw [hfixed]
  apply _root_.AFT.FiniteDist.ext
  rintro ⟨matrix,error⟩
  simp only [_root_.AFT.FiniteDist.mix_weight,_root_.AFT.FiniteDist.prod_weight,_root_.InfoLossLAR.WorstCase.affineSourceLaw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro seed hs
  simp only [f,_root_.InfoLossLAR.WorstCase.UnitAffineProbability.affineVectorEquiv,Equiv.coe_fn_mk]
  ring
open _root_.P2Mf6bd8d28 renaming h316 → _P8s
theorem _root_.P2Mf6bd8d28.h317 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det) :
    _root_.InfoLossLAR.WorstCase.affineMatrixErrorLaw (N:=N) samp (_root_.AFT.FiniteDist.uniform (Fin d → ZMod q))=
      (_root_.AFT.FiniteDist.uniform (Matrix (Fin d) (Fin N) (ZMod q))).prod (_root_.AFT.FiniteDist.uniform (Fin d → ZMod q)) := by
  exact _Pf (_root_.AFT.FiniteDist.uniform Ω)
    (fun seed=>_root_.InfoLossLAR.WorstCase.UnitAffineProbability.leftMatrixEquiv (matModq q (samp seed).1) (hinv seed))
    (fun seed=>_root_.InfoLossLAR.WorstCase.UnitAffineProbability.affineVectorEquiv (samp seed).1 (samp seed).2 (hinv seed))
open _root_.P2Mf6bd8d28 renaming h317 → _P8t
theorem _root_.P2Mf6bd8d28.h315 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det) (secret : Fin N → ZMod q) :
    _root_.InfoLossLAR.WorstCase.affineLWEBlockLaw samp source secret=_root_.InfoLossLAR.WorstCase.lweBlockLaw (_root_.InfoLossLAR.WorstCase.affineSourceLaw samp source) secret := by
  rw [_P9c,_P8s samp source hinv]
  rfl
open _root_.P2Mf6bd8d28 renaming h315 → _P8r
theorem _root_.P2Mf6bd8d28.h321 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det)
    (D : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    _root_.InfoLossLAR.WorstCase.affinePreprocessedReal (N:=N) D lam pp t samp source=
      prRealLWE D lam pp q N d t (transportLaw samp source.weight) := by
  rw [← show (_root_.InfoLossLAR.WorstCase.affineSourceLaw samp source).weight=transportLaw samp source.weight from funext (_P9f samp source)]
  rw [_Pdu]
  unfold _root_.InfoLossLAR.WorstCase.affinePreprocessedReal
  apply congrArg avg
  funext secret
  simp_rw [_P8r samp source hinv]
open _root_.P2Mf6bd8d28 renaming h321 → _P8x
theorem _root_.P2Mf6bd8d28.h320 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det)
    (D : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    _root_.InfoLossLAR.WorstCase.affinePreprocessedIdeal (q:=q) (N:=N) D lam pp t samp=prIdealLWE D lam pp q N d t := by
  rw [_Pdl]
  unfold _root_.InfoLossLAR.WorstCase.affinePreprocessedIdeal
  simp_rw [_P8t samp hinv]
open _root_.P2Mf6bd8d28 renaming h320 → _P8w
theorem _root_.P2Mf6bd8d28.h318 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (source : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det)
    (D : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    _root_.InfoLossLAR.WorstCase.affinePreprocessedAdv (N:=N) D lam pp t samp source=
      advLWE D lam pp q N d t (transportLaw samp source.weight) := by
  unfold _root_.InfoLossLAR.WorstCase.affinePreprocessedAdv advLWE
  rw [_P8x samp source hinv,_P8w (q:=q) (N:=N) samp hinv]
open _root_.P2Mf6bd8d28 renaming h318 → _P8u
theorem _root_.P2Mf6bd8d28.h319 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (source target : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det)
    (D : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    |_root_.InfoLossLAR.WorstCase.affinePreprocessedAdv (N:=N) D lam pp t samp source-advLWE D lam pp q N d t target.weight| ≤
      (t : ℝ)*sdist (transportLaw samp source.weight) target.weight := by
  rw [_P8u samp source hinv]
  have h:=_P9b D lam pp q N d t (_root_.InfoLossLAR.WorstCase.affineSourceLaw samp source) target
  simpa only [show (_root_.InfoLossLAR.WorstCase.affineSourceLaw samp source).weight=transportLaw samp source.weight from
    funext (_P9f samp source)] using h
open _root_.P2Mf6bd8d28 renaming h319 → _P8v
theorem _root_.P2Mf6bd8d28.h322 {q d N : ℕ} [NeZero q]
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (samp : Ω  →  Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
    (sigma : ℝ) (hsigma : 0 < sigma) (target : _root_.AFT.FiniteDist (Fin d → ZMod q))
    (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det)
    (D : Family) (lam : ℕ) (pp : Str) (t : ℕ) :
    |_root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv (q:=q) (N:=N) D lam pp t samp sigma hsigma-advLWE D lam pp q N d t target.weight| ≤
      (t : ℝ)*sdist (transportLaw samp (chiG q d sigma)) target.weight := by
  have hsource : (_root_.AFT.GaussianSource.residueGaussian d q sigma hsigma).weight=chiG q d sigma :=
    funext (_P4z q d sigma hsigma)
  simpa only [_root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv,hsource] using
    _P8v samp (_root_.AFT.GaussianSource.residueGaussian d q sigma hsigma) target hinv D lam pp t
open _root_.P2Mf6bd8d28 renaming h322 → _P8y
section Bounds
variable {q d N : ℕ} [NeZero q] {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable (samp : Ω → Matrix (Fin d) (Fin d) ℤ×(Fin d → ℤ))
variable (sigma : ℝ) (hsigma : 0 < sigma) (target : FiniteDist (Fin d → ZMod q))
variable (hinv : ∀ seed,IsUnit (matModq q (samp seed).1).det)
variable (D : Family) (lam : ℕ) (pp : Str) (t : ℕ)
include hinv
theorem _root_.P2Mf6bd8d28.h323 (delta : ℝ)
    (hclose : sdist (transportLaw samp (chiG q d sigma)) target.weight ≤ delta) :
    |_root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv (q:=q) (N:=N) D lam pp t samp sigma hsigma-advLWE D lam pp q N d t target.weight| ≤
      (t : ℝ)*delta :=
  (_P8y samp sigma hsigma target hinv D lam pp t).trans
    (mul_le_mul_of_nonneg_left hclose (Nat.cast_nonneg t))
open _root_.P2Mf6bd8d28 renaming h323 → _P8z
theorem _root_.P2Mf6bd8d28.h324 (delta : ℝ)
    (hclose : sdist (transportLaw samp (chiG q d sigma)) target.weight ≤ delta) :
    advLWE D lam pp q N d t target.weight ≤
      _root_.InfoLossLAR.WorstCase.gaussianPreprocessedAdv (q:=q) (N:=N) D lam pp t samp sigma hsigma+(t : ℝ)*delta := by
  have h := (abs_le.mp (_P8z (N:=N) samp sigma hsigma target hinv D lam pp t delta hclose)).1
  linarith
open _root_.P2Mf6bd8d28 renaming h324 → _P90
end Bounds
open _root_.P2Mf6bd8d28 renaming h323 → _P8z
open _root_.P2Mf6bd8d28 renaming h324 → _P90
end
open _root_.P2Mf6bd8d28 renaming h315 → _P8r
open _root_.P2Mf6bd8d28 renaming h316 → _P8s
open _root_.P2Mf6bd8d28 renaming h317 → _P8t
open _root_.P2Mf6bd8d28 renaming h318 → _P8u
open _root_.P2Mf6bd8d28 renaming h319 → _P8v
open _root_.P2Mf6bd8d28 renaming h320 → _P8w
open _root_.P2Mf6bd8d28 renaming h321 → _P8x
open _root_.P2Mf6bd8d28 renaming h322 → _P8y
open _root_.P2Mf6bd8d28 renaming h323 → _P8z
open _root_.P2Mf6bd8d28 renaming h324 → _P90
end InfoLossLAR.WorstCase.UnitAffineProbability
open _root_.P2Mf6bd8d28 renaming h315 → _P8r
open _root_.P2Mf6bd8d28 renaming h316 → _P8s
open _root_.P2Mf6bd8d28 renaming h317 → _P8t
open _root_.P2Mf6bd8d28 renaming h318 → _P8u
open _root_.P2Mf6bd8d28 renaming h319 → _P8v
open _root_.P2Mf6bd8d28 renaming h320 → _P8w
open _root_.P2Mf6bd8d28 renaming h321 → _P8x
open _root_.P2Mf6bd8d28 renaming h322 → _P8y
open _root_.P2Mf6bd8d28 renaming h323 → _P8z
open _root_.P2Mf6bd8d28 renaming h324 → _P90
end
open _root_.P2Mf6bd8d28 renaming h315 → _P8r
open _root_.P2Mf6bd8d28 renaming h316 → _P8s
open _root_.P2Mf6bd8d28 renaming h317 → _P8t
open _root_.P2Mf6bd8d28 renaming h318 → _P8u
open _root_.P2Mf6bd8d28 renaming h319 → _P8v
open _root_.P2Mf6bd8d28 renaming h320 → _P8w
open _root_.P2Mf6bd8d28 renaming h321 → _P8x
open _root_.P2Mf6bd8d28 renaming h322 → _P8y
open _root_.P2Mf6bd8d28 renaming h323 → _P8z
open _root_.P2Mf6bd8d28 renaming h324 → _P90
namespace InfoLossLAR.WorstCase.famN
end InfoLossLAR.WorstCase.famN
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InfoLossLAR.WorstCase
theorem _root_.P2Mf6bd8d28.h440
    (n q t a s c : ℕ) (hn : 2 ≤ n) (hcn : c+2 ≤ n) (hnq : n ≤ q)
    (hqa : q ≤ n^a) (hts : t ≤ n^s) (L G : ℝ)
    (hadv : (n : ℝ)^(-(c : ℝ)) ≤ L)
    (hcomparison : L ≤ (2*(q : ℝ))*G+
      (2*(q : ℝ))*(t : ℝ)*(n : ℝ)^(-((c+a+s+3 : ℕ) : ℝ))+((q : ℝ)^n)⁻¹) :
    (n : ℝ)^(-((c+a+2 : ℕ) : ℝ)) ≤ G := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hstep (order : ℕ) :
      2*(n : ℝ)^(-((order+1 : ℕ) : ℝ)) ≤ (n : ℝ)^(-(order : ℝ)) := by
    rw [_Pfh _ hnpos.le,_Pfh _ hnpos.le,pow_succ]
    have hh : 2/((n : ℝ)^order*n) ≤ 1/(n : ℝ)^order := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [pow_pos hnpos order]
    simpa only [div_eq_mul_inv,one_mul] using hh
  have herr : (2*(q : ℝ))*(t : ℝ)*(n : ℝ)^(-((c+a+s+3 : ℕ) : ℝ)) ≤
      (q : ℝ)*(t : ℝ)*(n : ℝ)^(-((c+a+s+2 : ℕ) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left (hstep (c+a+s+2))
      (by positivity : (0 : ℝ) ≤ (q : ℝ)*(t : ℝ))
    convert h using 1 <;> first | rfl | ring
  have hcomparison' : L ≤ (q : ℝ)*(2*G)+
      (q : ℝ)*(t : ℝ)*(n : ℝ)^(-((c+a+s+2 : ℕ) : ℝ))+((q : ℝ)^n)⁻¹ := by
    nlinarith
  have h := _Pc7 n q t a s c hn hcn hnq hqa hts L (2*G) hadv hcomparison'
  have hh := hstep (c+a+1)
  have heq : c+a+1+1=c+a+2 := by omega
  rw [heq] at hh
  linarith
open _root_.P2Mf6bd8d28 renaming h440 → _Pc8
theorem _root_.P2Mf6bd8d28.h427
    (D : QAlgorithms.Complexity.Family) (t : ℕ → ℕ) (htp : PolyBoundedFn t) (c : ℕ)
    (hcomparison : ∀ order : ℕ,1 ≤ order →
      ∃ B : QAlgorithms.Complexity.Family,IsQPT B ∧ CallsOnce B D ∧
        ∃ n₀ : ℕ,∀ n ≥ n₀,
          famAdvLAR D n (t n) ≤ (2*(famq n : ℝ))*
            advLWE B n (famPP n) (famq n) (famN n) (famd n) (t n)
              (chiG (famq n) (famd n) (famσ n))+
            (2*(famq n : ℝ))*(t n : ℝ)*(n : ℝ)^(-(order : ℝ))+
            ((famq n : ℝ)^famN n)⁻¹) :
    ∃ B : QAlgorithms.Complexity.Family,IsQPT B ∧ CallsOnce B D ∧ ∃ b n₀ : ℕ,
      ∀ n : ℕ,n₀ ≤ n → 1 ≤ n → (n : ℝ)^(-(c : ℝ)) ≤ famAdvLAR D n (t n) →
        (n : ℝ)^(-(b : ℝ)) ≤
          advLWE B n (famPP n) (famq n) (famN n) (famd n) (t n)
            (chiG (famq n) (famd n) (famσ n)) := by
  obtain ⟨a,q₀,hq⟩ := _Pde famq _Pbo
  obtain ⟨s,t₀,ht⟩ := _Pde t htp
  obtain ⟨B,hB,hOnce,n₀,hbound⟩ := hcomparison (c+a+s+3) (by omega)
  refine ⟨B,hB,hOnce,c+a+2,max 2 (max (c+2) (max q₀ (max t₀ n₀))),?_⟩
  intro n hlarge hnpositive hadv
  apply _Pc8 n (famq n) (t n) a s c
    (by omega) (by omega) (_Pfj n) (hq n (by omega)) (ht n (by omega))
    (famAdvLAR D n (t n)) _ hadv
  simpa only [famN] using hbound n (by omega)
open _root_.P2Mf6bd8d28 renaming h427 → _Pbv
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h427 → _Pbv
open _root_.P2Mf6bd8d28 renaming h440 → _Pc8
end
open _root_.P2Mf6bd8d28 renaming h427 → _Pbv
open _root_.P2Mf6bd8d28 renaming h440 → _Pc8
namespace InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler
end InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler
namespace InfoLossLAR.WorstCase.Integration.paddedActualSampler
end InfoLossLAR.WorstCase.Integration.paddedActualSampler
namespace InfoLossLAR.WorstCase.Integration.reindexAffine
end InfoLossLAR.WorstCase.Integration.reindexAffine
namespace InfoLossLAR.WorstCase.famInput
end InfoLossLAR.WorstCase.famInput
namespace InfoLossLAR.WorstCase.unifZeroFiber
end InfoLossLAR.WorstCase.unifZeroFiber
namespace Integration9_9.AFTToPlatformTheorem
end Integration9_9.AFTToPlatformTheorem
namespace Integration9_9.GaussianRankOnePre
end Integration9_9.GaussianRankOnePre
namespace Integration9_9.TM2NativePrime.primeFromParameter
end Integration9_9.TM2NativePrime.primeFromParameter
namespace Integration9_9.TM2NativePrime.primeFromSamplerRequest
end Integration9_9.TM2NativePrime.primeFromSamplerRequest
namespace Integration9_9.TM2NativeSamplerEncoding
end Integration9_9.TM2NativeSamplerEncoding
namespace Integration9_9.TM2NativeSamplerRequest
end Integration9_9.TM2NativeSamplerRequest
namespace Integration9_9.TM2NativeSamplerRequest.fields
end Integration9_9.TM2NativeSamplerRequest.fields
namespace Integration9_9.TM2NativeSamplerRequest.run
end Integration9_9.TM2NativeSamplerRequest.run
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open InfoLossLAR.WorstCase.Integration
open Integration9_9.GaussianRankOnePre
attribute [local irreducible] famq famd famAdvLAR
theorem _root_.P2Mf6bd8d28.h426
    (D : Family) (hD : IsQPT D) (t : ℕ → ℕ) (ht : ∀ n,1 ≤ t n)
    (accuracy : ℕ) (haccuracy : 1 ≤ accuracy) :
    ∃ B : Family,IsQPT B ∧ CallsOnce B D ∧ ∃ cutoff : ℕ,∀ n ≥ cutoff,
      famAdvLAR D n (t n) ≤ (2*(famq n : ℝ))*
        advLWE B n (famPP n) (famq n) (famN n) (famd n) (t n)
          (chiG (famq n) (famd n) (famσ n))+
        (2*(famq n : ℝ))*(t n : ℝ)*(n : ℝ)^(-(accuracy : ℝ))+
        ((famq n : ℝ)^famN n)⁻¹ := by
  obtain ⟨data,hdata,m,hbits,hunit,cutoff,hclose⟩ := _P4k accuracy
  refine ⟨_root_.Integration9_9.GaussianRankOnePre.combinedFamily (_root_.CurrentAFT.Parameters.calibrationOrder accuracy) m [] D,
    _Pgn _ m [] D hD,_Pgl _ m [] D,cutoff,?_⟩
  intro n hn
  have htpos : 0 < t n := by have := ht n; omega
  have hw : (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw (famq n) (famd n)).weight=unifZeroFiber (famLabel n) := by
    funext error
    exact _Pbs (famq n) (famd n) error
  have hsigma : 0 < (famσ n : ℝ) := by unfold famσ famL; positivity
  have htarget : sdist (transportLaw
      (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracy) data m hbits n)
      (chiG (famq n) (famd n) (famσ n)))
      (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw (famq n) (famd n)).weight ≤ (n : ℝ)^(-(accuracy : ℝ)) := by
    rw [hw]
    exact hclose n hn
  have htransport := _P90
    (N := famN n)
    (_root_.InfoLossLAR.WorstCase.Integration.fixedFamilyActualSampler (_root_.CurrentAFT.Parameters.calibrationOrder accuracy) data m hbits n)
    (famσ n) hsigma (_root_.InfoLossLAR.WorstCase.fixedZeroFiberLaw (famq n) (famd n)) (hunit n)
    (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily [] D) n (famPP n) (t n) ((n : ℝ)^(-(accuracy : ℝ))) htarget
  have hactual := _Pgm (_root_.CurrentAFT.Parameters.calibrationOrder accuracy)
    data hdata m hbits [] D n (t n) htpos
  rw [hw,←hactual] at htransport
  calc
    famAdvLAR D n (t n) ≤ (2*(famq n : ℝ))*
        advLWE (_root_.Integration9_9.GaussianRankOnePre.rankOneFamily [] D) n (famPP n) (famq n) (famN n) (famd n) (t n)
          (unifZeroFiber (famLabel n))+((famq n : ℝ)^famN n)⁻¹ :=
      _Pgr D [] n (t n) htpos
    _ ≤ (2*(famq n : ℝ))*(advLWE (_root_.Integration9_9.GaussianRankOnePre.combinedFamily (_root_.CurrentAFT.Parameters.calibrationOrder accuracy) m [] D)
        n (famPP n) (famq n) (famN n) (famd n) (t n) (chiG (famq n) (famd n) (famσ n))+
          (t n : ℝ)*(n : ℝ)^(-(accuracy : ℝ)))+((famq n : ℝ)^famN n)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left htransport
        (show (0 : ℝ) ≤ 2*(famq n : ℝ) by positivity)) le_rfl
    _ = _ := by ring
open _root_.P2Mf6bd8d28 renaming h426 → _Pbu
theorem _root_.InfoLossLAR.WorstCase.__p2m_proof_f6bd8d2813cfc8d188c3
    (_hAFT : AdmitsFixedOrderGaussianAFT famInput famq famd (fun _ => 1)
      (fun lam => (famσ lam : ℝ)) famLabel)
    (D : Family) (hD : IsQPT D)
    (t : ℕ → ℕ) (ht : ∀ lam,1 ≤ t lam) (htp : PolyBoundedFn t) (c : ℕ) :
    ∃ B : Family,IsQPT B ∧ CallsOnce B D ∧ ∃ b lam₀ : ℕ,
      ∀ lam : ℕ,lam₀ ≤ lam → 1 ≤ lam →
        (lam : ℝ)^(-(c : ℝ)) ≤ famAdvLAR D lam (t lam) →
        (lam : ℝ)^(-(b : ℝ)) ≤
          advLWE B lam (famPP lam) (famq lam) (famN lam) (famd lam) (t lam)
            (chiG (famq lam) (famd lam) (famσ lam)) :=
  _Pbv D t htp c
    (_Pbu D hD t ht)
end InfoLossLAR.WorstCase
open _root_.P2Mf6bd8d28 renaming h426 → _Pbu
end
end
open _root_.P2Mf6bd8d28 renaming h426 → _Pbu
theorem solution : (type_of% @_root_.InfoLossLAR.WorstCase.__p2m_proof_f6bd8d2813cfc8d188c3) := @_root_.InfoLossLAR.WorstCase.__p2m_proof_f6bd8d2813cfc8d188c3
