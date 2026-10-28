-- Prove2me | solution 1 for OAI.CriticalStrip.positiveLaw_inverseQuarterSum_growth_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:49:55.889103+00:00
-- url     : https://prove2.me/submissions/cde0c768-7ea0-4313-bb51-2bdab72a29ad

import Mathlib
import Definitions.Def_OAIQ042S004
import Theorems.Thm_OAI_CriticalStrip_laguerre_inverseQuarterSum_upper

section
-- module Solutions.OAIQ042_SS.StripMass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory


theorem omega_nonneg (x : ℝ) : 0 ≤ omega x := by
  unfold omega
  positivity

theorem omega_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < omega x := by
  have hx0 := hx.1
  have hh : 1 < (1 + x) / (2 * x) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * x)).2
    linarith [hx.2]
  have hh' : 1 < Real.sqrt ((1 + x) / (2 * x)) := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hh
  unfold omega
  exact mul_pos (by norm_num) (Real.sqrt_pos.2 (sub_pos.2 hh'))

theorem omega_le_rpow {x : ℝ} (hx : x ∈ Ioo 0 1) :
    omega x ≤ x ^ (-(1 / 4 : ℝ)) := by
  have hx0 := hx.1
  have ha : (1 + x) / (2 * x) ≤ 1 / x := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * x) hx.1).2
    nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)]
  have hb : Real.sqrt ((1 + x) / (2 * x)) - 1 ≤ Real.sqrt (1 / x) :=
    (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.sqrt_le_sqrt ha)
  calc
    omega x ≤ Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1) := by
      unfold omega
      nlinarith [Real.sqrt_nonneg (Real.sqrt ((1 + x) / (2 * x)) - 1)]
    _ ≤ Real.sqrt (Real.sqrt (1 / x)) := Real.sqrt_le_sqrt hb
    _ = x ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by positivity : 0 ≤ 1 / x)]
      norm_num only [one_div, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
      rw [Real.inv_rpow hx.1.le, Real.rpow_neg hx.1.le]

theorem measurable_omega : Measurable omega := by
  unfold omega
  fun_prop

theorem integrableOn_omega : IntegrableOn omega (Ioo 0 1) := by
  have hh : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num)
  apply hh.mono' measurable_omega.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (omega_nonneg x)] using omega_le_rpow hx

theorem pairKernel_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < pairKernel x y := by
  unfold pairKernel
  exact div_pos (sq_pos_of_pos (sub_pos.2 hxy)) (by linarith)

theorem pairKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ pairKernel x y := by
  unfold pairKernel
  positivity

theorem pairKernel_le_one {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    pairKernel x y ≤ 1 := by
  unfold pairKernel
  apply (div_le_one (by linarith [hx.1, hy.1] : 0 < y + x)).2
  have hxx : x ^ 2 ≤ x := by nlinarith [hx.1, hx.2]
  have hyy : y ^ 2 ≤ y := by nlinarith [hy.1, hy.2]
  nlinarith [mul_pos hx.1 hy.1]

theorem density_pos {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N) :
    0 < density N y := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => omega_pos (hy.2 i)
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    exact pairKernel_pos (hy.2 i).1 (hy.1 (Finset.mem_Ioi.1 hj))

theorem density_le_product {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N) :
    density N y ≤ ∏ i, omega (y i) := by
  have h0 : 0 ≤ ∏ i : Fin N, omega (y i) :=
    Finset.prod_nonneg fun _ _ => omega_nonneg _
  suffices hh : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, pairKernel (y i) (y j)) ≤ 1 by
    simpa only [density, mul_one] using mul_le_mul_of_nonneg_left hh h0
  apply Finset.prod_le_one
  · intro i _
    exact Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy.2 i).1.le (hy.2 j).1.le
  · intro i _
    exact Finset.prod_le_one
      (fun j _ => pairKernel_nonneg (hy.2 i).1.le (hy.2 j).1.le)
      (fun j _ => pairKernel_le_one (hy.2 i) (hy.2 j))

theorem measurable_density (N : ℕ) : Measurable (density N) := by
  unfold density pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ => measurable_omega.comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

theorem isOpen_orderedDomain (N : ℕ) : IsOpen (orderedDomain N) := by
  have heq : orderedDomain N =
      (⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {y | y i < y j}) ∩
      (⋂ i : Fin N, {y | y i ∈ Ioo (0 : ℝ) 1}) := by
    ext y
    simp only [orderedDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictMono]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

theorem integrableOn_density (N : ℕ) : IntegrableOn (density N) (orderedDomain N) := by
  have hi : IntegrableOn (fun y : Fin N → ℝ => ∏ i, omega (y i))
      (Set.univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1) := by
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun _ => integrableOn_omega
  have his : IntegrableOn (fun y : Fin N → ℝ => ∏ i, omega (y i)) (orderedDomain N) :=
    hi.mono_set (fun _ hy => fun i _ => hy.2 i)
  apply his.mono' (measurable_density N).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  simpa only [Real.norm_eq_abs, abs_of_pos (density_pos hy)] using density_le_product hy

 theorem orderedDomain_nonempty (N : ℕ) : (orderedDomain N).Nonempty := by
  refine ⟨fun i => ((i : ℕ) + 1 : ℝ) / (N + 1 : ℕ), ?_⟩
  constructor
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (N + 1 : ℕ))).2
    exact_mod_cast Nat.add_lt_add_right hij 1
  · intro i
    constructor
    · exact div_pos (by positivity) (by positivity)
    · apply (div_lt_one (by positivity : (0 : ℝ) < (N + 1 : ℕ))).2
      exact_mod_cast Nat.add_lt_add_right i.isLt 1

theorem normalizer_pos (N : ℕ) : 0 < normalizer N := by
  have hpos : 0 ≤ᵐ[volume.restrict (orderedDomain N)] density N := by
    filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
    exact (density_pos hy).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos (integrableOn_density N)).2
  have hs : orderedDomain N ⊆ Function.support (density N) :=
    fun y hy => (density_pos hy).ne'
  have hm := (isOpen_orderedDomain N).measure_pos volume (orderedDomain_nonempty N)
  calc
    0 < volume (orderedDomain N) := hm
    _ = (volume.restrict (orderedDomain N)) (orderedDomain N) :=
      (Measure.restrict_apply_self _ _).symm
    _ ≤ (volume.restrict (orderedDomain N)) (Function.support (density N)) := measure_mono hs

 
theorem integrableOn_power_omega (s : ℝ) (hs : -(3 / 4 : ℝ) < s) :
    IntegrableOn (fun x : ℝ => x ^ s * omega x) (Ioo 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (s - 1 / 4)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by linarith)
  apply hp.mono' ((measurable_id.pow_const s).mul measurable_omega).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 := hx.1
  change ‖x ^ s * omega x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx.1 s).le (omega_nonneg x))]
  calc
    x ^ s * omega x ≤ x ^ s * x ^ (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (omega_le_rpow hx) (Real.rpow_pos_of_pos hx.1 s).le
    _ = x ^ (s - 1 / 4) := by rw [← Real.rpow_add hx.1]; rfl

theorem integrableOn_coordinate_weight (N : ℕ) (i : Fin N) :
    IntegrableOn (fun y : Fin N → ℝ => (y i) ^ (-(1 / 2 : ℝ)) * density N y)
      (orderedDomain N) := by
  classical
  let f : Fin N → ℝ → ℝ := fun j t => (if j = i then t ^ (-(1 / 2 : ℝ)) else 1) * omega t
  have hf : ∀ j, IntegrableOn (f j) (Ioo 0 1) := by
    intro j
    by_cases hj : j = i
    · simpa only [f, hj, ite_true] using integrableOn_power_omega (-(1 / 2 : ℝ)) (by norm_num)
    · simpa only [f, hj, ite_false, one_mul] using integrableOn_omega
  have hp : IntegrableOn (fun y : Fin N → ℝ => (y i) ^ (-(1 / 2 : ℝ)) * ∏ j, omega (y j))
      (Set.univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1) := by
    have he : (fun y : Fin N → ℝ => (y i) ^ (-(1 / 2 : ℝ)) * ∏ j, omega (y j)) =
        (fun y => ∏ j, f j (y j)) := by
      funext y
      simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    rw [he]
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod hf
  have hps := hp.mono_set (show orderedDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1) from
    fun y hy i _ => hy.2 i)
  apply hps.mono' (((measurable_pi_apply i).pow_const _).mul (measurable_density N)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  have hi : 0 ≤ (y i) ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos (hy.2 i).1 _).le
  change ‖(y i) ^ (-(1 / 2 : ℝ)) * density N y‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hi (density_pos hy).le)]
  exact mul_le_mul_of_nonneg_left (density_le_product hy) hi


theorem integrableOn_inverseHalfSum_density (N : ℕ) :
    IntegrableOn (fun y => inverseHalfSum N y * density N y) (orderedDomain N) := by
  simp only [inverseHalfSum, Finset.sum_mul]
  exact integrable_finsetSum _ fun i _ => integrableOn_coordinate_weight N i

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

lemma top_wedge_determinant (n : ℕ) (v : Fin n → Vec n) :
    ExteriorAlgebra.ιMulti ℂ n v = (standardBasis n).det v • topWedge n := by
  have hf : ExteriorAlgebra.ιMulti ℂ n (M := Vec n) =
      ((standardBasis n).det).smulRight (topWedge n) := by
    apply (standardBasis n).ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change ExteriorAlgebra.ιMulti ℂ n ((standardBasis n) ∘ σ) =
      (((standardBasis n).det).smulRight (topWedge n)) ((standardBasis n) ∘ σ)
    simp [AlternatingMap.map_perm, topWedge, Module.Basis.det_self]
  exact DFunLike.congr_fun hf v

lemma generator_mem (n : ℕ) (i : Fin n) :
    generator n i ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ : Vec n →ₗ[ℂ] Grassmann n)) :=
  LinearMap.mem_range_self _ _

lemma twoForm_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    twoForm A ∈ ExteriorAlgebra.exteriorPower ℂ 2 (Vec n) := by
  unfold twoForm ExteriorAlgebra.exteriorPower
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  simpa only [pow_two] using Submodule.mul_mem_mul (generator_mem n i) (generator_mem n j)

lemma twoForm_pow_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    twoForm A ^ m ∈ ExteriorAlgebra.exteriorPower ℂ (2 * m) (Vec n) := by
  convert Submodule.pow_mem_pow _ (twoForm_mem A) m using 1
  all_goals try with_reducible_and_instances rfl
  exact pow_mul _ 2 m

lemma exteriorBasis_univ (n : ℕ) :
    (standardBasis n).ExteriorAlgebra Finset.univ = topWedge n := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin n)).card = n)]
  unfold ExteriorAlgebra.ιMulti_family topWedge
  congr 1
  funext i
  simp only [Function.comp_apply]
  apply congrArg (standardBasis n)
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change Finset.univ.orderEmbOfFin (by simp) i = i
  exact congr_fun (Finset.orderEmbOfFin_unique (by simp)
    (fun x : Fin n => Finset.mem_univ x) (fun _ _ h => h)).symm i

@[simp] lemma topCoord_topWedge (n : ℕ) : topCoord n (topWedge n) = 1 := by
  rw [← exteriorBasis_univ]
  simp [topCoord, Module.Basis.coord_apply]

lemma topCoord_wedge (n : ℕ) (v : Fin n → Vec n) :
    topCoord n (ExteriorAlgebra.ιMulti ℂ n v) = (standardBasis n).det v := by
  rw [top_wedge_determinant, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma homogeneous_eq_coord_topWedge (n : ℕ) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    x = topCoord n x • topWedge n := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    rw [topCoord_wedge, top_wedge_determinant]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add, add_smul, ← ihx, ← ihy]
  | smul r x hx ih =>
    rw [map_smul, smul_eq_mul, ← smul_smul, ← ih]

lemma topCoord_map (n : ℕ) (f : Vec n →ₗ[ℂ] Vec n) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord n (ExteriorAlgebra.map f x) = f.det * topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul]
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti, topCoord_wedge]
  have hd : (standardBasis n).det (f ∘ standardBasis n) = f.det := by
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hd, smul_eq_mul, mul_comm]

lemma generator_anticomm (n : ℕ) (i j : Fin n) :
    generator n i * generator n j = -(generator n j * generator n i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma sum_symmetric_offdiag {n : ℕ} {E : Type*} [AddCommGroup E]
    (F : Fin n → Fin n → E) (hF : ∀ i j, F i j = F j i)
    (hzero : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
  have hij (i j : Fin n) : F i j =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hzero]
    · simp [h, not_lt_of_gt h, hF i j]
  have hsum (i : Fin n) : (∑ j, if i < j then F i j else 0) =
      ∑ j ∈ Finset.Ioi i, F i j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  calc
    ∑ i, ∑ j, F i j =
        (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ i, ∑ j, if j < i then F j i else 0) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j
    _ = (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ j, ∑ i, if j < i then F j i else 0) := by
      rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
    _ = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
      simp only [hsum, two_nsmul]

lemma twoForm_full {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    twoForm A = (1 / 2 : ℂ) • ∑ i, ∑ j, A i j • (generator n i * generator n j) := by
  have hs := sum_symmetric_offdiag
    (fun i j => A i j • (generator n i * generator n j))
    (fun i j => by rw [hA i j, generator_anticomm n j i, neg_smul, smul_neg, neg_neg])
    (fun i => by simp [generator])
  rw [hs]
  change twoForm A = (1 / 2 : ℂ) • (2 • twoForm A)
  rw [← Nat.cast_smul_eq_nsmul ℂ 2, smul_smul]
  norm_num

lemma permMap_det (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permMap n σ).det = (Equiv.Perm.sign σ : ℂ) := by
  have he : permMap n σ ∘ standardBasis n = standardBasis n ∘ σ := by
    funext i
    exact permMap_basis n σ i
  have hd := Module.Basis.det_comp (standardBasis n) (permMap n σ) (standardBasis n)
  rw [he, AlternatingMap.map_perm, Module.Basis.det_self, mul_one] at hd
  simpa [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul] using hd.symm

lemma twoForm_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    ExteriorAlgebra.map (permMap n σ) (twoForm A) =
      twoForm (fun i j => A (σ.symm i) (σ.symm j)) := by
  rw [twoForm_full A hA, twoForm_full _ (fun i j => hA _ _)]
  simp only [map_smul, map_sum, map_mul, permMap_generator]
  congr 1
  apply Fintype.sum_equiv σ
  intro i
  simp only [Equiv.symm_apply_apply]
  apply Fintype.sum_equiv σ
  intro j
  simp

lemma pfaffian_perm (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    pfaffian n (fun i j => A (σ.symm i) (σ.symm j)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    (Equiv.Perm.sign σ : ℂ) * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_perm A hA σ, ← map_pow, topCoord_map n _ _ hhom, permMap_det]
  ring

lemma wedge_anticomm {n : ℕ} (u v : Vec n) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v =
      -(ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma wedge_commutes {n : ℕ} (u v : Vec n) (x : Grassmann n) :
    Commute (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι w =>
    change (_ * _) * _ = _ * (_ * _)
    calc
      _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) :=
        mul_assoc _ _ _
      _ = -(ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
        rw [wedge_anticomm v w, mul_neg]
      _ = -((ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ v) := by
        rw [mul_assoc]
      _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ v := by
        rw [wedge_anticomm u w, neg_mul, neg_neg]
      _ = _ := mul_assoc _ _ _
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

lemma wedge_sq_zero {n : ℕ} (u v : Vec n) :
    (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) ^ 2 = 0 := by
  rw [pow_two, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι ℂ v), wedge_anticomm v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]
  simp

lemma generator_expansion (n : ℕ) (u : Vec n) :
    (∑ i, u i • generator n i) = ExteriorAlgebra.ι ℂ u := by
  have h := congrArg (ExteriorAlgebra.ι ℂ) ((standardBasis n).sum_repr u)
  simpa [standardBasis, generator, map_sum, map_smul] using h

lemma pow_add_sq_zero {E : Type*} [Ring E] [Algebra ℂ E] (a b : E)
    (hab : Commute a b) (hb : b ^ 2 = 0) (m : ℕ) :
    (a + b) ^ (m + 1) = a ^ (m + 1) + (m + 1 : ℂ) • (a ^ m * b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (a + b), ih, add_mul, mul_add, mul_add,
      smul_mul_assoc, smul_mul_assoc]
    have hba : a ^ m * b * a = a ^ (m + 1) * b := by
      rw [mul_assoc, hab.eq.symm, ← mul_assoc, ← pow_succ]
    have hbb : a ^ m * b * b = 0 := by rw [mul_assoc, ← pow_two, hb, mul_zero]
    rw [hba, hbb, smul_zero, add_zero, ← pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    module

lemma high_degree_zero {n k : ℕ} (hk : n < k) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ k (Vec n)) : x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    apply AlternatingMap.map_linearDependent
    intro hv
    have h := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at h
    omega
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul r x hx ih => simp [ih]

lemma border_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (i j : Fin (n + 1)) :
    border A u j i = -border A u i j := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [border_last_last, border_last_old, border_old_last, border_old_old,
      neg_zero, neg_neg]
  exact hA _ _

lemma twoForm_border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    twoForm (border A u) = ExteriorAlgebra.map (embedMap n) (twoForm A) +
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
  rw [twoForm_full _ (border_skew A hA u), twoForm_full A hA]
  simp only [map_smul, map_sum, map_mul, embedMap_generator]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, border_old_old, border_old_last,
    border_last_old, border_last_last, zero_smul, add_zero, Finset.sum_add_distrib]
  have hu : (∑ i : Fin n, u i • generator (n + 1) i.castSucc) =
      ExteriorAlgebra.ι ℂ (embedMap n u) := by
    have h := congrArg (ExteriorAlgebra.map (embedMap n)) (generator_expansion n u)
    simpa using h
  have hp : (∑ i : Fin n, u i • (generator (n + 1) i.castSucc * generator (n + 1) (Fin.last n))) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hu, Finset.sum_mul]
    simp only [smul_mul_assoc]
  have hm : (∑ i : Fin n, -u i • (generator (n + 1) (Fin.last n) * generator (n + 1) i.castSucc)) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [generator_anticomm (n + 1) (Fin.last n), neg_smul, smul_neg, neg_neg]
  rw [hp, hm]
  module

lemma topWedge_snoc (n : ℕ) :
    topWedge (n + 1) = ExteriorAlgebra.map (embedMap n) (topWedge n) *
      generator (n + 1) (Fin.last n) := by
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti]
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Function.comp_apply, embedMap_basis, generator]

lemma topCoord_embed_mul_last {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 1) (ExteriorAlgebra.map (embedMap n) x * generator (n + 1) (Fin.last n)) =
      topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, smul_mul_assoc, ← topWedge_snoc,
    map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial
lemma pfaffian_border {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    pfaffian (n + 1) (border A u) = borderLinear A u := by
  have hm : (n + 1) / 2 = n / 2 + 1 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hz : twoForm A ^ (n / 2 + 1) = 0 :=
    high_degree_zero (by omega) _ (twoForm_pow_mem A (n / 2 + 1))
  have hcomm : Commute (ExteriorAlgebra.map (embedMap n) (twoForm A))
      (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n)) :=
    (wedge_commutes _ _ _).symm
  unfold pfaffian
  change topCoord (n + 1) _ / _ = _
  rw [twoForm_border A hA, hm, pow_add_sq_zero _ _ hcomm (wedge_sq_zero _ _) (n / 2),
    ← map_pow, hz, map_zero, zero_add, map_smul, smul_eq_mul]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm0 : (↑(n / 2) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n / 2)
  rw [mul_div_mul_left _ _ hm0]
  rfl

lemma topCoord_embed_twice {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 2)
      (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) x) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) =
      topCoord n x := by
  have ht : ExteriorAlgebra.map (embedMap (n + 1))
        (ExteriorAlgebra.map (embedMap n) (topWedge n)) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1))) =
      topWedge (n + 2) := by
    rw [← embedMap_generator (n + 1) (Fin.last n), ← mul_assoc, ← map_mul,
      ← topWedge_snoc, ← topWedge_snoc]
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul, smul_mul_assoc, ht, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma pfaffian_block_pair {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian (n + 2) (border (border A 0) (standardBasis (n + 1) (Fin.last n))) =
      pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have hm : (n + 1) / 2 = n / 2 := by obtain ⟨k, hk⟩ := hn; omega
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  rw [pfaffian_border hodd _ (border_skew A hA 0)]
  change topCoord (n + 2) _ / _ = _
  rw [twoForm_border A hA 0]
  simp only [map_zero, zero_mul, add_zero, embedMap_basis, hm, ← map_pow]
  change topCoord (n + 2)
    (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) (twoForm A ^ (n / 2))) *
      (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) / _ = _
  rw [topCoord_embed_twice _ hhom]
  rfl

lemma basis_last (n : ℕ) : standardBasis (n + 1) (Fin.last n) = Fin.snoc (fun _ => 0) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [standardBasis, Pi.basisFun_apply]

lemma pfaffian_zero_row (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (i : Fin n) (hrow : ∀ j, A i j = 0) :
    pfaffian n A = 0 := by
  let f : Vec n →ₗ[ℂ] Vec n :=
    (standardBasis n).constr ℂ (fun j => if j = i then 0 else standardBasis n j)
  have hf (j : Fin n) : f (standardBasis n j) = if j = i then 0 else standardBasis n j := by
    exact (standardBasis n).constr_basis ℂ _ j
  have hdet : f.det = 0 := by
    have hd := Module.Basis.det_comp (standardBasis n) f (standardBasis n)
    rw [Module.Basis.det_self, mul_one] at hd
    rw [← hd]
    exact (standardBasis n).det.map_coord_zero i (by simp [hf])
  have hcol (j : Fin n) : A j i = 0 := by rw [hA, hrow, neg_zero]
  have hform : ExteriorAlgebra.map f (twoForm A) = twoForm A := by
    unfold twoForm
    simp only [map_sum, map_smul, map_mul, generator, ExteriorAlgebra.map_apply_ι, hf]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hji : j = i
    · subst j
      simp [hrow]
    by_cases hki : k = i
    · subst k
      simp [hcol]
    simp [hji, hki]
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  have htop := topCoord_map n f (twoForm A ^ (n / 2)) hhom
  rw [map_pow, hform, hdet, zero_mul] at htop
  change topCoord n (twoForm A ^ (n / 2)) / _ = 0
  rw [htop, zero_div]

lemma pfaffian_block_extra {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (t : ℂ) :
    pfaffian (n + 2) (border (border A 0) (Fin.snoc u t)) = t * pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have he : Fin.snoc u t = Fin.snoc u 0 + t • standardBasis (n + 1) (Fin.last n) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [basis_last]
  have hz : borderLinear (border A 0) (Fin.snoc u 0) = 0 := by
    rw [← pfaffian_border hodd _ (border_skew A hA 0)]
    apply pfaffian_zero_row (n + 2) (hodd.add_one) _
      (border_skew _ (border_skew A hA 0) _) (Fin.last n).castSucc
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [pfaffian_border hodd _ (border_skew A hA 0), he, map_add, map_smul, hz, zero_add]
  rw [← pfaffian_border hodd _ (border_skew A hA 0), pfaffian_block_pair hn A hA, smul_eq_mul]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

lemma prod_Ioi_castSucc {n : ℕ} (f : Fin (n + 1) → ℂ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i.castSucc, f j) = (∏ j ∈ Finset.Ioi i, f j.castSucc) * f (Fin.last n) := by
  have h1 : Finset.Ioi i.castSucc = Finset.univ.filter (fun j => i.castSucc < j) := by ext; simp
  have h2 : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  rw [h1, h2, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp

lemma prod_Ioi_last {n : ℕ} (f : Fin (n + 1) → ℂ) :
    (∏ j ∈ Finset.Ioi (Fin.last n), f j) = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have h := Finset.mem_Ioi.mp hj
  have hj := j.isLt
  change n < j.val at h
  omega

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory


theorem fourthRoot_sum_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ (1 / 4 : ℝ) ≤ ∑ i ∈ s, (a i) ^ (1 / 4 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Real.rpow_add_le_add_rpow hai (Finset.sum_nonneg has) (by norm_num) (by norm_num)).trans
      (add_le_add_right (ih has) _)

theorem inverseQuarterSum_le_inverseHalfSum {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) :
    (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) ≤ inverseHalfSum N y := by
  refine (fourthRoot_sum_le_sum Finset.univ (fun i => (y i)⁻¹)
    (fun i _ => inv_nonneg.mpr (hy.2 i).1.le)).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [Real.inv_rpow (hy.2 i).1.le, ← Real.rpow_neg (hy.2 i).1.le]
  exact Real.rpow_le_rpow_of_exponent_ge (hy.2 i).1 (hy.2 i).2.le (by norm_num)

theorem integrableOn_inverseQuarterSum_density (N : ℕ) :
    IntegrableOn (fun y => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y : Fin N → ℝ => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) * density N y) :=
    ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).inv).pow_const _).mul (measurable_density N)
  apply (integrableOn_inverseHalfSum_density N).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg
    fun i _ => inv_nonneg.mpr (hy.2 i).1.le) _) (density_pos hy).le)]
  exact mul_le_mul_of_nonneg_right (inverseQuarterSum_le_inverseHalfSum hy) (density_pos hy).le

end


end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open scoped BigOperators
open Set MeasureTheory


theorem laguerreWeight_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < laguerreWeight a x :=
  mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

theorem measurable_laguerreWeight (a : ℝ) : Measurable (laguerreWeight a) := by
  unfold laguerreWeight
  fun_prop

theorem laguerreDensity_pos {N : ℕ} (a : ℝ) {r : Fin N → ℝ}
    (hr : r ∈ laguerreDomain N) : 0 < laguerreDensity N a r := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => laguerreWeight_pos a (hr.2 i)
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    exact pairKernel_pos (hr.2 i) (hr.1 (Finset.mem_Ioi.1 hj))

theorem measurable_laguerreDensity (N : ℕ) (a : ℝ) :
    Measurable (laguerreDensity N a) := by
  unfold laguerreDensity pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_laguerreWeight a).comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

theorem isOpen_laguerreDomain (N : ℕ) : IsOpen (laguerreDomain N) := by
  have heq : laguerreDomain N =
      (⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {r | r i < r j}) ∩
      (⋂ i : Fin N, {r | 0 < r i}) := by
    ext r
    simp only [laguerreDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictMono]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)

theorem laguerreDomain_nonempty (N : ℕ) : (laguerreDomain N).Nonempty := by
  refine ⟨fun i => (i : ℝ) + 1, ?_, ?_⟩
  · intro i j hij
    dsimp
    exact_mod_cast (show i.val + 1 < j.val + 1 by omega)
  · intro i
    positivity

theorem pairKernel_le_right {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y) :
    pairKernel x y ≤ y := by
  unfold pairKernel
  apply (div_le_iff₀ (by linarith : 0 < y + x)).2
  have hxx := mul_le_mul_of_nonneg_left hxy hx
  nlinarith [mul_nonneg hx hy.le]

theorem prod_pair_right (N : ℕ) (r : Fin N → ℝ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, r j) = ∏ j, r j ^ j.val := by
  classical
  calc
    (∏ i, ∏ j ∈ Finset.Ioi i, r j) =
        ∏ i, ∏ j : Fin N, if i < j then r j else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_filter]
      congr 1
      ext j
      simp
    _ = ∏ j : Fin N, ∏ i : Fin N, if i < j then r j else 1 := Finset.prod_comm
    _ = ∏ j : Fin N, r j ^ j.val := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← Finset.prod_filter]
      simp [show Finset.univ.filter (fun i : Fin N => i < j) = Finset.Iio j by ext; simp]

theorem laguerreDensity_le_product {N : ℕ} (a : ℝ) {r : Fin N → ℝ}
    (hr : r ∈ laguerreDomain N) :
    laguerreDensity N a r ≤ ∏ i, laguerreWeight (a + i.val) (r i) := by
  have hp : (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)) ≤
      ∏ i, ∏ j ∈ Finset.Ioi i, r j := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.prod_nonneg fun j _ => pairKernel_nonneg (hr.2 i).le (hr.2 j).le
    · intro i _
      apply Finset.prod_le_prod
      · intro j _
        exact pairKernel_nonneg (hr.2 i).le (hr.2 j).le
      · intro j hj
        exact pairKernel_le_right (hr.2 i).le (hr.2 j) (hr.1 (Finset.mem_Ioi.1 hj)).le
  rw [prod_pair_right] at hp
  calc
    laguerreDensity N a r ≤ (∏ i, laguerreWeight a (r i)) * ∏ i, r i ^ i.val :=
      mul_le_mul_of_nonneg_left hp (Finset.prod_nonneg fun i _ => (laguerreWeight_pos a (hr.2 i)).le)
    _ = ∏ i, laguerreWeight (a + i.val) (r i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      unfold laguerreWeight
      rw [show a + (i.val : ℝ) - 1 = (a - 1) + (i.val : ℝ) by ring,
        Real.rpow_add (hr.2 i), Real.rpow_natCast]
      ring

theorem integrableOn_laguerreWeight {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laguerreWeight a) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-x)) (Ioi 0)
  simpa only [mul_comm] using Real.GammaIntegral_convergent ha

theorem integral_laguerreWeight {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi 0, laguerreWeight a x) = Real.Gamma a := by
  simpa only [laguerreWeight, mul_comm] using (Real.Gamma_eq_integral ha).symm

theorem integrableOn_laguerre_product {N : ℕ} {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : Fin N → ℝ => ∏ i, laguerreWeight (a + i.val) (r i))
      (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) := by
  unfold IntegrableOn
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod fun i =>
    integrableOn_laguerreWeight (by positivity : 0 < a + (i.val : ℝ))

theorem integrableOn_laguerreDensity (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laguerreDensity N a) (laguerreDomain N) := by
  have hp := (integrableOn_laguerre_product (N := N) ha).mono_set
    (show laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) from
      fun r hr i _ => hr.2 i)
  apply hp.mono' (measurable_laguerreDensity N a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simpa only [Real.norm_eq_abs, abs_of_pos (laguerreDensity_pos a hr)] using
    laguerreDensity_le_product a hr

theorem laguerreNormalizer_pos (N : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < laguerreNormalizer N a := by
  have hpos : 0 ≤ᵐ[volume.restrict (laguerreDomain N)] laguerreDensity N a := by
    filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
    exact (laguerreDensity_pos a hr).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos (integrableOn_laguerreDensity N ha)).2
  have hs : laguerreDomain N ⊆ Function.support (laguerreDensity N a) :=
    fun r hr => (laguerreDensity_pos a hr).ne'
  calc
    0 < volume (laguerreDomain N) :=
      (isOpen_laguerreDomain N).measure_pos volume (laguerreDomain_nonempty N)
    _ = (volume.restrict (laguerreDomain N)) (laguerreDomain N) :=
      (Measure.restrict_apply_self _ _).symm
    _ ≤ (volume.restrict (laguerreDomain N)) (Function.support (laguerreDensity N a)) :=
      measure_mono hs



theorem integrableOn_laguerre_inverse_coordinate {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) :
    IntegrableOn (fun r => (r i) ^ (-p) * laguerreDensity N a r) (laguerreDomain N) := by
  classical
  let b : Fin N → ℝ := fun j => a + j.val - if j = i then p else 0
  have hb : ∀ j, 0 < b j := by
    intro j
    by_cases hj : j = i
    · simpa [b, hj] using sub_pos.mpr hp
    · simp only [b, hj, ite_false, sub_zero]
      positivity
  have heq : ∀ r : Fin N → ℝ, (∀ j, 0 < r j) →
      (r i) ^ (-p) * (∏ j, laguerreWeight (a + j.val) (r j)) =
        ∏ j, laguerreWeight (b j) (r j) := by
    intro r hr
    calc
      _ = (∏ j, if j = i then (r j) ^ (-p) else 1) *
          ∏ j, laguerreWeight (a + j.val) (r j) := by simp
      _ = ∏ j, (if j = i then (r j) ^ (-p) else 1) *
          laguerreWeight (a + j.val) (r j) := (Finset.prod_mul_distrib).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hj : j = i
        · simp only [b, hj, ite_true, laguerreWeight]
          rw [show a + (i.val : ℝ) - p - 1 = -p + (a + i.val - 1) by ring,
            Real.rpow_add (hr i)]
          ring
        · simp [b, hj]
  have hi : IntegrableOn (fun r : Fin N → ℝ => ∏ j, laguerreWeight (b j) (r j))
      (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) := by
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun j => integrableOn_laguerreWeight (hb j)
  have hs : laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) :=
    fun r hr j _ => hr.2 j
  apply (hi.mono_set hs).mono'
    (((measurable_pi_apply i).pow_const _).mul (measurable_laguerreDensity N a)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  change ‖(r i) ^ (-p) * laguerreDensity N a r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hr.2 i) _).le
    (laguerreDensity_pos a hr).le),
    ← heq r hr.2]
  exact mul_le_mul_of_nonneg_left (laguerreDensity_le_product a hr)
    (Real.rpow_pos_of_pos (hr.2 i) _).le

 

theorem integrableOn_laguerre_inverseQuarterSum {N : ℕ} {a : ℝ} (ha : 1 / 4 < a) :
    IntegrableOn (fun r : Fin N → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ) *
      laguerreDensity N a r) (laguerreDomain N) := by
  have hi : IntegrableOn (fun r : Fin N → ℝ =>
      ∑ i, (r i) ^ (-(1 / 4 : ℝ)) * laguerreDensity N a r) (laguerreDomain N) :=
    integrable_finsetSum _ fun i _ =>
      integrableOn_laguerre_inverse_coordinate (by linarith : 0 < a) i
        (by
          have h : (0 : ℝ) ≤ i.val := by positivity
          linarith)
  have hm : Measurable (fun r : Fin N → ℝ =>
      (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ) * laguerreDensity N a r) := by
    apply Measurable.mul _ (measurable_laguerreDensity N a)
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  have hh : 0 ≤ ∑ i : Fin N, (r i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr.2 i)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hh _)
    (laguerreDensity_pos a hr).le), ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (laguerreDensity_pos a hr).le
  calc
    (∑ i : Fin N, (r i)⁻¹) ^ (1 / 4 : ℝ) ≤ ∑ i : Fin N, ((r i)⁻¹) ^ (1 / 4 : ℝ) :=
      fourthRoot_sum_le_sum _ _ (fun i _ => (inv_pos.mpr (hr.2 i)).le)
    _ = ∑ i : Fin N, (r i) ^ (-(1 / 4 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.inv_rpow (hr.2 i).le, Real.rpow_neg (hr.2 i).le]



theorem laguerreLaw_isProbabilityMeasure (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (laguerreLaw N a) := by
  refine ⟨?_⟩
  rw [laguerreLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_laguerreDensity N ha)]
  · exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (laguerreNormalizer_pos N ha)).ne'
      ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
    exact (laguerreDensity_pos a hr).le

theorem ae_laguerreDomain (N : ℕ) (a : ℝ) :
    ∀ᵐ r ∂laguerreLaw N a, r ∈ laguerreDomain N := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff (measurable_laguerreDensity N a).ennreal_ofReal).2
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  exact fun _ => hr

theorem integral_laguerreLaw (N : ℕ) {a : ℝ} (ha : 0 < a) (f : (Fin N → ℝ) → ℝ) :
    (∫ r, f r ∂laguerreLaw N a) = laguerreExpectation N a f := by
  rw [laguerreLaw, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_laguerreDensity N a).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (laguerreNormalizer_pos N ha).le,
    smul_eq_mul, laguerreExpectation, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  rw [ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le, mul_comm]

theorem integrable_laguerreLaw {N : ℕ} {a : ℝ} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ}
    (hf : IntegrableOn (fun r => f r * laguerreDensity N a r) (laguerreDomain N)) :
    Integrable f (laguerreLaw N a) := by
  apply Integrable.smul_measure (c := (ENNReal.ofReal (laguerreNormalizer N a))⁻¹) ?_
    (by simp [laguerreNormalizer_pos N ha])
  apply (integrable_withDensity_iff_integrable_smul' (measurable_laguerreDensity N a).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  apply hf.congr
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le, mul_comm]

theorem integrable_laguerreLaw_inverseQuarterSum {N : ℕ} {a : ℝ} (ha : 1 / 4 < a) :
    Integrable (fun r : Fin N → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ)) (laguerreLaw N a) :=
  integrable_laguerreLaw (by linarith) (integrableOn_laguerre_inverseQuarterSum ha)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory





theorem pairProduct_snoc {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      pairKernel ((Fin.snoc r x : Fin (n + 1) → ℝ) i) ((Fin.snoc r x : Fin (n + 1) → ℝ) j)) =
      (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)) * ∏ i, pairKernel (r i) x := by
  classical
  have he {m : ℕ} (s : Fin m → ℝ) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, pairKernel (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then pairKernel (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp [Fin.prod_univ_castSucc, Finset.prod_mul_distrib, not_lt.mpr (Fin.le_last _)]

theorem laguerreDensity_snoc {n : ℕ} (a x : ℝ) (r : Fin n → ℝ) :
    laguerreDensity (n + 1) a (Fin.snoc r x) =
      laguerreWeight a x * laguerreDensity n a r * ∏ i, pairKernel (r i) x := by
  unfold laguerreDensity
  rw [pairProduct_snoc]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem laguerreDomain_of_snoc {n : ℕ} {x : ℝ} {r : Fin n → ℝ}
    (hr : Fin.snoc r x ∈ laguerreDomain (n + 1)) :
    r ∈ laguerreDomain n ∧ 0 < x ∧ ∀ i, r i < x := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    simpa using hr.1 (show i.castSucc < j.castSucc from hij)
  · intro i
    simpa using hr.2 i.castSucc
  · simpa using hr.2 (Fin.last n)
  · intro i
    simpa using hr.1 (Fin.castSucc_lt_last i)

theorem laguerreDensity_snoc_le {n : ℕ} (a : ℝ) {x : ℝ} {r : Fin n → ℝ}
    (hr : Fin.snoc r x ∈ laguerreDomain (n + 1)) :
    laguerreDensity (n + 1) a (Fin.snoc r x) ≤
      laguerreWeight (a + n) x * laguerreDensity n a r := by
  obtain ⟨hrt, hx, hrx⟩ := laguerreDomain_of_snoc hr
  rw [laguerreDensity_snoc]
  have hp : (∏ i, pairKernel (r i) x) ≤ x ^ n := by
    calc
      _ ≤ ∏ _ : Fin n, x := Finset.prod_le_prod
        (fun i _ => pairKernel_nonneg (hrt.2 i).le hx.le)
        (fun i _ => pairKernel_le_right (hrt.2 i).le hx (hrx i).le)
      _ = _ := by simp
  calc
    _ ≤ (laguerreWeight a x * laguerreDensity n a r) * x ^ n :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (laguerreWeight_pos a hx).le (laguerreDensity_pos a hrt).le)
    _ = laguerreWeight (a + n) x * laguerreDensity n a r := by
      unfold laguerreWeight
      rw [show a + (n : ℝ) - 1 = a - 1 + n by ring, Real.rpow_add hx, Real.rpow_natCast]
      ring

theorem integral_fin_snoc_eq (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ r, f r) = ∫ p : ℝ × (Fin n → ℝ), f (Fin.snoc p.2 p.1) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last, Fin.succAbove_last, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm).integral_comp' f

theorem integrable_fin_snoc {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.snoc p.2 p.1)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last, Fin.succAbove_last, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm).integrable_comp_of_integrable hf

theorem laguerreLaw_measureReal (N : ℕ) {a : ℝ} (ha : 0 < a)
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) :
    (laguerreLaw N a).real s =
      (∫ r in laguerreDomain N ∩ s, laguerreDensity N a r) / laguerreNormalizer N a := by
  rw [← integral_indicator_one hs, integral_laguerreLaw N ha]
  unfold laguerreExpectation
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hs]

theorem laguerreLargestIntegral_le (n : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    (∫ r in laguerreDomain (n + 1) ∩ {r | h < r (Fin.last n)}, laguerreDensity (n + 1) a r) ≤
      (∫ x in Ioi h, laguerreWeight (a + n) x) * laguerreNormalizer n a := by
  let S : Set (Fin (n + 1) → ℝ) := laguerreDomain (n + 1) ∩ {r | h < r (Fin.last n)}
  have hm : MeasurableSet S := (isOpen_laguerreDomain _).measurableSet.inter
    (measurableSet_lt measurable_const (measurable_pi_apply _))
  let f : ℝ → ℝ := (Ioi h).indicator (laguerreWeight (a + n))
  let g : (Fin n → ℝ) → ℝ := (laguerreDomain n).indicator (laguerreDensity n a)
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_laguerreWeight (show 0 < a + (n : ℝ) by positivity)).mono_set (Ioi_subset_Ioi hh))
  have hgi : Integrable g := (integrable_indicator_iff (isOpen_laguerreDomain n).measurableSet).2
    (integrableOn_laguerreDensity n ha)
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : h < x
    · rw [show f x = laguerreWeight (a + n) x from indicator_of_mem hx _]
      exact (laguerreWeight_pos _ (hh.trans_lt hx)).le
    · exact le_of_eq (indicator_of_notMem hx _).symm
  have hgn : ∀ r, 0 ≤ g r := by
    intro r
    by_cases hr : r ∈ laguerreDomain n
    · rw [show g r = laguerreDensity n a r from indicator_of_mem hr _]
      exact (laguerreDensity_pos a hr).le
    · exact le_of_eq (indicator_of_notMem hr _).symm
  have hsi : Integrable (S.indicator (laguerreDensity (n + 1) a)) :=
    (integrable_indicator_iff hm).2 ((integrableOn_laguerreDensity _ ha).mono_set inter_subset_left)
  have hb (p : ℝ × (Fin n → ℝ)) : S.indicator (laguerreDensity (n + 1) a) (Fin.snoc p.2 p.1) ≤
      f p.1 * g p.2 := by
    by_cases hp : Fin.snoc p.2 p.1 ∈ S
    · have htail := (laguerreDomain_of_snoc hp.1).1
      have hx : p.1 ∈ Ioi h := by simpa using hp.2
      simpa only [f, g, indicator_of_mem hp, indicator_of_mem hx, indicator_of_mem htail] using
        laguerreDensity_snoc_le a hp.1
    · rw [indicator_of_notMem hp]
      exact mul_nonneg (hfn _) (hgn _)
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), S.indicator (laguerreDensity (n + 1) a) (Fin.snoc p.2 p.1) := by
      rw [← integral_indicator hm, integral_fin_snoc_eq]
    _ ≤ ∫ p : ℝ × (Fin n → ℝ), f p.1 * g p.2 :=
      integral_mono (integrable_fin_snoc hsi) (hfi.mul_prod hgi) hb
    _ = (∫ x, f x) * ∫ r, g r := integral_prod_mul f g
    _ = _ := by
      simp only [f, g, integral_indicator measurableSet_Ioi,
        integral_indicator (isOpen_laguerreDomain n).measurableSet, laguerreNormalizer]

 
theorem laguerreLaw_max_tail_le (n : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    (laguerreLaw (n + 1) a).real {r | h < r (Fin.last n)} ≤
      (laguerreNormalizer n a / laguerreNormalizer (n + 1) a) *
        ∫ x in Ioi h, laguerreWeight (a + n) x := by
  rw [laguerreLaw_measureReal _ ha (measurableSet_lt measurable_const (measurable_pi_apply _))]
  have H := div_le_div_of_nonneg_right (laguerreLargestIntegral_le n ha hh)
    (laguerreNormalizer_pos (n + 1) ha).le
  exact H.trans_eq (by ring)

 

theorem laguerreWeight_tail_exp_bound {b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h) :
    (∫ x in Ioi h, laguerreWeight b x) ≤
      Real.exp (-h / 2) * (2 ^ b * Real.Gamma b) := by
  let f : ℝ → ℝ := fun x => x ^ (b - 1) * Real.exp (-(1 / 2 * x))
  have hfi : IntegrableOn f (Ioi 0) := by
    simpa only [f, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := b - 1) (p := 1) (b := 1 / 2)
        (by linarith) (by norm_num) (by norm_num))
  have hfn : ∀ x ∈ Ioi 0, 0 ≤ f x := fun x hx =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_nonneg _)
  have ht : ∫ x in Ioi h, laguerreWeight b x ≤ Real.exp (-h / 2) * ∫ x in Ioi h, f x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      ((integrableOn_laguerreWeight hb).mono_set (Ioi_subset_Ioi hh))
      ((hfi.mono_set (Ioi_subset_Ioi hh)).const_mul _) measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := lt_of_le_of_lt hh hx
    have he : Real.exp (-x / 2) ≤ Real.exp (-h / 2) :=
      Real.exp_le_exp.2 (by have : h < x := hx; linarith)
    calc
      laguerreWeight b x = Real.exp (-x / 2) * f x := by
        simp only [laguerreWeight, f]
        conv_lhs => rw [show -x = -(x / 2) + -(1 / 2 * x) by ring, Real.exp_add]
        simp only [neg_div, mul_left_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right he (hfn x hxpos)
  calc
    _ ≤ Real.exp (-h / 2) * ∫ x in Ioi h, f x := ht
    _ ≤ Real.exp (-h / 2) * ∫ x in Ioi 0, f x := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply setIntegral_mono_set hfi _ (Filter.Eventually.of_forall (Ioi_subset_Ioi hh))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hfn x hx
    _ = _ := by
      congr 1
      simpa only [f, one_div_div, div_one] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi hb (by norm_num : (0 : ℝ) < 1 / 2))

 

theorem laguerreLaw_max_tail_exp_bound (n : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    (laguerreLaw (n + 1) a).real {r | h < r (Fin.last n)} ≤
      (laguerreNormalizer n a / laguerreNormalizer (n + 1) a) *
        (Real.exp (-h / 2) * (2 ^ (a + (n : ℝ)) * Real.Gamma (a + n))) := by
  apply (laguerreLaw_max_tail_le n ha hh).trans
  exact mul_le_mul_of_nonneg_left
    (laguerreWeight_tail_exp_bound (by positivity) hh)
    (div_nonneg (laguerreNormalizer_pos n ha).le (laguerreNormalizer_pos (n + 1) ha).le)

end

noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter


lemma orderedPairKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ orderedPairKernel x y := by
  unfold orderedPairKernel
  positivity

lemma orderedPairKernel_eq {x y : ℝ} (hxy : x ≤ y) :
    orderedPairKernel x y = pairKernel x y := by
  simp [orderedPairKernel, pairKernel, max_eq_left (sub_nonneg.mpr hxy)]

lemma orderedPairKernel_eq_zero {x y : ℝ} (hxy : y ≤ x) :
    orderedPairKernel x y = 0 := by
  simp [orderedPairKernel, max_eq_right (sub_nonpos.mpr hxy)]

 

lemma pairKernel_cross {a b s t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbs : b < s) (hst : s ≤ t) :
    pairKernel a t * pairKernel b s ≤ pairKernel a s * pairKernel b t := by
  have hb : 0 < b := ha.trans_le hab
  have has : a < s := hab.trans_lt hbs
  have hat : a < t := has.trans_le hst
  have hbt : b < t := hbs.trans_le hst
  have hu : (s - b) / (t - b) ≤ (s - a) / (t - a) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hbt) (sub_pos.mpr hat)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hst)]
  have hv : (t + b) / (s + b) ≤ (t + a) / (s + a) := by
    rw [div_le_div_iff₀ (by linarith : 0 < s + b) (by linarith : 0 < s + a)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hst)]
  have hr : pairKernel b s / pairKernel b t ≤ pairKernel a s / pairKernel a t := by
    have he {u : ℝ} (hu0 : 0 < u) (hus : u < s) :
        pairKernel u s / pairKernel u t = ((s - u) / (t - u)) ^ 2 * ((t + u) / (s + u)) := by
      unfold pairKernel
      field_simp
    rw [he hb hbs, he ha has]
    refine mul_le_mul ((sq_le_sq₀ (by positivity) (by positivity)).2 hu) hv ?_ (sq_nonneg _)
    exact div_nonneg (by linarith) (by linarith)
  have hr' := (div_le_div_iff₀ (pairKernel_pos hb hbt) (pairKernel_pos ha hat)).1 hr
  nlinarith

lemma orderedPairKernel_logSupermodular {a b s t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (ht : 0 < t) :
    orderedPairKernel a s * orderedPairKernel b t ≤
      orderedPairKernel (min a b) (min s t) * orderedPairKernel (max a b) (max s t) := by
  wlog hab : a ≤ b generalizing a b s t
  · have h := this hb ha ht hs (le_of_not_ge hab)
    simpa [min_comm, max_comm, mul_comm] using h
  by_cases hst : s ≤ t
  · simp [min_eq_left hab, max_eq_right hab, min_eq_left hst, max_eq_right hst]
  have hts : t ≤ s := le_of_not_ge hst
  rw [min_eq_left hab, max_eq_right hab, min_eq_right hts, max_eq_left hts]
  by_cases hbt : b < t
  · rw [orderedPairKernel_eq (hab.trans (hbt.le.trans hts)), orderedPairKernel_eq hbt.le,
      orderedPairKernel_eq (hab.trans hbt.le), orderedPairKernel_eq (hbt.le.trans hts)]
    exact pairKernel_cross ha hab hbt hts
  · rw [orderedPairKernel_eq_zero (le_of_not_gt hbt), mul_zero]
    exact mul_nonneg (orderedPairKernel_nonneg ha.le ht.le)
      (orderedPairKernel_nonneg hb.le hs.le)

 

lemma product_coordinate_modular {ι α : Type*} [Fintype ι] [LinearOrder α]
    (w : ι → α → ℝ) (x y : ι → α) :
    (∏ i, w i (x i)) * (∏ i, w i (y i)) =
      (∏ i, w i ((x ⊓ y) i)) * (∏ i, w i ((x ⊔ y) i)) := by
  classical
  simp only [← Finset.prod_mul_distrib, Pi.inf_apply, Pi.sup_apply]
  apply Finset.prod_congr rfl
  intro i _
  obtain h | h := le_total (x i) (y i)
  · simp [inf_eq_left.mpr h, sup_eq_right.mpr h]
  · simp [inf_eq_right.mpr h, sup_eq_left.mpr h, mul_comm]

 

lemma association_finite_product {ι α : Type*} [Fintype ι] [Fintype α] [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)]
    (h f g : (ι → α) → ℝ) (hh : 0 ≤ h) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hfm : Monotone f) (hgm : Monotone g)
    (hhm : ∀ x y, h x * h y ≤ h (x ⊓ y) * h (x ⊔ y)) :
    (∫ x, h x * f x ∂Measure.pi ν) * (∫ x, h x * g x ∂Measure.pi ν) ≤
      (∫ x, h x ∂Measure.pi ν) * (∫ x, h x * (f x * g x) ∂Measure.pi ν) := by
  classical
  let m : (ι → α) → ℝ := fun x => ∏ i, (ν i).real {x i}
  have hm : ∀ x, (Measure.pi ν).real {x} = m x := by
    intro x
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, m]
  have hmn : 0 ≤ m := fun x => Finset.prod_nonneg fun i _ => measureReal_nonneg
  have hmod (x y : ι → α) : m x * m y = m (x ⊓ y) * m (x ⊔ y) :=
    product_coordinate_modular (fun i z => (ν i).real {z}) x y
  have hmh : ∀ x y, (m x * h x) * (m y * h y) ≤
      (m (x ⊓ y) * h (x ⊓ y)) * (m (x ⊔ y) * h (x ⊔ y)) := by
    intro x y
    rw [mul_mul_mul_comm, mul_mul_mul_comm (m (x ⊓ y)), hmod]
    exact mul_le_mul_of_nonneg_left (hhm x y) (mul_nonneg (hmn _) (hmn _))
  simp only [integral_fintype (Integrable.of_finite), hm, smul_eq_mul]
  simpa only [mul_assoc] using
    fkg f g (fun x => m x * h x) (fun x => mul_nonneg (hmn x) (hh x))
      hf hg hfm hgm hmh



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PositiveAssociation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
lemma association_sampled {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (q : SimpleFunc ℝ ℝ) {I : Set ℝ}
    (hqI : ∀ x, q x ∈ I) (h f g : (ι → ℝ) → ℝ)
    (hh : ∀ x ∈ coordinateBox ι I, 0 ≤ h x)
    (hf : ∀ x ∈ coordinateBox ι I, 0 ≤ f x)
    (hg : ∀ x ∈ coordinateBox ι I, 0 ≤ g x)
    (hfm : MonotoneOn f (coordinateBox ι I))
    (hgm : MonotoneOn g (coordinateBox ι I))
    (hhm : ∀ x ∈ coordinateBox ι I, ∀ y ∈ coordinateBox ι I,
      h x * h y ≤ h (x ⊓ y) * h (x ⊔ y)) :
    (∫ x, h (fun i => q (x i)) * f (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h (fun i => q (x i)) * g (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) ≤
    (∫ x, h (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h (fun i => q (x i)) * (f (fun i => q (x i)) * g (fun i => q (x i)))
        ∂Measure.pi (fun _ : ι => μ)) := by
  classical
  let A := ↥q.range
  let Q : ℝ → A := fun x => ⟨q x, q.mem_range_self x⟩
  let e : (ι → A) → (ι → ℝ) := fun x i => x i
  have hQ : Measurable Q := q.measurable.subtype_mk
  let ν : Measure A := μ.map Q
  have heI (x : ι → A) : e x ∈ coordinateBox ι I := by
    intro i
    obtain ⟨z, hz⟩ := SimpleFunc.mem_range.mp (x i).property
    change (x i).val ∈ I
    rw [← hz]
    exact hqI z
  have hint (k : (ι → ℝ) → ℝ) :
      (∫ x, k (fun i => q (x i)) ∂Measure.pi (fun _ : ι => μ)) =
        ∫ x : ι → A, k (e x) ∂Measure.pi (fun _ : ι => ν) := by
    rw [← Measure.pi_map_pi (fun _ : ι => hQ.aemeasurable)]
    symm
    apply integral_map (Measurable.of_eval (fun i => hQ.comp (measurable_pi_apply i))).aemeasurable
    exact (measurable_of_countable _).aestronglyMeasurable
  rw [hint (fun x => h x * f x), hint (fun x => h x * g x), hint h,
    hint (fun x => h x * (f x * g x))]
  apply association_finite_product (fun _ : ι => ν) (fun x => h (e x)) (fun x => f (e x))
    (fun x => g (e x)) (fun x => hh _ (heI x)) (fun x => hf _ (heI x)) (fun x => hg _ (heI x))
  · intro x y hxy
    exact hfm (heI x) (heI y) (fun i => hxy i)
  · intro x y hxy
    exact hgm (heI x) (heI y) (fun i => hxy i)
  · intro x y
    exact hhm _ (heI x) _ (heI y)

lemma measurable_sampled {ι : Type*} [Fintype ι]
    (q : SimpleFunc ℝ ℝ) (k : (ι → ℝ) → ℝ) :
    Measurable (fun x : ι → ℝ => k (fun i => q (x i))) := by
  let Q : ℝ → ↥q.range := fun x => ⟨q x, q.mem_range_self x⟩
  have hQ : Measurable Q := q.measurable.subtype_mk
  exact (measurable_of_countable (fun x : ι → ↥q.range => k (fun i => x i))).comp
    (Measurable.of_eval (fun i => hQ.comp (measurable_pi_apply i)))

 

lemma integral_tendsto_quantization {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {I : Set ℝ} (hIc : IsCompact I)
    {y₀ : ℝ} (h₀ : y₀ ∈ I) (hμI : ∀ᵐ x ∂μ, x ∈ I)
    (k : (ι → ℝ) → ℝ) (hk : ContinuousOn k (coordinateBox ι I)) :
    Tendsto (fun n => ∫ x : ι → ℝ,
      k (fun i => SimpleFunc.approxOn id measurable_id I y₀ h₀ n (x i))
        ∂Measure.pi (fun _ : ι => μ)) atTop
      (nhds (∫ x, k x ∂Measure.pi (fun _ : ι => μ))) := by
  let q : ℕ → SimpleFunc ℝ ℝ := SimpleFunc.approxOn id measurable_id I y₀ h₀
  have hqI (n : ℕ) (x : ι → ℝ) : (fun i => q n (x i)) ∈ coordinateBox ι I :=
    fun i => SimpleFunc.approxOn_mem measurable_id h₀ n (x i)
  have hB : IsCompact (coordinateBox ι I) := isCompact_pi_infinite fun _ => hIc
  obtain ⟨b, hb⟩ := hB.exists_bound_of_continuousOn hk
  have hμB : ∀ᵐ x ∂Measure.pi (fun _ : ι => μ), x ∈ coordinateBox ι I :=
    ae_all_iff.mpr (fun i => (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).ae hμI)
  apply tendsto_integral_of_dominated_convergence (fun _ => b)
    (fun n => (measurable_sampled (q n) k).aestronglyMeasurable) (integrable_const b)
    (fun n => Eventually.of_forall (fun x => hb _ (hqI n x)))
  filter_upwards [hμB] with x hx
  apply (hk x hx).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_pi_nhds.mpr (fun i => ?_), Eventually.of_forall (fun n => hqI n x)⟩
  exact SimpleFunc.tendsto_approxOn measurable_id h₀ (subset_closure (hx i))

 

lemma association_compact_product {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] {I : Set ℝ} (hIc : IsCompact I)
    {y₀ : ℝ} (h₀ : y₀ ∈ I) (hμI : ∀ᵐ x ∂μ, x ∈ I)
    (h f g : (ι → ℝ) → ℝ)
    (hhc : ContinuousOn h (coordinateBox ι I))
    (hfc : ContinuousOn f (coordinateBox ι I))
    (hgc : ContinuousOn g (coordinateBox ι I))
    (hh : ∀ x ∈ coordinateBox ι I, 0 ≤ h x)
    (hf : ∀ x ∈ coordinateBox ι I, 0 ≤ f x)
    (hg : ∀ x ∈ coordinateBox ι I, 0 ≤ g x)
    (hfm : MonotoneOn f (coordinateBox ι I))
    (hgm : MonotoneOn g (coordinateBox ι I))
    (hhm : ∀ x ∈ coordinateBox ι I, ∀ y ∈ coordinateBox ι I,
      h x * h y ≤ h (x ⊓ y) * h (x ⊔ y)) :
    (∫ x, h x * f x ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h x * g x ∂Measure.pi (fun _ : ι => μ)) ≤
    (∫ x, h x ∂Measure.pi (fun _ : ι => μ)) *
      (∫ x, h x * (f x * g x) ∂Measure.pi (fun _ : ι => μ)) := by
  apply le_of_tendsto_of_tendsto
    ((integral_tendsto_quantization μ hIc h₀ hμI _ (hhc.mul hfc)).mul
      (integral_tendsto_quantization μ hIc h₀ hμI _ (hhc.mul hgc)))
    ((integral_tendsto_quantization μ hIc h₀ hμI h hhc).mul
      (integral_tendsto_quantization μ hIc h₀ hμI _ (hhc.mul (hfc.mul hgc))))
  exact Eventually.of_forall (fun n => association_sampled μ
    (SimpleFunc.approxOn id measurable_id I y₀ h₀ n)
    (SimpleFunc.approxOn_mem measurable_id h₀ n) h f g hh hf hg hfm hgm hhm)



lemma orderedProductDensity_nonneg {N : ℕ} {I : Set ℝ}
    (hI : I ⊆ Ioi 0) (w : Fin N → ℝ → ℝ) (hw : ∀ i x, x ∈ I → 0 ≤ w i x)
    {x : Fin N → ℝ} (hx : x ∈ coordinateBox (Fin N) I) :
    0 ≤ orderedProductDensity N w x := by
  unfold orderedProductDensity
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw i _ (hx i)))
    (Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ =>
      orderedPairKernel_nonneg (hI (hx i)).le (hI (hx j)).le)))

lemma continuousOn_orderedProductDensity {N : ℕ} {I : Set ℝ}
    (hI : I ⊆ Ioi 0) (w : Fin N → ℝ → ℝ) (hw : ∀ i, ContinuousOn (w i) I) :
    ContinuousOn (orderedProductDensity N w) (coordinateBox (Fin N) I) := by
  unfold orderedProductDensity
  apply ContinuousOn.mul
  · apply continuousOn_finsetProd
    intro i _
    exact (hw i).comp (continuous_apply i).continuousOn (fun x hx => hx i)
  · apply continuousOn_finsetProd
    intro i _
    apply continuousOn_finsetProd
    intro j _
    unfold orderedPairKernel
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact ne_of_gt (add_pos (hI (hx j)) (hI (hx i)))

lemma orderedProductDensity_logSupermodular {N : ℕ} {I : Set ℝ}
    (hI : I ⊆ Ioi 0) (w : Fin N → ℝ → ℝ) (hw : ∀ i x, x ∈ I → 0 ≤ w i x)
    {x y : Fin N → ℝ} (hx : x ∈ coordinateBox (Fin N) I) (hy : y ∈ coordinateBox (Fin N) I) :
    orderedProductDensity N w x * orderedProductDensity N w y ≤
      orderedProductDensity N w (x ⊓ y) * orderedProductDensity N w (x ⊔ y) := by
  have hp :
      (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (x i) (x j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (y i) (y j)) ≤
      (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel ((x ⊓ y) i) ((x ⊓ y) j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel ((x ⊔ y) i) ((x ⊔ y) j)) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.prod_nonneg fun j _ => mul_nonneg
        (orderedPairKernel_nonneg (hI (hx i)).le (hI (hx j)).le)
        (orderedPairKernel_nonneg (hI (hy i)).le (hI (hy j)).le)
    · intro i _
      apply Finset.prod_le_prod
      · intro j _
        exact mul_nonneg
          (orderedPairKernel_nonneg (hI (hx i)).le (hI (hx j)).le)
          (orderedPairKernel_nonneg (hI (hy i)).le (hI (hy j)).le)
      · intro j _
        exact orderedPairKernel_logSupermodular
          (hI (hx i)) (hI (hy i)) (hI (hx j)) (hI (hy j))
  unfold orderedProductDensity
  rw [mul_mul_mul_comm, mul_mul_mul_comm (∏ i, w i ((x ⊓ y) i)),
    ← product_coordinate_modular]
  exact mul_le_mul_of_nonneg_left hp (mul_nonneg
    (Finset.prod_nonneg (fun i _ => hw i _ (hx i)))
    (Finset.prod_nonneg (fun i _ => hw i _ (hy i))))

lemma orderedProductDensity_eq {N : ℕ} (w : Fin N → ℝ → ℝ)
    {x : Fin N → ℝ} (hx : StrictMono x) :
    orderedProductDensity N w x =
      (∏ i, w i (x i)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (x i) (x j) := by
  unfold orderedProductDensity
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  exact orderedPairKernel_eq (hx (Finset.mem_Ioi.mp hj)).le

lemma orderedProductDensity_eq_zero {N : ℕ} (w : Fin N → ℝ → ℝ)
    {x : Fin N → ℝ} (hx : ¬ StrictMono x) : orderedProductDensity N w x = 0 := by
  classical
  unfold StrictMono at hx
  push Not at hx
  obtain ⟨i, j, hij, hji⟩ := hx
  have hz : (∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (x i) (x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_Ioi.mpr hij) (orderedPairKernel_eq_zero hji))
  simp [orderedProductDensity, hz]

 

theorem ordered_density_association_compact {N : ℕ} {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Icc l u))
    (hw : ∀ i x, x ∈ Icc l u → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Icc l u)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Icc l u)))
    (hf : ∀ x ∈ coordinateBox (Fin N) (Icc l u), 0 ≤ f x)
    (hg : ∀ x ∈ coordinateBox (Fin N) (Icc l u), 0 ≤ g x)
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Icc l u)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Icc l u))) :
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * f x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * g x) ≤
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * (f x * g x)) := by
  have hI : Icc l u ⊆ Ioi (0 : ℝ) := fun _ hx => hl.trans_le hx.1
  have hb : coordinateBox (Fin N) (Icc l u) = Set.univ.pi (fun _ : Fin N => Icc l u) := by
    ext x
    simp [coordinateBox, Pi.le_def, forall_and]
  have h := association_compact_product (volume.restrict (Icc l u)) isCompact_Icc
    (left_mem_Icc.mpr hlu) (ae_restrict_mem measurableSet_Icc) (orderedProductDensity N w) f g
    (continuousOn_orderedProductDensity hI w hwc) hfc hgc
    (fun _ hx => orderedProductDensity_nonneg hI w hw hx) hf hg hfm hgm
    (fun _ hx _ hy => orderedProductDensity_logSupermodular hI w hw hx hy)
  simpa only [hb, volume_pi, Measure.restrict_pi_pi] using h

 

lemma weighted_covariance_shift {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h f g : α → ℝ) (hh : Integrable h μ) (hf : Integrable (fun x => h x * f x) μ)
    (hg : Integrable (fun x => h x * g x) μ)
    (hfg : Integrable (fun x => h x * (f x * g x)) μ) (b c : ℝ) :
    (∫ x, h x * (f x + b) ∂μ) * (∫ x, h x * (g x + c) ∂μ) -
        (∫ x, h x ∂μ) * (∫ x, h x * ((f x + b) * (g x + c)) ∂μ) =
      (∫ x, h x * f x ∂μ) * (∫ x, h x * g x ∂μ) -
        (∫ x, h x ∂μ) * (∫ x, h x * (f x * g x) ∂μ) := by
  have hf' : (∫ x, h x * (f x + b) ∂μ) = (∫ x, h x * f x ∂μ) + b * ∫ x, h x ∂μ := by
    simp_rw [mul_add]
    rw [integral_add hf (hh.mul_const b), integral_mul_const, mul_comm _ b]
  have hg' : (∫ x, h x * (g x + c) ∂μ) = (∫ x, h x * g x ∂μ) + c * ∫ x, h x ∂μ := by
    simp_rw [mul_add]
    rw [integral_add hg (hh.mul_const c), integral_mul_const, mul_comm _ c]
  have hfg' : (∫ x, h x * ((f x + b) * (g x + c)) ∂μ) =
      (∫ x, h x * (f x * g x) ∂μ) + c * (∫ x, h x * f x ∂μ) +
        b * (∫ x, h x * g x ∂μ) + b * c * (∫ x, h x ∂μ) := by
    simp_rw [show ∀ x, h x * ((f x + b) * (g x + c)) =
      h x * (f x * g x) + c * (h x * f x) + b * (h x * g x) + (b * c) * h x by
        intro x; ring]
    have hi₁ : Integrable (fun x => h x * (f x * g x) + c * (h x * f x)) μ :=
      hfg.add (hf.const_mul c)
    have hi₂ : Integrable (fun x => h x * (f x * g x) + c * (h x * f x) + b * (h x * g x)) μ :=
      hi₁.add (hg.const_mul b)
    rw [integral_add hi₂ (hh.const_mul (b * c)),
      integral_add hi₁ (hg.const_mul b), integral_add hfg (hf.const_mul c)]
    simp only [integral_const_mul]
  rw [hf', hg', hfg']
  ring

 

theorem ordered_density_covariance_compact {N : ℕ} {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Icc l u))
    (hw : ∀ i x, x ∈ Icc l u → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Icc l u)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Icc l u)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Icc l u)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Icc l u))) :
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * f x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * g x) ≤
    (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x) *
      (∫ x in coordinateBox (Fin N) (Icc l u), orderedProductDensity N w x * (f x * g x)) := by
  have hB : IsCompact (coordinateBox (Fin N) (Icc l u)) := isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨b, hb⟩ := hB.exists_bound_of_continuousOn hfc
  obtain ⟨c, hc⟩ := hB.exists_bound_of_continuousOn hgc
  have hh : ContinuousOn (orderedProductDensity N w) (coordinateBox (Fin N) (Icc l u)) :=
    continuousOn_orderedProductDensity (fun _ hx => hl.trans_le hx.1) w hwc
  have h := ordered_density_association_compact hl hlu w hwc hw
    (fun x => f x + b) (fun x => g x + c) (hfc.add continuousOn_const) (hgc.add continuousOn_const)
    (fun x hx => by have h := (abs_le.mp (hb x hx)).1; linarith)
    (fun x hx => by have h := (abs_le.mp (hc x hx)).1; linarith)
    (fun x hx y hy hxy => add_le_add (hfm hx hy hxy) le_rfl)
    (fun x hx y hy hxy => add_le_add (hgm hx hy hxy) le_rfl)
  have he := weighted_covariance_shift (volume.restrict (coordinateBox (Fin N) (Icc l u)))
    (orderedProductDensity N w) f g (hh.integrableOn_compact hB)
    ((hh.mul hfc).integrableOn_compact hB) ((hh.mul hgc).integrableOn_compact hB)
    ((hh.mul (hfc.mul hgc)).integrableOn_compact hB) b c
  linarith



lemma isOpen_strictMono_coordinates (N : ℕ) : IsOpen {x : Fin N → ℝ | StrictMono x} := by
  have heq : {x : Fin N → ℝ | StrictMono x} =
      ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {x | x i < x j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, StrictMono]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)

lemma coordinateBox_eq_pi {ι : Type*} (I : Set ℝ) :
    coordinateBox ι I = Set.univ.pi (fun _ : ι => I) := by
  ext x
  simp [coordinateBox]

lemma measurableSet_coordinateBox {ι : Type*} [Countable ι] {I : Set ℝ}
    (hI : MeasurableSet I) : MeasurableSet (coordinateBox ι I) := by
  have he : coordinateBox ι I = ⋂ i : ι, (fun x : ι → ℝ => x i) ⁻¹' I := by
    ext x
    simp [coordinateBox]
  rw [he]
  exact MeasurableSet.iInter fun i : ι => hI.preimage (measurable_pi_apply i)

lemma orderedProductDensity_indicator (N : ℕ) (w : Fin N → ℝ → ℝ) :
    orderedProductDensity N w = {x : Fin N → ℝ | StrictMono x}.indicator (rawProductDensity N w) := by
  classical
  funext x
  by_cases hx : StrictMono x
  · simp only [Set.indicator_of_mem (show x ∈ {x : Fin N → ℝ | StrictMono x} from hx)]
    exact orderedProductDensity_eq w hx
  · simp only [Set.indicator_of_notMem (show x ∉ {x : Fin N → ℝ | StrictMono x} from hx)]
    exact orderedProductDensity_eq_zero w hx

lemma orderedProductDensity_mul_indicator (N : ℕ) (w : Fin N → ℝ → ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (fun x => orderedProductDensity N w x * f x) =
      {x : Fin N → ℝ | StrictMono x}.indicator (fun x => rawProductDensity N w x * f x) := by
  rw [orderedProductDensity_indicator]
  funext x
  by_cases hx : StrictMono x <;> simp [hx]

lemma orderedChamber_eq_inter (N : ℕ) (I : Set ℝ) :
    orderedChamber N I = {x : Fin N → ℝ | StrictMono x} ∩ coordinateBox (Fin N) I := rfl

lemma integral_orderedProductDensity_mul {N : ℕ} (I : Set ℝ) (w : Fin N → ℝ → ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ x in coordinateBox (Fin N) I, orderedProductDensity N w x * f x) =
      ∫ x in orderedChamber N I, rawProductDensity N w x * f x := by
  rw [orderedProductDensity_mul_indicator, setIntegral_indicator (isOpen_strictMono_coordinates N).measurableSet,
    orderedChamber_eq_inter, inter_comm]

lemma integrable_orderedProductDensity_mul_iff {N : ℕ} (I : Set ℝ) (w : Fin N → ℝ → ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    IntegrableOn (fun x => orderedProductDensity N w x * f x) (coordinateBox (Fin N) I) ↔
      IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N I) := by
  rw [orderedProductDensity_mul_indicator,
    integrableOn_indicator_iff (isOpen_strictMono_coordinates N).measurableSet]
  rfl

lemma coordinateBox_mono {ι : Type*} {I J : Set ℝ} (hIJ : I ⊆ J) :
    coordinateBox ι I ⊆ coordinateBox ι J := fun _ hx i => hIJ (hx i)

lemma coordinateBox_iUnion_of_monotone {ι : Type*} [Fintype ι] {s : ℕ → Set ℝ}
    (hs : Monotone s) :
    (⋃ n, coordinateBox ι (s n)) = coordinateBox ι (⋃ n, s n) := by
  simp only [coordinateBox_eq_pi]
  exact Set.iUnion_pi_of_monotone (Set.toFinite Set.univ) (fun _ _ => hs)

 

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DensityExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
theorem ordered_density_covariance_exhaustion {N : ℕ} {I : Set ℝ} (l u : ℕ → ℝ)
    (hl : ∀ n, 0 < l n) (hlu : ∀ n, l n ≤ u n)
    (hm : Monotone (fun n => Icc (l n) (u n)))
    (hc : (⋃ n, Icc (l n) (u n)) = I)
    (w : Fin N → ℝ → ℝ) (hwc : ∀ i, ContinuousOn (w i) I)
    (hw : ∀ i x, x ∈ I → 0 ≤ w i x)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) I))
    (hgc : ContinuousOn g (coordinateBox (Fin N) I))
    (hfm : MonotoneOn f (coordinateBox (Fin N) I))
    (hgm : MonotoneOn g (coordinateBox (Fin N) I))
    (hh : IntegrableOn (rawProductDensity N w) (orderedChamber N I))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N I))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (orderedChamber N I))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (orderedChamber N I)) :
    (∫ x in orderedChamber N I, rawProductDensity N w x * f x) *
      (∫ x in orderedChamber N I, rawProductDensity N w x * g x) ≤
    (∫ x in orderedChamber N I, rawProductDensity N w x) *
      (∫ x in orderedChamber N I, rawProductDensity N w x * (f x * g x)) := by
  have hsub (n : ℕ) : Icc (l n) (u n) ⊆ I := hc ▸ subset_iUnion (fun n => Icc (l n) (u n)) n
  have hB : (⋃ n, coordinateBox (Fin N) (Icc (l n) (u n))) = coordinateBox (Fin N) I := by
    rw [coordinateBox_iUnion_of_monotone hm, hc]
  have ht (F : (Fin N → ℝ) → ℝ)
      (hi : IntegrableOn (fun x => rawProductDensity N w x * F x) (orderedChamber N I)) :
      Tendsto (fun n => ∫ x in coordinateBox (Fin N) (Icc (l n) (u n)),
        orderedProductDensity N w x * F x) atTop
        (nhds (∫ x in orderedChamber N I, rawProductDensity N w x * F x)) := by
    rw [← integral_orderedProductDensity_mul]
    have hi' := (integrable_orderedProductDensity_mul_iff I w F).2 hi
    rw [← hB] at hi' ⊢
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_coordinateBox measurableSet_Icc)
      (fun i j hij => coordinateBox_mono (hm hij)) hi'
  have hht : Tendsto (fun n => ∫ x in coordinateBox (Fin N) (Icc (l n) (u n)),
        orderedProductDensity N w x) atTop
        (nhds (∫ x in orderedChamber N I, rawProductDensity N w x)) := by
    simpa using ht (fun _ => 1) (by simpa using hh)
  exact le_of_tendsto_of_tendsto ((ht f hf).mul (ht g hg))
    (hht.mul (ht (fun x => f x * g x) hfg))
    (Eventually.of_forall fun n => ordered_density_covariance_compact (hl n) (hlu n) w
      (fun i => (hwc i).mono (hsub n)) (fun i x hx => hw i x (hsub n hx)) f g
      (hfc.mono (coordinateBox_mono (hsub n))) (hgc.mono (coordinateBox_mono (hsub n)))
      (hfm.mono (coordinateBox_mono (hsub n))) (hgm.mono (coordinateBox_mono (hsub n))))

lemma boundedWindow_mono {R : ℝ} (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => Icc (R / (n + 3 : ℝ)) (R - R / (n + 3 : ℝ))) := by
  intro n m hnm x hx
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  have hd : R / (m + 3 : ℝ) ≤ R / (n + 3 : ℝ) :=
    div_le_div_of_nonneg_left hR (by positivity) (by linarith)
  exact ⟨hd.trans hx.1, by linarith [hx.2]⟩

lemma boundedWindow_cover {R : ℝ} (hR : 0 < R) :
    (⋃ n : ℕ, Icc (R / (n + 3 : ℝ)) (R - R / (n + 3 : ℝ))) = Ioo 0 R := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hp : 0 < R / (n + 3 : ℝ) := by positivity
    exact ⟨hp.trans_le hn.1, by linarith [hn.2]⟩
  · rintro ⟨hx, hxr⟩
    have heps : 0 < min x (R - x) / R := div_pos (lt_min hx (sub_pos.mpr hxr)) hR
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt heps
    have hsmall : R / (n + 3 : ℝ) < min x (R - x) := by
      have hnd : R / (n + 3 : ℝ) ≤ R / (n + 1 : ℝ) :=
        div_le_div_of_nonneg_left hR.le (by positivity) (by norm_num)
      rw [lt_div_iff₀ hR] at hn
      have hn' : R / (n + 1 : ℝ) < min x (R - x) := by simpa [div_eq_mul_inv, mul_comm] using hn
      exact hnd.trans_lt hn'
    exact mem_iUnion.mpr ⟨n, (hsmall.trans_le (min_le_left _ _)).le,
      by have h := hsmall.trans_le (min_le_right _ _); linarith⟩

 

theorem ordered_density_covariance_Ioo {N : ℕ} {R : ℝ} (hR : 0 < R)
    (w : Fin N → ℝ → ℝ) (hwc : ∀ i, ContinuousOn (w i) (Ioo 0 R))
    (hw : ∀ i x, x ∈ Ioo 0 R → 0 ≤ w i x) (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 R)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 R)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 R)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 R)))
    (hh : IntegrableOn (rawProductDensity N w) (orderedChamber N (Ioo 0 R)))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N (Ioo 0 R)))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (orderedChamber N (Ioo 0 R)))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (orderedChamber N (Ioo 0 R))) :
    (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * f x) *
      (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * g x) ≤
    (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x) *
      (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * (f x * g x)) := by
  apply ordered_density_covariance_exhaustion (fun n => R / (n + 3 : ℝ))
      (fun n => R - R / (n + 3 : ℝ)) (fun _ => by positivity) (fun n => ?_)
      (boundedWindow_mono hR.le) (boundedWindow_cover hR)
      w hwc hw f g hfc hgc hfm hgm hh hf hg hfg
  have hd : R / (n + 3 : ℝ) ≤ R / 2 :=
    div_le_div_of_nonneg_left hR.le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

lemma weighted_covariance_normalize {Af Ag Afg Z : ℝ} (hZ : 0 < Z)
    (h : Af * Ag ≤ Z * Afg) : (Af / Z) * (Ag / Z) ≤ Afg / Z := by
  apply (le_div_iff₀ hZ).2
  calc
    (Af / Z * (Ag / Z)) * Z = (Af * Ag) / Z := by field_simp
    _ ≤ Afg := (div_le_iff₀ hZ).2 (by simpa [mul_comm] using h)



lemma continuousOn_omega_Ioi : ContinuousOn omega (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  apply ContinuousAt.continuousWithinAt
  unfold omega
  fun_prop (disch := positivity)

 
theorem expectation_covariance {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : IntegrableOn (fun y => f y * density N y) (orderedDomain N))
    (hg : IntegrableOn (fun y => g y * density N y) (orderedDomain N))
    (hfg : IntegrableOn (fun y => (f y * g y) * density N y) (orderedDomain N)) :
    expectation N f * expectation N g ≤ expectation N (fun y => f y * g y) := by
  unfold expectation
  apply weighted_covariance_normalize (normalizer_pos N)
  have h := ordered_density_covariance_Ioo (by norm_num : (0 : ℝ) < 1)
    (fun _ : Fin N => omega) (fun _ => continuousOn_omega_Ioi.mono (fun _ hx => hx.1))
    (fun _ x _ => omega_nonneg x) f g hfc hgc hfm hgm (integrableOn_density N)
    (by simpa only [rawProductDensity, density, orderedChamber, orderedDomain, mul_comm] using hf)
    (by simpa only [rawProductDensity, density, orderedChamber, orderedDomain, mul_comm] using hg)
    (by simpa only [rawProductDensity, density, orderedChamber, orderedDomain, mul_comm] using hfg)
  simpa only [rawProductDensity, density, orderedChamber, orderedDomain, normalizer, mul_comm] using h

lemma cutoffRamp_bounds (n : ℕ) (R x : ℝ) :
    0 ≤ cutoffRamp n R x ∧ cutoffRamp n R x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma continuous_cutoffRamp (n : ℕ) (R : ℝ) : Continuous (cutoffRamp n R) := by
  unfold cutoffRamp
  fun_prop

lemma antitone_cutoffRamp (n : ℕ) (R : ℝ) : Antitone (cutoffRamp n R) := by
  intro x y hxy
  exact min_le_min_left 1 (max_le_max_left 0
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hxy R) (by positivity)))

lemma cutoffRamp_tendsto (R x : ℝ) :
    Tendsto (fun n => cutoffRamp n R x) atTop (nhds (if x < R then 1 else 0)) := by
  split_ifs with hx
  · obtain ⟨b, hb⟩ := exists_nat_gt (1 / (R - x))
    have hb' : 1 < (b : ℝ) * (R - x) := (div_lt_iff₀ (sub_pos.mpr hx)).mp hb
    have he : (fun n => cutoffRamp n R x) =ᶠ[atTop] (fun _ => 1) := by
      filter_upwards [eventually_ge_atTop b] with n hn
      have hn' : (b : ℝ) ≤ n := Nat.cast_le.mpr hn
      have hm : 1 ≤ (n + 1 : ℝ) * (R - x) := by nlinarith
      exact min_eq_left (hm.trans (le_max_right _ _))
    exact (tendsto_congr' he).2 tendsto_const_nhds
  · have he : (fun n => cutoffRamp n R x) = (fun _ => 0) := by
      funext n
      have hm : (n + 1 : ℝ) * (R - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (le_of_not_gt hx))
      simp only [cutoffRamp, max_eq_left hm, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    rw [he]
    exact tendsto_const_nhds



lemma measurableSet_cutoffEvent (N : ℕ) (R : ℝ) : MeasurableSet (cutoffEvent N R) :=
  measurableSet_coordinateBox measurableSet_Iio

lemma cutoffProduct_bounds (N n : ℕ) (R : ℝ) (r : Fin N → ℝ) :
    0 ≤ cutoffProduct N n R r ∧ cutoffProduct N n R r ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => (cutoffRamp_bounds n R (r i)).1), ?_⟩
  exact Finset.prod_le_one (fun i _ => (cutoffRamp_bounds n R (r i)).1)
    (fun i _ => (cutoffRamp_bounds n R (r i)).2)

lemma cutoffProduct_norm_le (N n : ℕ) (R : ℝ) (r : Fin N → ℝ) :
    ‖cutoffProduct N n R r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoffProduct_bounds N n R r).1]
  exact (cutoffProduct_bounds N n R r).2

lemma continuous_cutoffProduct (N n : ℕ) (R : ℝ) : Continuous (cutoffProduct N n R) := by
  unfold cutoffProduct
  exact continuous_finsetProd _ fun i _ => (continuous_cutoffRamp n R).comp (continuous_apply i)

lemma antitone_cutoffProduct (N n : ℕ) (R : ℝ) : Antitone (cutoffProduct N n R) := by
  intro r s hrs
  exact Finset.prod_le_prod (fun i _ => (cutoffRamp_bounds n R (s i)).1)
    (fun i _ => antitone_cutoffRamp n R (hrs i))

lemma cutoffProduct_tendsto (N : ℕ) (R : ℝ) (r : Fin N → ℝ) :
    Tendsto (fun n => cutoffProduct N n R r) atTop
      (nhds ((cutoffEvent N R).indicator (fun _ => (1 : ℝ)) r)) := by
  classical
  have he : (∏ i : Fin N, if r i < R then (1 : ℝ) else 0) =
      (cutoffEvent N R).indicator (fun _ => (1 : ℝ)) r := by
    by_cases hr : ∀ i, r i < R
    · simp [cutoffEvent, coordinateBox, hr]
    · have hr' : r ∉ cutoffEvent N R := hr
      rw [indicator_of_notMem hr']
      obtain ⟨i, hi⟩ := not_forall.mp hr
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simpa only [cutoffProduct, he] using
    tendsto_finsetProd Finset.univ (fun i _ => cutoffRamp_tendsto R (r i))

lemma cutoffProduct_integrable {N : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (n : ℕ) (R : ℝ) : Integrable (cutoffProduct N n R) μ :=
  (integrable_const (1 : ℝ)).mono' (continuous_cutoffProduct N n R).aestronglyMeasurable
    (Eventually.of_forall (cutoffProduct_norm_le N n R))

lemma cutoffProduct_integral_tendsto {N : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (R : ℝ) : Tendsto (fun n => ∫ r, cutoffProduct N n R r ∂μ) atTop
      (nhds (μ.real (cutoffEvent N R))) := by
  rw [← integral_indicator_one (measurableSet_cutoffEvent N R)]
  exact tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (continuous_cutoffProduct N n R).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (cutoffProduct_norm_le N n R))
    (Eventually.of_forall (cutoffProduct_tendsto N R))

lemma cutoffProduct_weighted_tendsto {N : ℕ} (μ : Measure (Fin N → ℝ)) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) (hf : Integrable f μ) :
    Tendsto (fun n => ∫ r, f r * cutoffProduct N n R r ∂μ) atTop
      (nhds (∫ r in cutoffEvent N R, f r ∂μ)) := by
  have he : (fun r => f r * (cutoffEvent N R).indicator (fun _ => (1 : ℝ)) r) =
      (cutoffEvent N R).indicator f := by
    funext r
    by_cases hr : r ∈ cutoffEvent N R <;> simp [hr]
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun r => ‖f r‖)
    (fun n => hf.aestronglyMeasurable.mul (continuous_cutoffProduct N n R).aestronglyMeasurable) hf.norm
    (fun n => Eventually.of_forall fun r =>
      calc ‖f r * cutoffProduct N n R r‖ = ‖f r‖ * ‖cutoffProduct N n R r‖ := norm_mul _ _
           _ ≤ ‖f r‖ * 1 := mul_le_mul_of_nonneg_left (cutoffProduct_norm_le N n R r) (norm_nonneg _)
           _ = ‖f r‖ := mul_one _)
    (Eventually.of_forall fun r => tendsto_const_nhds.mul (cutoffProduct_tendsto N R r))
  simpa only [Pi.mul_apply, he, integral_indicator (measurableSet_cutoffEvent N R)] using ht



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CoordinateBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter
lemma isOpen_coordinateBox {ι : Type*} [Fintype ι] {I : Set ℝ} (hI : IsOpen I) :
    IsOpen (coordinateBox ι I) := by
  have he : coordinateBox ι I = ⋂ i : ι, (fun x : ι → ℝ => x i) ⁻¹' I := by
    ext x
    simp [coordinateBox]
  rw [he]
  exact isOpen_iInter_of_finite fun i : ι => hI.preimage (continuous_apply i)

lemma isOpen_cutoffEvent (N : ℕ) (R : ℝ) : IsOpen (cutoffEvent N R) :=
  isOpen_coordinateBox isOpen_Iio

lemma laguerreDomain_cutoff_nonempty (N : ℕ) {R : ℝ} (hR : 0 < R) :
    (laguerreDomain N ∩ cutoffEvent N R).Nonempty := by
  obtain ⟨v, hvm, hv⟩ := orderedDomain_nonempty N
  refine ⟨fun i => R * v i, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_left (hvm hij) hR
  · intro i
    exact mul_pos hR (hv i).1
  · intro i
    simpa using mul_lt_mul_of_pos_left (hv i).2 hR

 

theorem laguerreLaw_cutoff_pos (N : ℕ) {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    0 < (laguerreLaw N a).real (cutoffEvent N R) := by
  rw [laguerreLaw_measureReal N ha (measurableSet_cutoffEvent N R)]
  apply div_pos ?_ (laguerreNormalizer_pos N ha)
  let S : Set (Fin N → ℝ) := laguerreDomain N ∩ cutoffEvent N R
  have hS : IsOpen S := (isOpen_laguerreDomain N).inter (isOpen_cutoffEvent N R)
  have hi : IntegrableOn (laguerreDensity N a) S :=
    (integrableOn_laguerreDensity N ha).mono_set inter_subset_left
  have hpos : 0 ≤ᵐ[volume.restrict S] laguerreDensity N a := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with r hr
    exact (laguerreDensity_pos a hr.1).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos hi).2
  calc 0 < volume S := hS.measure_pos volume (laguerreDomain_cutoff_nonempty N hR)
       _ = (volume.restrict S) S := (Measure.restrict_apply_self _ _).symm
       _ ≤ (volume.restrict S) (Function.support (laguerreDensity N a)) :=
         measure_mono (fun r hr => (laguerreDensity_pos a hr.1).ne')



theorem positiveLaw_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (positiveLaw N) := by
  refine ⟨?_⟩
  rw [positiveLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_density N)]
  · exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (normalizer_pos N)).ne' ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
    exact (density_pos hy).le

theorem integral_positiveLaw (N : ℕ) (f : (Fin N → ℝ) → ℝ) :
    (∫ y, f y ∂positiveLaw N) = expectation N f := by
  rw [positiveLaw, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_density N).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (normalizer_pos N).le,
    smul_eq_mul, expectation, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [ENNReal.toReal_ofReal (density_pos hy).le, mul_comm]

theorem integrable_positiveLaw_iff {N : ℕ} {f : (Fin N → ℝ) → ℝ} :
    Integrable f (positiveLaw N) ↔
      IntegrableOn (fun y => f y * density N y) (orderedDomain N) := by
  rw [positiveLaw, integrable_smul_measure (by simp) (by simpa using normalizer_pos N),
    integrable_withDensity_iff_integrable_smul' (measurable_density N).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  simp [smul_eq_mul, ENNReal.toReal_ofReal (density_pos hy).le, mul_comm]

theorem positiveLaw_covariance {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) (hg : Integrable g (positiveLaw N))
    (hfg : Integrable (fun r => f r * g r) (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) * (∫ r, g r ∂positiveLaw N) ≤
      ∫ r, f r * g r ∂positiveLaw N := by
  simpa only [integral_positiveLaw] using
    expectation_covariance f g hfc hgc hfm hgm (integrable_positiveLaw_iff.1 hf)
      (integrable_positiveLaw_iff.1 hg) (integrable_positiveLaw_iff.1 hfg)

theorem positiveLaw_covariance_antitone {N : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hgm : AntitoneOn g (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) (hg : Integrable g (positiveLaw N))
    (hfg : Integrable (fun r => f r * g r) (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) * (∫ r, g r ∂positiveLaw N) ≤
      ∫ r, f r * g r ∂positiveLaw N := by
  have h := positiveLaw_covariance (fun r => -f r) (fun r => -g r) hfc.neg hgc.neg
    (fun _ hx _ hy hxy => neg_le_neg (hfm hx hy hxy))
    (fun _ hx _ hy hxy => neg_le_neg (hgm hx hy hxy)) hf.neg hg.neg (by simpa using hfg)
  simpa only [integral_neg, neg_mul_neg] using h

theorem positiveLaw_cutoff_covariance {N : ℕ} (R : ℝ) (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) * (positiveLaw N).real (cutoffEvent N R) ≤
      ∫ r in cutoffEvent N R, f r ∂positiveLaw N := by
  let := positiveLaw_isProbabilityMeasure N
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (cutoffProduct_integral_tendsto (positiveLaw N) R))
    (cutoffProduct_weighted_tendsto (positiveLaw N) R f hf)
  apply Eventually.of_forall
  intro n
  exact positiveLaw_covariance_antitone f (cutoffProduct N n R) hfc
    (continuous_cutoffProduct N n R).continuousOn hfm
    ((antitone_cutoffProduct N n R).antitoneOn _) hf (cutoffProduct_integrable _ n R)
    (hf.mul_bdd (continuous_cutoffProduct N n R).aestronglyMeasurable
      (Eventually.of_forall (cutoffProduct_norm_le N n R)))

theorem positiveLaw_integrable_inverseQuarterSum (N : ℕ) :
    Integrable (fun y : Fin N → ℝ => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ)) (positiveLaw N) :=
  integrable_positiveLaw_iff.2 (integrableOn_inverseQuarterSum_density N)



theorem positiveLaw_measureReal (N : ℕ)
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) :
    (positiveLaw N).real s = (∫ r in orderedDomain N ∩ s, density N r) / normalizer N := by
  let := positiveLaw_isProbabilityMeasure N
  rw [← integral_indicator_one hs, integral_positiveLaw N]
  unfold expectation
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hs]

lemma orderedDomain_cutoff_nonempty (N : ℕ) {R : ℝ} (hR : 0 < R) :
    (orderedDomain N ∩ cutoffEvent N R).Nonempty := by
  obtain ⟨v, hvm, hv⟩ := orderedDomain_nonempty N
  have ht : 0 < min R 1 := lt_min hR (by norm_num)
  refine ⟨fun i => min R 1 * v i, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_left (hvm hij) ht
  · intro i
    have hi : min R 1 * v i < min R 1 := by simpa using mul_lt_mul_of_pos_left (hv i).2 ht
    exact ⟨mul_pos ht (hv i).1, hi.trans_le (min_le_right _ _)⟩
  · intro i
    have hi : min R 1 * v i < min R 1 := by simpa using mul_lt_mul_of_pos_left (hv i).2 ht
    exact hi.trans_le (min_le_left _ _)

theorem positiveLaw_cutoff_pos (N : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < (positiveLaw N).real (cutoffEvent N R) := by
  rw [positiveLaw_measureReal N (measurableSet_cutoffEvent N R)]
  apply div_pos ?_ (normalizer_pos N)
  let S : Set (Fin N → ℝ) := orderedDomain N ∩ cutoffEvent N R
  have hS : IsOpen S := (isOpen_orderedDomain N).inter (isOpen_cutoffEvent N R)
  have hi : IntegrableOn (density N) S := (integrableOn_density N).mono_set inter_subset_left
  have hpos : 0 ≤ᵐ[volume.restrict S] density N := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with r hr
    exact (density_pos hr.1).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos hi).2
  calc 0 < volume S := hS.measure_pos volume (orderedDomain_cutoff_nonempty N hR)
       _ = (volume.restrict S) S := (Measure.restrict_apply_self _ _).symm
       _ ≤ (volume.restrict S) (Function.support (density N)) :=
         measure_mono (fun _ hr => (density_pos hr.1).ne')

 

theorem positiveLaw_conditioned_antitone {N : ℕ} {R : ℝ} (hR : 0 < R)
    (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioo 0 1)))
    (hf : Integrable f (positiveLaw N)) :
    (∫ r, f r ∂positiveLaw N) ≤
      (∫ r in cutoffEvent N R, f r ∂positiveLaw N) /
        (positiveLaw N).real (cutoffEvent N R) := by
  exact (le_div_iff₀ (positiveLaw_cutoff_pos N hR)).2
    (positiveLaw_cutoff_covariance R f hfc hfm hf)

lemma continuousOn_inverseQuarterSum {ι : Type*} [Fintype ι] :
    ContinuousOn (fun r : ι → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ))
      (coordinateBox ι (Ioi 0)) := by
  have hsum : ContinuousOn (fun r : ι → ℝ => ∑ i, (r i)⁻¹) (coordinateBox ι (Ioi 0)) := by
    exact continuousOn_finsetSum _ fun i _ =>
      (continuous_apply i).continuousOn.inv₀ (fun _ hr => (hr i).ne')
  exact hsum.rpow_const (fun _ _ => Or.inr (by norm_num))

lemma antitoneOn_inverseQuarterSum {ι : Type*} [Fintype ι] :
    AntitoneOn (fun r : ι → ℝ => (∑ i, (r i)⁻¹) ^ (1 / 4 : ℝ))
      (coordinateBox ι (Ioi 0)) := by
  intro x hx y hy hxy
  apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hy i).le)) ?_ (by norm_num)
  exact Finset.sum_le_sum fun i _ => inv_anti₀ (hx i) (hxy i)

theorem positiveLaw_cutoff_inverseQuarterSum {N : ℕ} {R : ℝ} (hR : 0 < R) :
    (∫ y : Fin N → ℝ, (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) ∂positiveLaw N) ≤
      (∫ y in cutoffEvent N R, (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) ∂positiveLaw N) /
        (positiveLaw N).real (cutoffEvent N R) := by
  exact positiveLaw_conditioned_antitone hR _
    (continuousOn_inverseQuarterSum.mono (fun _ hx i => (hx i).1))
    (antitoneOn_inverseQuarterSum.mono (fun _ hx i => (hx i).1))
    (positiveLaw_integrable_inverseQuarterSum N)

lemma mem_cutoffEvent_iff_last {n : ℕ} {r : Fin (n + 1) → ℝ} (hr : Monotone r) (R : ℝ) :
    r ∈ cutoffEvent (n + 1) R ↔ r (Fin.last n) < R := by
  constructor
  · exact fun h => h (Fin.last n)
  · intro h i
    exact (hr (Fin.le_last i)).trans_lt h

end

end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_WeightComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
lemma hasDerivAt_omegaLogHalf {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt omegaLogHalf
      ((1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x))) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hd : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx0
  have hr : 1 < (1 + x) / (2 * x) := (lt_div_iff₀ (by linarith [hx.1])).2 (by linarith [hx.2])
  have ht : 1 < Real.sqrt ((1 + x) / (2 * x)) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + x) / (2 * x)), Real.sqrt_nonneg ((1 + x) / (2 * x))]
  have hs : 0 < Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hs2 := Real.sq_sqrt (by linarith : 0 ≤ Real.sqrt ((1 + x) / (2 * x)) - 1)
  have ht2 := Real.sq_sqrt (by linarith : 0 ≤ (1 + x) / (2 * x))
  have ht2' : 2 * x * (Real.sqrt ((1 + x) / (2 * x))) ^ 2 = 1 + x := by
    rw [ht2]
    exact mul_div_cancel₀ (1 + x) hd
  have hdr : HasDerivAt (fun y : ℝ => (1 + y) / (2 * y)) (-1 / (2 * x ^ 2)) x := by
    apply (((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_mul 2) hd).congr_deriv
    dsimp
    field_simp
    ring
  have hω := (((hdr.sqrt (by linarith : (1 + x) / (2 * x) ≠ 0)).sub_const 1).sqrt
    (by linarith : Real.sqrt ((1 + x) / (2 * x)) - 1 ≠ 0)).const_mul (1 / 2 : ℝ)
  have hdω : HasDerivAt omega
      (-1 / (16 * x ^ 2 * Real.sqrt ((1 + x) / (2 * x)) *
        Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1))) x := by
    apply hω.congr_deriv
    field_simp
    ring
  have hdlog := (hdω.log (omega_pos hx).ne').add
    (((hasDerivAt_id x).log hx0).const_mul (1 / 2 : ℝ))
  apply hdlog.congr_deriv
  dsimp only [omega, id_eq]
  have ht0 : Real.sqrt ((1 + x) / (2 * x)) ≠ 0 := by linarith
  have hs0 := hs.ne'
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  generalize htdef : Real.sqrt ((1 + x) / (2 * x)) = t at *
  generalize hsdef : Real.sqrt (t - 1) = s at *
  field_simp
  ring_nf
  rw [hs2]
  nlinarith [ht2']

 

lemma omegaLogHalf_derivative_lower {x : ℝ} (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) :
    -4 ≤ (1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x)) := by
  have hr : 1 ≤ (1 + x) / (2 * x) := (le_div_iff₀ (by linarith [hx.1])).2 (by linarith [hx.2])
  have ht : 1 ≤ Real.sqrt ((1 + x) / (2 * x)) := Real.one_le_sqrt.mpr hr
  have hinv : (Real.sqrt ((1 + x) / (2 * x)))⁻¹ ≤ 1 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) ht
  have hdp : 0 < 4 * x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  by_cases hsmall : x ≤ 1 / 8
  · have ht4 : (2 : ℝ) ^ 2 ≤ (1 + x) / (2 * x) :=
      (le_div_iff₀ (by linarith [hx.1])).2 (by nlinarith)
    have ht2 : 2 ≤ Real.sqrt ((1 + x) / (2 * x)) := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 + x) / (2 * x)), Real.sqrt_nonneg ((1 + x) / (2 * x))]
    have hinv2 : (Real.sqrt ((1 + x) / (2 * x)))⁻¹ ≤ 1 / 2 := by
      simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) ht2
    have : 0 ≤ (1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x)) :=
      div_nonneg (by linarith) hdp.le
    linarith
  · have hx8 : 1 / 8 ≤ x := le_of_not_ge hsmall
    have hden : 1 / 4 ≤ 4 * x * (1 - x) := by nlinarith [mul_nonneg hx.1.le (by linarith [hx.2] : 0 ≤ 1 / 2 - x)]
    apply (le_div_iff₀ hdp).2
    nlinarith [hx.2]


lemma upperLikelihoodWeight_exp {x : ℝ} (hx : x ∈ Ioo 0 1) (β : ℝ) :
    upperLikelihoodWeight β x = Real.exp (omegaLogHalf x + β * x) := by
  rw [omegaLogHalf, Real.exp_add, Real.exp_add, Real.exp_log (omega_pos hx)]
  simp only [upperLikelihoodWeight, Real.rpow_def_of_pos hx.1, mul_comm (Real.log x) (1 / 2 : ℝ)]

 

theorem upperLikelihoodWeight_monotone {β : ℝ} (hb : 4 ≤ β) :
    MonotoneOn (upperLikelihoodWeight β) (Ioo 0 (1 / 2 : ℝ)) := by
  have hh (x : ℝ) (hx : x ∈ Ioo 0 (1 / 2 : ℝ)) :
      HasDerivAt (fun x => omegaLogHalf x + β * x)
        ((1 - 2 * x - (Real.sqrt ((1 + x) / (2 * x)))⁻¹) / (4 * x * (1 - x)) + β) x := by
    apply ((hasDerivAt_omegaLogHalf ⟨hx.1, by linarith [hx.2]⟩).add ((hasDerivAt_id x).const_mul β)).congr_deriv
    simp only [mul_one]
  have hmono : MonotoneOn (fun x => omegaLogHalf x + β * x) (Ioo 0 (1 / 2 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo (0 : ℝ) (1 / 2 : ℝ))
      (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hh x (by simpa only [interior_Ioo] using hx)).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Ioo 0 (1 / 2 : ℝ) := by simpa only [interior_Ioo] using hx
    linarith [omegaLogHalf_derivative_lower ⟨hx'.1, hx'.2.le⟩]
  intro x hx y hy hxy
  rw [upperLikelihoodWeight_exp ⟨hx.1, by linarith [hx.2]⟩,
    upperLikelihoodWeight_exp ⟨hy.1, by linarith [hy.2]⟩]
  exact Real.exp_le_exp.mpr (hmono hx hy hxy)

end

noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter


lemma laguerreDensityScale_pos (N : ℕ) (a : ℝ) {β : ℝ} (hb : 0 < β) :
    0 < laguerreDensityScale N a β := by
  unfold laguerreDensityScale
  exact mul_pos (Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos hb _)
    (Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => hb)

lemma pairKernel_smul {β : ℝ} (hb : β ≠ 0) (x y : ℝ) :
    pairKernel (β * x) (β * y) = β * pairKernel x y := by
  unfold pairKernel
  rw [← mul_sub, ← mul_add, mul_pow, pow_two β, mul_assoc,
    mul_div_mul_left _ _ hb, mul_div_assoc]

lemma laguerreDensity_scaled {N : ℕ} (a : ℝ) {β : ℝ} (hb : 0 < β)
    {y : Fin N → ℝ} (hy : ∀ i, 0 < y i) :
    laguerreDensity N a (β • y) = laguerreDensityScale N a β * scaledLaguerreDensity N a β y := by
  have hw (i : Fin N) : laguerreWeight a ((β • y) i) =
      β ^ (a - 1) * scaledLaguerreWeight a β (y i) := by
    simp only [Pi.smul_apply, smul_eq_mul, laguerreWeight, scaledLaguerreWeight,
      Real.mul_rpow hb.le (hy i).le, mul_assoc]
  have hp (i j : Fin N) : pairKernel ((β • y) i) ((β • y) j) =
      β * pairKernel (y i) (y j) := pairKernel_smul hb.ne' _ _
  simp only [laguerreDensity, hw, hp, Finset.prod_mul_distrib,
    laguerreDensityScale, scaledLaguerreDensity, rawProductDensity]
  ring

lemma orderedChamber_eq_laguerre_cutoff (N : ℕ) (R : ℝ) :
    orderedChamber N (Ioo 0 R) = laguerreDomain N ∩ cutoffEvent N R := by
  ext y
  constructor
  · exact fun h => ⟨⟨h.1, fun i => (h.2 i).1⟩, fun i => (h.2 i).2⟩
  · exact fun h => ⟨h.1.1, fun i => ⟨h.1.2 i, h.2 i⟩⟩

lemma measurableSet_orderedChamber_Ioo (N : ℕ) (R : ℝ) :
    MeasurableSet (orderedChamber N (Ioo 0 R)) := by
  rw [orderedChamber_eq_laguerre_cutoff]
  exact (isOpen_laguerreDomain N).measurableSet.inter (measurableSet_cutoffEvent N R)

lemma orderedChamber_smul {N : ℕ} (R : ℝ) {β : ℝ} (hb : 0 < β) :
    β • orderedChamber N (Ioo 0 R) = orderedChamber N (Ioo 0 (β * R)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i j hij => mul_lt_mul_of_pos_left (hx.1 hij) hb,
      fun i => ⟨mul_pos hb (hx.2 i).1, mul_lt_mul_of_pos_left (hx.2 i).2 hb⟩⟩
  · intro hy
    refine ⟨β⁻¹ • y, ⟨?_, ?_⟩, smul_inv_smul₀ hb.ne' y⟩
    · exact fun i j hij => mul_lt_mul_of_pos_left (hy.1 hij) (inv_pos.mpr hb)
    · intro i
      constructor
      · exact mul_pos (inv_pos.mpr hb) (hy.2 i).1
      · change β⁻¹ * y i < R
        exact (inv_mul_lt_iff₀ hb).2 (hy.2 i).2

lemma integral_orderedChamber_scaled {N : ℕ} (R : ℝ) {β : ℝ} (hb : 0 < β)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ y in orderedChamber N (Ioo 0 R), f (β • y)) =
      (β ^ N)⁻¹ * ∫ r in orderedChamber N (Ioo 0 (β * R)), f r := by
  simpa only [orderedChamber_smul R hb, Module.finrank_pi, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul, mul_one,
    Nat.cast_id, nsmul_eq_mul, Nat.cast_one] using
    Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin N → ℝ)) f
      (orderedChamber N (Ioo 0 R)) hb

lemma inverseQuarterSum_smul {N : ℕ} {β : ℝ} (hb : 0 < β)
    {y : Fin N → ℝ} (hy : ∀ i, 0 < y i) :
    (∑ i, ((β • y) i)⁻¹) ^ (1 / 4 : ℝ) =
      (β ^ (1 / 4 : ℝ))⁻¹ * (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_comm (y _)⁻¹ β⁻¹,
    ← Finset.mul_sum]
  rw [Real.mul_rpow (inv_nonneg.mpr hb.le) (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hy i)).le),
      Real.inv_rpow hb.le]

lemma measurable_scaledLaguerreWeight (a β : ℝ) : Measurable (scaledLaguerreWeight a β) := by
  unfold scaledLaguerreWeight
  fun_prop

lemma continuousOn_scaledLaguerreWeight (a β : ℝ) :
    ContinuousOn (scaledLaguerreWeight a β) (Ioi 0) := by
  unfold scaledLaguerreWeight
  exact (continuousOn_id.rpow_const (fun _ hx => Or.inl (ne_of_gt hx))).mul
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn)

lemma scaledLaguerreWeight_pos (a β : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < scaledLaguerreWeight a β x := by
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

lemma scaledLaguerreWeight_le (a : ℝ) {β x : ℝ} (hb : 1 ≤ β) (hx : 0 < x) :
    scaledLaguerreWeight a β x ≤ laguerreWeight a x := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hx _).le
  apply Real.exp_le_exp.mpr
  nlinarith

lemma scaledLaguerreDensity_pos {N : ℕ} (a β : ℝ) {y : Fin N → ℝ}
    (hy : y ∈ laguerreDomain N) : 0 < scaledLaguerreDensity N a β y := by
  exact mul_pos (Finset.prod_pos fun i _ => scaledLaguerreWeight_pos a β (hy.2 i))
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      pairKernel_pos (hy.2 i) (hy.1 (Finset.mem_Ioi.1 hj)))

lemma scaledLaguerreDensity_le {N : ℕ} (a : ℝ) {β : ℝ} (hb : 1 ≤ β)
    {y : Fin N → ℝ} (hy : y ∈ laguerreDomain N) :
    scaledLaguerreDensity N a β y ≤ laguerreDensity N a y := by
  apply mul_le_mul_of_nonneg_right _
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
      pairKernel_nonneg (hy.2 i).le (hy.2 j).le)
  exact Finset.prod_le_prod (fun i _ => (scaledLaguerreWeight_pos a β (hy.2 i)).le)
    (fun i _ => scaledLaguerreWeight_le a hb (hy.2 i))

lemma measurable_scaledLaguerreDensity (N : ℕ) (a β : ℝ) :
    Measurable (scaledLaguerreDensity N a β) := by
  unfold scaledLaguerreDensity rawProductDensity pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_scaledLaguerreWeight a β).comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

lemma integrableOn_scaledLaguerreDensity {N : ℕ} {a β : ℝ} (ha : 0 < a) (hb : 1 ≤ β) :
    IntegrableOn (scaledLaguerreDensity N a β) (laguerreDomain N) := by
  apply (integrableOn_laguerreDensity N ha).mono'
    (measurable_scaledLaguerreDensity N a β).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with y hy
  simpa only [Real.norm_eq_abs, abs_of_pos (scaledLaguerreDensity_pos a β hy)] using
    scaledLaguerreDensity_le a hb hy

lemma inverseQuarterStatistic_nonneg {N : ℕ} {y : Fin N → ℝ} (hy : ∀ i, 0 < y i) :
    0 ≤ inverseQuarterStatistic N y :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hy i)).le) _

lemma measurable_inverseQuarterStatistic (N : ℕ) : Measurable (inverseQuarterStatistic N) := by
  unfold inverseQuarterStatistic
  fun_prop

lemma integrableOn_scaledLaguerre_inverseQuarter {N : ℕ} {a β : ℝ}
    (ha : 1 / 4 < a) (hb : 1 ≤ β) :
    IntegrableOn (fun y => inverseQuarterStatistic N y * scaledLaguerreDensity N a β y)
      (laguerreDomain N) := by
  apply (integrableOn_laguerre_inverseQuarterSum ha).mono'
    ((measurable_inverseQuarterStatistic N).mul
      (measurable_scaledLaguerreDensity N a β)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with y hy
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inverseQuarterStatistic_nonneg hy.2)
    (scaledLaguerreDensity_pos a β hy).le)]
  exact mul_le_mul_of_nonneg_left (scaledLaguerreDensity_le a hb hy)
    (inverseQuarterStatistic_nonneg hy.2)

lemma scaledLaguerre_cutoffNormalizer_pos (N : ℕ) {a β R : ℝ}
    (ha : 0 < a) (hb : 1 ≤ β) (hR : 0 < R) :
    0 < ∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y := by
  rw [orderedChamber_eq_laguerre_cutoff]
  let S : Set (Fin N → ℝ) := laguerreDomain N ∩ cutoffEvent N R
  have hS : IsOpen S := (isOpen_laguerreDomain N).inter (isOpen_cutoffEvent N R)
  have hi : IntegrableOn (scaledLaguerreDensity N a β) S :=
    (integrableOn_scaledLaguerreDensity ha hb).mono_set inter_subset_left
  have hn : 0 ≤ᵐ[volume.restrict S] scaledLaguerreDensity N a β := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with r hr
    exact (scaledLaguerreDensity_pos a β hr.1).le
  apply (integral_pos_iff_support_of_nonneg_ae hn hi).2
  calc 0 < volume S := hS.measure_pos volume (laguerreDomain_cutoff_nonempty N hR)
       _ = (volume.restrict S) S := (Measure.restrict_apply_self _ _).symm
       _ ≤ (volume.restrict S) (Function.support (scaledLaguerreDensity N a β)) :=
          measure_mono fun _ hr => (scaledLaguerreDensity_pos a β hr.1).ne'

lemma continuousOn_upperLikelihood (N : ℕ) (β : ℝ) :
    ContinuousOn (upperLikelihood N β) (coordinateBox (Fin N) (Ioi 0)) := by
  unfold upperLikelihood upperLikelihoodWeight
  apply continuousOn_finsetProd
  intro i _
  apply ContinuousOn.mul
  · exact (continuousOn_omega_Ioi.comp (continuous_apply i).continuousOn (show MapsTo (fun y : Fin N → ℝ => y i) (coordinateBox (Fin N) (Ioi 0)) (Ioi 0) from fun _ hy => hy i)).mul
      ((continuous_apply i).continuousOn.rpow_const (fun _ hy => Or.inl (hy i).ne'))
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).continuousOn

lemma upperLikelihood_monotone (N : ℕ) {β : ℝ} (hb : 4 ≤ β) :
    MonotoneOn (upperLikelihood N β) (coordinateBox (Fin N) (Ioo 0 (1 / 2 : ℝ))) := by
  intro x hx y hy hxy
  apply Finset.prod_le_prod
  · intro i _
    exact mul_nonneg (mul_nonneg (omega_nonneg _) (Real.rpow_nonneg (hx i).1.le _))
      (Real.exp_pos _).le
  · intro i _
    exact upperLikelihoodWeight_monotone hb (hx i) (hy i) (hxy i)

lemma scaledWeight_mul_upperLikelihoodWeight (β : ℝ) {x : ℝ} (hx : 0 < x) :
    scaledLaguerreWeight (1 / 2) β x * upperLikelihoodWeight β x = omega x := by
  unfold scaledLaguerreWeight upperLikelihoodWeight
  calc
    x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(β * x)) *
        (omega x * x ^ (1 / 2 : ℝ) * Real.exp (β * x)) =
      omega x * (x ^ ((1 / 2 : ℝ) - 1) * x ^ (1 / 2 : ℝ)) *
        (Real.exp (-(β * x)) * Real.exp (β * x)) := by ring
    _ = omega x := by
      rw [← Real.rpow_add hx, ← Real.exp_add]
      norm_num

lemma scaledDensity_mul_upperLikelihood {N : ℕ} (β : ℝ) {y : Fin N → ℝ}
    (hy : ∀ i, 0 < y i) :
    scaledLaguerreDensity N (1 / 2) β y * upperLikelihood N β y = density N y := by
  have hw : (∏ i, scaledLaguerreWeight (1 / 2) β (y i)) *
      (∏ i, upperLikelihoodWeight β (y i)) = ∏ i, omega (y i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => scaledWeight_mul_upperLikelihoodWeight β (hy i)
  unfold scaledLaguerreDensity rawProductDensity upperLikelihood density
  rw [mul_right_comm, hw]

lemma orderedChamber_eq_positive_cutoff (N : ℕ) {R : ℝ} (hR : R ≤ 1) :
    orderedChamber N (Ioo 0 R) = orderedDomain N ∩ cutoffEvent N R := by
  ext y
  constructor
  · exact fun h => ⟨⟨h.1, fun i => ⟨(h.2 i).1, (h.2 i).2.trans_le hR⟩⟩,
      fun i => (h.2 i).2⟩
  · exact fun h => ⟨h.1.1, fun i => ⟨(h.1.2 i).1, h.2 i⟩⟩

lemma positive_cutoffNormalizer_pos (N : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    0 < ∫ y in orderedChamber N (Ioo 0 R), density N y := by
  have h := positiveLaw_cutoff_pos N hR
  rw [positiveLaw_measureReal N (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_positive_cutoff N hR1] at h
  exact (div_pos_iff_of_pos_right (normalizer_pos N)).1 h

 

theorem positive_half_inverseQuarter_le_scaled_reference (N : ℕ) {β : ℝ} (hb : 4 ≤ β) :
    (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), inverseQuarterStatistic N y * density N y) /
        (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), density N y) ≤
      (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), inverseQuarterStatistic N y *
        scaledLaguerreDensity N (1 / 2) β y) /
      (∫ y in orderedChamber N (Ioo 0 (1 / 2 : ℝ)), scaledLaguerreDensity N (1 / 2) β y) := by
  let S := orderedChamber N (Ioo 0 (1 / 2 : ℝ))
  have hS := measurableSet_orderedChamber_Ioo N (1 / 2)
  have hSl : S ⊆ laguerreDomain N := fun _ hy => ⟨hy.1, fun i => (hy.2 i).1⟩
  have hSt : S ⊆ orderedDomain N := fun _ hy => ⟨hy.1, fun i =>
    ⟨(hy.2 i).1, (hy.2 i).2.trans (by norm_num)⟩⟩
  have heq : (fun y => scaledLaguerreDensity N (1 / 2) β y * upperLikelihood N β y) =ᵐ[volume.restrict S]
      density N := by
    filter_upwards [ae_restrict_mem hS] with y hy
    exact scaledDensity_mul_upperLikelihood β (fun i => (hy.2 i).1)
  have hiT := (integrableOn_density N).mono_set hSt
  have hiTF := (integrableOn_inverseQuarterSum_density N).mono_set hSt
  have hiB := (integrableOn_scaledLaguerreDensity (N := N) (by norm_num : (0 : ℝ) < 1/2)
    (by linarith : 1 ≤ β)).mono_set hSl
  have hiBF := (integrableOn_scaledLaguerre_inverseQuarter (N := N) (by norm_num : (1/4 : ℝ) < 1/2)
    (by linarith : 1 ≤ β)).mono_set hSl
  have heqF : (fun y => scaledLaguerreDensity N (1 / 2) β y *
      (-inverseQuarterStatistic N y * upperLikelihood N β y)) =ᵐ[volume.restrict S]
        (fun y => -(inverseQuarterStatistic N y * density N y)) := by
    filter_upwards [heq] with y hy
    calc
      _ = - (inverseQuarterStatistic N y * (scaledLaguerreDensity N (1/2) β y * upperLikelihood N β y)) := by ring
      _ = _ := by rw [hy]
  have h := ordered_density_covariance_Ioo (by norm_num : (0 : ℝ) < 1/2)
    (fun _ : Fin N => scaledLaguerreWeight (1 / 2) β)
    (fun _ => (continuousOn_scaledLaguerreWeight (1/2) β).mono (fun _ hx => hx.1))
    (fun _ _ hx => (scaledLaguerreWeight_pos (1/2) β hx.1).le)
    (fun y => -inverseQuarterStatistic N y) (upperLikelihood N β)
    ((continuousOn_inverseQuarterSum.mono (fun _ hx i => (hx i).1)).neg)
    ((continuousOn_upperLikelihood N β).mono (fun _ hx i => (hx i).1))
    (fun _ hx _ hy hxy => neg_le_neg (antitoneOn_inverseQuarterSum
      (fun i => (hx i).1) (fun i => (hy i).1) hxy)) (upperLikelihood_monotone N hb)
    hiB (by simpa only [Pi.neg_def, scaledLaguerreDensity, mul_neg, neg_mul, mul_comm] using hiBF.neg) (hiT.congr heq.symm)
    (hiTF.neg.congr heqF.symm)
  change _ ≤ _ at h
  have hprod : (∫ y in S, inverseQuarterStatistic N y * density N y) *
      (∫ y in S, scaledLaguerreDensity N (1/2) β y) ≤
      (∫ y in S, inverseQuarterStatistic N y * scaledLaguerreDensity N (1/2) β y) *
      (∫ y in S, density N y) := by
    change (∫ y in S, scaledLaguerreDensity N (1/2) β y * -inverseQuarterStatistic N y) *
      (∫ y in S, scaledLaguerreDensity N (1/2) β y * upperLikelihood N β y) ≤
      (∫ y in S, scaledLaguerreDensity N (1/2) β y) *
      (∫ y in S, scaledLaguerreDensity N (1/2) β y * (-inverseQuarterStatistic N y * upperLikelihood N β y)) at h
    rw [integral_congr_ae heq, integral_congr_ae heqF] at h
    simpa only [mul_neg, integral_neg, neg_mul, neg_le_neg_iff, mul_comm] using h
  exact (div_le_div_iff₀ (positive_cutoffNormalizer_pos N (by norm_num) (by norm_num))
    (scaledLaguerre_cutoffNormalizer_pos N (by norm_num) (by linarith) (by norm_num))).2 hprod

lemma integral_scaledLaguerre_cutoff (N : ℕ) (a R : ℝ) {β : ℝ} (hb : 0 < β) :
    laguerreDensityScale N a β *
      (∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y) =
      (β ^ N)⁻¹ * (∫ r in orderedChamber N (Ioo 0 (β * R)), laguerreDensity N a r) := by
  rw [← integral_const_mul]
  calc
    (∫ y in orderedChamber N (Ioo 0 R), laguerreDensityScale N a β * scaledLaguerreDensity N a β y) =
        ∫ y in orderedChamber N (Ioo 0 R), laguerreDensity N a (β • y) := by
      apply setIntegral_congr_fun (measurableSet_orderedChamber_Ioo N R)
      intro y hy
      exact (laguerreDensity_scaled a hb (fun i => (hy.2 i).1)).symm
    _ = _ := integral_orderedChamber_scaled R hb _

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter
lemma integral_scaledLaguerre_cutoff_inverseQuarter (N : ℕ) (a R : ℝ) {β : ℝ} (hb : 0 < β) :
    (laguerreDensityScale N a β * (β ^ (1 / 4 : ℝ))⁻¹) *
      (∫ y in orderedChamber N (Ioo 0 R), inverseQuarterStatistic N y * scaledLaguerreDensity N a β y) =
      (β ^ N)⁻¹ * (∫ r in orderedChamber N (Ioo 0 (β * R)),
        inverseQuarterStatistic N r * laguerreDensity N a r) := by
  rw [← integral_const_mul]
  calc
    (∫ y in orderedChamber N (Ioo 0 R), (laguerreDensityScale N a β * (β ^ (1 / 4 : ℝ))⁻¹) *
        (inverseQuarterStatistic N y * scaledLaguerreDensity N a β y)) =
        ∫ y in orderedChamber N (Ioo 0 R), inverseQuarterStatistic N (β • y) *
          laguerreDensity N a (β • y) := by
      apply setIntegral_congr_fun (measurableSet_orderedChamber_Ioo N R)
      intro y hy
      dsimp only [inverseQuarterStatistic]
      rw [laguerreDensity_scaled a hb (fun i => (hy.2 i).1),
        inverseQuarterSum_smul hb (fun i => (hy.2 i).1)]
      ring
    _ = _ := integral_orderedChamber_scaled R hb
      (fun r => inverseQuarterStatistic N r * laguerreDensity N a r)

lemma scaled_quotient {A Z B W c J p : ℝ} (hc : c ≠ 0) (hJ : J ≠ 0) (hp : p ≠ 0)
    (h0 : c * Z = J * W) (h1 : (c * p⁻¹) * A = J * B) :
    A / Z = p * (B / W) := by
  have hZ : Z = J * W / c := (eq_div_iff hc).2 (by simpa [mul_comm] using h0)
  have hA : A = J * B / (c * p⁻¹) := (eq_div_iff (mul_ne_zero hc (inv_ne_zero hp))).2
    (by simpa [mul_comm] using h1)
  rw [hZ, hA]
  field_simp

 

theorem scaled_reference_cutoff_inverseQuarter (N : ℕ) (a R : ℝ) {β : ℝ} (hb : 0 < β) :
    (∫ y in orderedChamber N (Ioo 0 R), inverseQuarterStatistic N y * scaledLaguerreDensity N a β y) /
      (∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y) =
      β ^ (1 / 4 : ℝ) *
        ((∫ r in orderedChamber N (Ioo 0 (β * R)), inverseQuarterStatistic N r * laguerreDensity N a r) /
          (∫ r in orderedChamber N (Ioo 0 (β * R)), laguerreDensity N a r)) := by
  exact scaled_quotient (laguerreDensityScale_pos N a hb).ne'
    (inv_ne_zero (pow_ne_zero _ hb.ne')) (Real.rpow_pos_of_pos hb _).ne'
    (integral_scaledLaguerre_cutoff N a R hb) (integral_scaledLaguerre_cutoff_inverseQuarter N a R hb)

lemma integral_positiveLaw_cutoff (N : ℕ) (R : ℝ) (f : (Fin N → ℝ) → ℝ) :
    (∫ y in cutoffEvent N R, f y ∂positiveLaw N) =
      (∫ y in orderedDomain N ∩ cutoffEvent N R, f y * density N y) / normalizer N := by
  rw [← integral_indicator (measurableSet_cutoffEvent N R), integral_positiveLaw N]
  unfold expectation
  simp_rw [← Set.indicator_mul_left]
  rw [setIntegral_indicator (measurableSet_cutoffEvent N R)]

lemma positiveLaw_conditioned_eq (N : ℕ) {R : ℝ} (hR : R ≤ 1) (f : (Fin N → ℝ) → ℝ) :
    (∫ y in cutoffEvent N R, f y ∂positiveLaw N) /
      (positiveLaw N).real (cutoffEvent N R) =
      (∫ y in orderedChamber N (Ioo 0 R), f y * density N y) /
        (∫ y in orderedChamber N (Ioo 0 R), density N y) := by
  rw [integral_positiveLaw_cutoff, positiveLaw_measureReal N (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_positive_cutoff N hR,
    div_div_div_cancel_right₀ (normalizer_pos N).ne']

lemma integral_laguerreLaw_cutoff (N : ℕ) {a : ℝ} (ha : 0 < a) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ r in cutoffEvent N R, f r ∂laguerreLaw N a) =
      (∫ r in orderedChamber N (Ioo 0 R), f r * laguerreDensity N a r) / laguerreNormalizer N a := by
  rw [orderedChamber_eq_laguerre_cutoff, ← integral_indicator (measurableSet_cutoffEvent N R),
    integral_laguerreLaw N ha]
  unfold laguerreExpectation
  simp_rw [← Set.indicator_mul_left]
  rw [setIntegral_indicator (measurableSet_cutoffEvent N R)]

lemma laguerreLaw_conditioned_eq (N : ℕ) {a : ℝ} (ha : 0 < a) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    (∫ r in cutoffEvent N R, f r ∂laguerreLaw N a) /
      (laguerreLaw N a).real (cutoffEvent N R) =
      (∫ r in orderedChamber N (Ioo 0 R), f r * laguerreDensity N a r) /
        (∫ r in orderedChamber N (Ioo 0 R), laguerreDensity N a r) := by
  rw [integral_laguerreLaw_cutoff N ha,
    laguerreLaw_measureReal N ha (measurableSet_cutoffEvent N R),
    ← orderedChamber_eq_laguerre_cutoff, div_div_div_cancel_right₀ (laguerreNormalizer_pos N ha).ne']

 

theorem positiveLaw_inverseQuarter_le_reference (N : ℕ) {β : ℝ} (hb : 4 ≤ β) :
    (∫ y, inverseQuarterStatistic N y ∂positiveLaw N) ≤
      β ^ (1 / 4 : ℝ) * (∫ r, inverseQuarterStatistic N r ∂laguerreLaw N (1 / 2)) /
        (laguerreLaw N (1 / 2)).real (cutoffEvent N (β / 2)) := by
  have hb0 : 0 < β := by linarith
  have hp := laguerreLaw_cutoff_pos N (by norm_num : (0:ℝ)<1/2) (by positivity : 0 < β / 2)
  have hcut : (∫ r in cutoffEvent N (β / 2), inverseQuarterStatistic N r ∂laguerreLaw N (1/2)) ≤
      ∫ r, inverseQuarterStatistic N r ∂laguerreLaw N (1/2) := by
    apply setIntegral_le_integral (integrable_laguerreLaw_inverseQuarterSum (by norm_num : (1/4:ℝ)<1/2))
    filter_upwards [ae_laguerreDomain N (1/2)] with r hr
    exact inverseQuarterStatistic_nonneg hr.2
  calc
    _ ≤ (∫ y in cutoffEvent N (1/2), inverseQuarterStatistic N y ∂positiveLaw N) /
        (positiveLaw N).real (cutoffEvent N (1/2)) := positiveLaw_cutoff_inverseQuarterSum (by norm_num)
    _ = (∫ y in orderedChamber N (Ioo 0 (1/2)), inverseQuarterStatistic N y * density N y) /
        (∫ y in orderedChamber N (Ioo 0 (1/2)), density N y) := positiveLaw_conditioned_eq N (by norm_num) _
    _ ≤ _ := positive_half_inverseQuarter_le_scaled_reference N hb
    _ = β ^ (1/4:ℝ) *
        ((∫ r in cutoffEvent N (β/2), inverseQuarterStatistic N r ∂laguerreLaw N (1/2)) /
          (laguerreLaw N (1/2)).real (cutoffEvent N (β/2))) := by
      rw [scaled_reference_cutoff_inverseQuarter N (1/2) (1/2) hb0,
        laguerreLaw_conditioned_eq N (by norm_num)]
      simp only [mul_one_div]
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcut hp.le)
        (Real.rpow_pos_of_pos hb0 _).le






end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InverseIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace StripPfaffian
noncomputable section
open scoped BigOperators _root_.Matrix

lemma congruence_skew {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    ∀ i j, (M * A * M.transpose) j i = -(M * A * M.transpose) i j := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [hA l k]
  ring

lemma toLin_basis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Matrix.toLin' M (standardBasis n i) = ∑ j, M j i • standardBasis n j := by
  ext k
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, standardBasis,
    Pi.basisFun_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]

lemma sum_four_reverse {ι E : Type*} [Fintype ι] [AddCommMonoid E]
    (F : ι → ι → ι → ι → E) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ l, ∑ k, ∑ j, ∑ i, F i j k l := by
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
    ⟨(fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)),
     (fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)), by intro p; rfl, by intro p; rfl⟩
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv e (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => F p.2.2.2 p.2.2.1 p.2.1 p.1) (fun _ => rfl))

lemma twoForm_congruence {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    ExteriorAlgebra.map (Matrix.toLin' M) (twoForm A) = twoForm (M * A * M.transpose) := by
  rw [twoForm_full A hA, twoForm_full _ (congruence_skew M A hA)]
  simp only [map_smul, map_sum, map_mul]
  congr 1
  simp only [generator, ExteriorAlgebra.map_apply_ι,
    toLin_basis, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, Finset.sum_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [sum_four_reverse]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

lemma pfaffian_congruence {n : ℕ} (hn : Even n) (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian n (M * A * M.transpose) = M.det * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    M.det * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_congruence M A hA, ← map_pow, topCoord_map n _ _ hhom]
  have hd : (Matrix.toLin' M).det = M.det := by
    rw [← LinearMap.det_toMatrix (standardBasis n)]
    congr 1
    ext i j
    simp [standardBasis, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hd]
  ring

lemma pfaffian_scale_coordinates {n : ℕ} (hn : Even n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (s : Fin n → ℂ) :
    pfaffian n (fun i j => s i * A i j * s j) = (∏ i, s i) * pfaffian n A := by
  have hM : Matrix.diagonal s * A * (Matrix.diagonal s).transpose =
      fun i j => s i * A i j * s j := by
    ext i j
    simp only [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simpa only [hM, Matrix.det_diagonal] using
    pfaffian_congruence hn (Matrix.diagonal s) A hA

lemma schurComplement_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u v : Vec n) (t : ℂ) :
    ∀ i j, schurComplement A u v t j i = -schurComplement A u v t i j := by
  intro i j
  simp only [schurComplement, hA i j]
  ring

lemma eliminatingShear_upper {n : ℕ} (u v : Vec n) (t : ℂ) :
    (eliminatingShear u v t).IsUpperTriangular := by
  intro i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i
  all_goals
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  all_goals
    intro hji
    simp only [id_eq] at hji
    simp_all [eliminatingShear]
  all_goals
    simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hji
    try omega

lemma eliminatingShear_det {n : ℕ} (u v : Vec n) (t : ℂ) :
    (eliminatingShear u v t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (eliminatingShear_upper u v t),
    Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp [eliminatingShear]

lemma eliminatingShear_congruence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (_hA : ∀ i j, A j i = -A i j) (u v : Vec n) {t : ℂ} (ht : t ≠ 0) :
    eliminatingShear u v t * border (border A u) (Fin.snoc v t) * (eliminatingShear u v t).transpose =
      border (border (schurComplement A u v t) 0) (Fin.snoc 0 t) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i
  all_goals
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  all_goals
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [Fin.sum_univ_castSucc]
    simp [eliminatingShear, schurComplement, ht]
  all_goals field_simp [ht]
  all_goals ring

lemma pfaffian_schur_complement {n : ℕ} (hn : Even n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j)
    (u v : Vec n) {t : ℂ} (ht : t ≠ 0) :
    pfaffian (n + 2) (border (border A u) (Fin.snoc v t)) =
      t * pfaffian n (schurComplement A u v t) := by
  have h := pfaffian_congruence (hn.add (by decide : Even 2))
    (eliminatingShear u v t) (border (border A u) (Fin.snoc v t))
    (border_skew _ (border_skew A hA u) _)
  rw [eliminatingShear_det, one_mul, eliminatingShear_congruence A hA u v ht,
    pfaffian_block_extra hn _ (schurComplement_skew A hA u v t)] at h
  exact h.symm

end

noncomputable section
open scoped BigOperators

lemma schurEntry_self (x : ℂ) : schurEntry x x = 0 := by simp [schurEntry]
lemma schurEntry_swap (x y : ℂ) : schurEntry y x = -schurEntry x y := by
  simp only [schurEntry, add_comm y x]
  ring
lemma schurMatrix_skew {n : ℕ} (x : Fin n → ℂ) :
    ∀ i j, schurMatrix x j i = -schurMatrix x i j :=
  fun i j => schurEntry_swap (x i) (x j)
lemma schurEntry_ne_zero {x y : ℂ} (hne : y ≠ x) (hd : x + y ≠ 0) :
    schurEntry x y ≠ 0 := div_ne_zero (sub_ne_zero.mpr hne) hd

lemma schurEntry_elimination {x y a b : ℂ}
    (hxy : x + y ≠ 0) (hxa : x + a ≠ 0) (hxb : x + b ≠ 0)
    (hya : y + a ≠ 0) (hyb : y + b ≠ 0) (_hab : a + b ≠ 0) (hne : b ≠ a) :
    schurEntry x y -
        (schurEntry x a * schurEntry y b - schurEntry x b * schurEntry y a) /
          schurEntry a b =
      (schurEntry x a * schurEntry x b) * schurEntry x y *
        (schurEntry y a * schurEntry y b) := by
  have hba := sub_ne_zero.mpr hne
  unfold schurEntry
  field_simp
  ring

lemma schurEntry_border_elimination {x y a : ℂ}
    (hxy : x + y ≠ 0) (hxa : x + a ≠ 0) (hya : y + a ≠ 0) :
    schurEntry x y - (schurEntry x a - schurEntry y a) =
      schurEntry x a * schurEntry x y * schurEntry y a := by
  unfold schurEntry
  field_simp
  ring

lemma schurMatrix_snoc {n : ℕ} (x : Fin n → ℂ) (a : ℂ) :
    schurMatrix (Fin.snoc x a) = border (schurMatrix x) (fun i => schurEntry (x i) a) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [schurMatrix, Fin.snoc_last, Fin.snoc_castSucc, border_last_last,
      border_last_old, border_old_last, border_old_old, schurEntry_self]
  exact schurEntry_swap _ _

lemma schurColumn_snoc {n : ℕ} (x : Fin n → ℂ) (a b : ℂ) :
    (fun i : Fin (n + 1) => schurEntry (Fin.snoc (α := fun _ => ℂ) x a i) b) =
      Fin.snoc (fun i => schurEntry (x i) b) (schurEntry a b) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

lemma schurProduct_snoc {n : ℕ} (x : Fin n → ℂ) (a : ℂ) :
    schurProduct (Fin.snoc x a) = schurProduct x * ∏ i, schurEntry (x i) a := by
  unfold schurProduct
  rw [Fin.prod_univ_castSucc, prod_Ioi_last, mul_one]
  simp_rw [prod_Ioi_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  exact Finset.prod_mul_distrib

@[simp] lemma pfaffian_empty (A : Matrix (Fin 0) (Fin 0) ℂ) : pfaffian 0 A = 1 := by
  have h := topCoord_topWedge 0
  simpa [topCoord, topWedge, ExteriorAlgebra.ιMulti_zero_apply, pfaffian,
    Module.Basis.coord_apply] using h

lemma pfaffian_schur_snoc_snoc {n : ℕ} (hn : Even n) (x : Fin n → ℂ) (a b : ℂ)
    (hbase : pfaffian n (schurMatrix x) = schurProduct x)
    (hxx : ∀ i j, x i + x j ≠ 0) (hxa : ∀ i, x i + a ≠ 0)
    (hxb : ∀ i, x i + b ≠ 0) (hab : a + b ≠ 0) (hne : b ≠ a) :
    pfaffian (n + 2) (schurMatrix (Fin.snoc (Fin.snoc x a) b)) =
      schurProduct (Fin.snoc (Fin.snoc x a) b) := by
  have hc : schurComplement (schurMatrix x) (fun i => schurEntry (x i) a)
      (fun i => schurEntry (x i) b) (schurEntry a b) =
      fun i j => (schurEntry (x i) a * schurEntry (x i) b) * schurMatrix x i j *
        (schurEntry (x j) a * schurEntry (x j) b) := by
    ext i j
    exact schurEntry_elimination (hxx i j) (hxa i) (hxb i) (hxa j) (hxb j) hab hne
  rw [schurMatrix_snoc, schurMatrix_snoc, schurColumn_snoc,
    pfaffian_schur_complement hn _ (schurMatrix_skew x) _ _ (schurEntry_ne_zero hne hab),
    hc, pfaffian_scale_coordinates hn _ (schurMatrix_skew x), hbase]
  simp only [schurProduct_snoc, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Finset.prod_mul_distrib]
  ring

 
end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SchurIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
theorem pfaffian_schur_even (n : ℕ) (hn : Even n) (x : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian n (schurMatrix x) = schurProduct x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [schurProduct]
  | one => exact False.elim (by simp at hn)
  | more n ih _ =>
    have he : Even n := by
      rw [Nat.even_iff] at *
      omega
    revert hd hx
    refine Fin.snocCases (fun y b => ?_) x
    refine Fin.snocCases (fun z a => ?_) y
    intro hd hx
    apply pfaffian_schur_snoc_snoc he z a b
    · apply ih he
      · intro i j
        simpa only [Fin.snoc_castSucc] using hd i.castSucc.castSucc j.castSucc.castSucc
      · intro i j hij
        apply Fin.castSucc_injective
        apply Fin.castSucc_injective
        apply hx
        simpa only [Fin.snoc_castSucc] using hij
    · intro i j
      simpa only [Fin.snoc_castSucc] using hd i.castSucc.castSucc j.castSucc.castSucc
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd i.castSucc.castSucc (Fin.last n).castSucc
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd i.castSucc.castSucc (Fin.last (n + 1))
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd (Fin.last n).castSucc (Fin.last (n + 1))
    · intro hab
      exact Fin.castSucc_ne_last (Fin.last n) (hx (by
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hab.symm))

lemma pfaffian_schur_odd_snoc {n : ℕ} (hn : Even n) (x : Fin n → ℂ) (a : ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x)
    (ha : ∀ i, x i + a ≠ 0) :
    pfaffian (n + 2) (border (schurMatrix (Fin.snoc x a)) (fun _ => 1)) =
      schurProduct (Fin.snoc x a) := by
  have hc : schurComplement (schurMatrix x) (fun i => schurEntry (x i) a) (fun _ => 1) 1 =
      fun i j => schurEntry (x i) a * schurMatrix x i j * schurEntry (x j) a := by
    ext i j
    simpa only [schurComplement, schurMatrix, mul_one, one_mul, div_one] using
      schurEntry_border_elimination (hd i j) (ha i) (ha j)
  have h1 : (fun _ : Fin (n + 1) => (1 : ℂ)) = Fin.snoc (fun _ => 1) 1 := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  rw [schurMatrix_snoc, h1,
    pfaffian_schur_complement hn _ (schurMatrix_skew x) _ _ one_ne_zero,
    one_mul, hc, pfaffian_scale_coordinates hn _ (schurMatrix_skew x),
    pfaffian_schur_even n hn x hd hx, schurProduct_snoc, mul_comm]

 
theorem pfaffian_schur_odd (n : ℕ) (hn : Odd n) (x : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian (n + 1) (border (schurMatrix x) (fun _ => 1)) = schurProduct x := by
  cases n with
  | zero => exact False.elim (by simp at hn)
  | succ n =>
    have he : Even n := by
      rw [Nat.odd_iff] at hn
      rw [Nat.even_iff]
      omega
    revert hd hx
    refine Fin.snocCases (fun y a => ?_) x
    intro hd hx
    apply pfaffian_schur_odd_snoc he y a
    · intro i j
      simpa only [Fin.snoc_castSucc] using hd i.castSucc j.castSucc
    · intro i j hij
      apply Fin.castSucc_injective
      apply hx
      simpa only [Fin.snoc_castSucc] using hij
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hd i.castSucc (Fin.last n)

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open MeasureTheory Set
open scoped BigOperators

lemma integral_translate_Ioi (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in Ioi a, f (x + b)) = ∫ x in Ioi (a + b), f x := by
  have hp : (fun x : ℝ => x + b) ⁻¹' Ioi (a + b) = Ioi a := by
    ext x
    simp
  simpa only [hp] using (measurePreserving_add_right volume b).setIntegral_preimage_emb
    (Homeomorph.addRight b).measurableEmbedding f (Ioi (a + b))

lemma integral_shifted_rpow {p : ℝ} (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(p + 1))) = 1 / p := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), x ^ (-(p+1)) := by
      simpa only [zero_add, add_comm] using
        integral_translate_Ioi (fun x : ℝ => x ^ (-(p+1))) 0 1
    _ = 1 / p := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -(p+1)< -1) (by norm_num : (0:ℝ)<1),
        Real.one_rpow]
      rw [show -(p+1)+1 = -p by ring, neg_div_neg_eq]

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

lemma ae_pos_pair : ∀ᵐ rs : ℝ × ℝ ∂μ₊.prod μ₊, 0 < rs.1 ∧ 0 < rs.2 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  exact (ae_restrict_mem measurableSet_Ioi).mono fun r hr =>
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => ⟨hr, hs⟩

lemma measurable_gammaLaplace (p q : ℝ) : Measurable (gammaLaplace p q) := by
  unfold gammaLaplace laguerreWeight
  fun_prop

lemma integrable_gammaLaplace_section (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun t => gammaLaplace p q ((r,s),t)) μ₊ := by
  exact (integrableOn_exp_mul_Ioi (show -(r+s) < 0 by linarith) 0).const_mul
    (laguerreWeight p r * laguerreWeight q s * r)

lemma integral_gammaLaplace_section (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ t, gammaLaplace p q ((r,s),t) ∂μ₊) =
      laguerreWeight p r * laguerreWeight q s * (r / (r+s)) := by
  simp only [gammaLaplace, integral_const_mul,
    integral_exp_mul_Ioi (show -(r+s) < 0 by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

lemma integrable_gammaFraction {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun rs : ℝ × ℝ => laguerreWeight p rs.1 * laguerreWeight q rs.2 *
      (rs.1 / (rs.1 + rs.2))) (μ₊.prod μ₊) := by
  have hi := (integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq)
  apply hi.mono' (by unfold laguerreWeight; fun_prop)
  filter_upwards [ae_pos_pair] with rs hrs
  obtain ⟨hr,hs⟩ := hrs
  have hw : 0 ≤ laguerreWeight p rs.1 * laguerreWeight q rs.2 :=
    mul_nonneg (laguerreWeight_pos p hr).le (laguerreWeight_pos q hs).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (div_nonneg hr.le (add_pos hr hs).le))]
  exact mul_le_of_le_one_right hw ((div_le_one (add_pos hr hs)).2 (by linarith))

lemma integrable_gammaLaplace {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (gammaLaplace p q) ((μ₊.prod μ₊).prod μ₊) := by
  apply (integrable_prod_iff (measurable_gammaLaplace p q).aestronglyMeasurable).2
  constructor
  · exact ae_pos_pair.mono fun rs hrs => integrable_gammaLaplace_section p q hrs.1 hrs.2
  · apply (integrable_gammaFraction hp hq).congr
    filter_upwards [ae_pos_pair] with rs hrs
    rw [← integral_gammaLaplace_section p q hrs.1 hrs.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_of_nonneg (by
      unfold gammaLaplace
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (laguerreWeight_pos p hrs.1).le (laguerreWeight_pos q hrs.2).le) hrs.1.le)
        (Real.exp_pos _).le)).symm

lemma gammaLaplace_factor (p q : ℝ) {r s : ℝ} (hr : 0 < r) (_hs : 0 < s) (t : ℝ) :
    gammaLaplace p q ((r,s),t) =
      (r ^ p * Real.exp (-((1+t)*r))) *
        (s ^ (q-1) * Real.exp (-((1+t)*s))) := by
  unfold gammaLaplace laguerreWeight
  have hrp : r^p = r^(p-1)*r := by
    calc
      _ = r ^ ((p-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr, Real.rpow_one]
  rw [hrp]
  have he : Real.exp (-r) * Real.exp (-s) * Real.exp (-(r+s)*t) =
      Real.exp (-((1+t)*r)) * Real.exp (-((1+t)*s)) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (r^(p-1) * r * s^(q-1)) *
        (Real.exp (-r) * Real.exp (-s) * Real.exp (-(r+s)*t)) := by ring
    _ = _ := by rw [he]; ring

lemma integral_gammaLaplace_pair {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (∫ rs : ℝ × ℝ, gammaLaplace p q (rs,t) ∂μ₊.prod μ₊) =
      (Real.Gamma (p+1) * Real.Gamma q) * (1+t)^(-(p+q+1)) := by
  calc
    _ = ∫ rs : ℝ × ℝ, (rs.1^p * Real.exp (-((1+t)*rs.1))) *
        (rs.2^(q-1) * Real.exp (-((1+t)*rs.2))) ∂μ₊.prod μ₊ := by
      apply integral_congr_ae
      exact ae_pos_pair.mono fun rs hrs => gammaLaplace_factor p q hrs.1 hrs.2 t
    _ = (∫ r in Ioi 0, r^p * Real.exp (-((1+t)*r))) *
        (∫ s in Ioi 0, s^(q-1) * Real.exp (-((1+t)*s))) := integral_prod_mul (μ := μ₊) (ν := μ₊)
      (fun r : ℝ => r^p * Real.exp (-((1+t)*r)))
      (fun s : ℝ => s^(q-1) * Real.exp (-((1+t)*s)))
    _ = ((1/(1+t))^(p+1) * Real.Gamma (p+1)) *
        ((1/(1+t))^q * Real.Gamma q) := by
      rw [show p = (p+1)-1 by ring, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0<p+1)
        (by linarith : 0<1+t), Real.integral_rpow_mul_exp_neg_mul_Ioi hq (by linarith : 0<1+t)]
      ring_nf
    _ = _ := by
      rw [show p+q+1 = (p+1)+q by ring, neg_add, Real.rpow_add (by linarith : 0<1+t)]
      simp only [one_div, Real.inv_rpow (by linarith : 0≤1+t), Real.rpow_neg (by linarith : 0≤1+t)]
      ring

lemma integral_gammaFraction {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 *
      (rs.1 / (rs.1+rs.2)) ∂μ₊.prod μ₊) =
      Real.Gamma p * Real.Gamma q * (p / (p+q)) := by
  calc
    _ = ∫ rs : ℝ × ℝ, ∫ t, gammaLaplace p q (rs,t) ∂μ₊ ∂μ₊.prod μ₊ := by
      apply integral_congr_ae
      exact ae_pos_pair.mono fun rs hrs => (integral_gammaLaplace_section p q hrs.1 hrs.2).symm
    _ = ∫ t, ∫ rs : ℝ × ℝ, gammaLaplace p q (rs,t) ∂μ₊.prod μ₊ ∂μ₊ :=
      integral_integral_swap (integrable_gammaLaplace hp hq)
    _ = ∫ t, (Real.Gamma (p+1) * Real.Gamma q) * (1+t)^(-(p+q+1)) ∂μ₊ := by
      apply integral_congr_ae
      exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => integral_gammaLaplace_pair hp hq ht
    _ = _ := by
      rw [integral_const_mul, integral_shifted_rpow (add_pos hp hq), Real.Gamma_add_one hp.ne']
      ring



lemma gammaSkewIntegrand_eq (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    gammaSkewIntegrand p q (r,s) =
      laguerreWeight p r * laguerreWeight q s -
        2 * (laguerreWeight p r * laguerreWeight q s * (r/(r+s))) := by
  unfold gammaSkewIntegrand
  field_simp [(add_pos hr hs).ne', (add_pos hs hr).ne']
  ring

lemma integrable_gammaSkewIntegrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (gammaSkewIntegrand p q) (μ₊.prod μ₊) := by
  have h := ((integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq)).sub
    ((integrable_gammaFraction hp hq).const_mul 2)
  exact h.congr (ae_pos_pair.mono fun rs hrs => (gammaSkewIntegrand_eq p q hrs.1 hrs.2).symm)

lemma integral_gammaSkewIntegrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ rs : ℝ × ℝ, gammaSkewIntegrand p q rs ∂μ₊.prod μ₊) =
      Real.Gamma p * Real.Gamma q * ((q-p)/(p+q)) := by
  calc
    _ = (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 ∂μ₊.prod μ₊) -
        2 * (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 *
          (rs.1/(rs.1 + rs.2)) ∂μ₊.prod μ₊) := by
      rw [← integral_const_mul, ← integral_sub
        ((integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq))
        ((integrable_gammaFraction hp hq).const_mul 2)]
      exact integral_congr_ae (ae_pos_pair.mono fun rs hrs => gammaSkewIntegrand_eq p q hrs.1 hrs.2)
    _ = _ := by
      rw [integral_prod_mul (μ := μ₊) (ν := μ₊) (laguerreWeight p) (laguerreWeight q),
        integral_laguerreWeight hp, integral_laguerreWeight hq, integral_gammaFraction hp hq]
      field_simp [(add_pos hp hq).ne']
      ring

 
theorem laguerre_double_moment {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    Integrable (gammaSkewIntegrand (a+i) (a+j)) (μ₊.prod μ₊) ∧
    (∫ rs : ℝ × ℝ, gammaSkewIntegrand (a+i) (a+j) rs ∂μ₊.prod μ₊) =
      Real.Gamma (a+i) * Real.Gamma (a+j) * (((j:ℝ)-i)/(2*a+i+j)) := by
  have hi : 0 < a+(i:ℝ) := by positivity
  have hj : 0 < a+(j:ℝ) := by positivity
  refine ⟨integrable_gammaSkewIntegrand hi hj, ?_⟩
  rw [integral_gammaSkewIntegrand hi hj]
  congr 2 <;> ring

end
end CriticalStrip

namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma border_scale_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u s : Vec n) :
    border (fun i j => s i * A i j * s j) (fun i => s i * u i) =
      fun i j => (Fin.snoc s (1:ℂ) : Vec (n+1)) i * border A u i j *
        (Fin.snoc s (1:ℂ) : Vec (n+1)) j := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  all_goals refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp [border]
  ring

lemma pfaffian_border_scale_coordinates {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (u s : Vec n) :
    pfaffian (n+1) (border (fun i j => s i * A i j * s j) (fun i => s i * u i)) =
      (∏ i, s i) * pfaffian (n+1) (border A u) := by
  rw [border_scale_coordinates, pfaffian_scale_coordinates hn.add_one _ (border_skew A hA u),
    Fin.prod_univ_castSucc]
  simp

 

theorem pfaffian_weighted_schur_even (n : ℕ) (hn : Even n) (x s : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian n (fun i j => s i * schurEntry (x i) (x j) * s j) =
      (∏ i, s i) * schurProduct x := by
  have h := pfaffian_scale_coordinates hn (schurMatrix x) (schurMatrix_skew x) s
  rw [pfaffian_schur_even n hn x hd hx] at h
  exact h

theorem pfaffian_weighted_schur_odd (n : ℕ) (hn : Odd n) (x s : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian (n+1) (border (fun i j => s i * schurEntry (x i) (x j) * s j) s) =
      (∏ i, s i) * schurProduct x := by
  have h := pfaffian_border_scale_coordinates hn (schurMatrix x) (schurMatrix_skew x)
    (fun _ => 1) s
  rw [pfaffian_schur_odd n hn x hd hx] at h
  simpa only [mul_one, schurMatrix] using h

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

lemma laguerreMomentMatrix_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    laguerreMomentMatrix n a = fun i j =>
      (Real.Gamma (a+i.val) : ℂ) *
        schurEntry ((a+i.val : ℝ) : ℂ) ((a+j.val : ℝ) : ℂ) *
          (Real.Gamma (a+j.val) : ℂ) := by
  ext i j
  rw [laguerreMomentMatrix, (laguerre_double_moment ha i.val j.val).2]
  simp only [StripPfaffian.schurEntry, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hn : ((a:ℂ)+j.val) - ((a:ℂ)+i.val) = (j.val:ℂ)-i.val := by ring
  have hd : ((a:ℂ)+i.val) + ((a:ℂ)+j.val) = 2*(a:ℂ)+i.val+j.val := by ring
  rw [hn,hd]
  ring

lemma laguerreMomentColumn_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    laguerreMomentColumn n a = fun i => (Real.Gamma (a+i.val) : ℂ) := by
  ext i
  exact congrArg Complex.ofReal (integral_laguerreWeight (by positivity))

lemma laguerre_schur_denominators {a : ℝ} (ha : 0 < a) (n : ℕ) (i j : Fin n) :
    ((a+i.val : ℝ) : ℂ) + ((a+j.val : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
  positivity

lemma laguerre_schur_injective (a : ℝ) (n : ℕ) :
    Function.Injective (fun i : Fin n => ((a+i.val : ℝ) : ℂ)) := by
  intro i j hij
  have h := Complex.ofReal_injective hij
  have he : (i.val:ℝ) = j.val := add_left_cancel h
  exact Fin.ext (Nat.cast_injective he)

lemma laguerreNormalizerProduct_eq (n : ℕ) (a : ℝ) :
    (laguerreNormalizerProduct n a : ℂ) =
      (∏ i : Fin n, (Real.Gamma (a+i.val) : ℂ)) *
        StripPfaffian.schurProduct (fun i : Fin n => ((a+i.val : ℝ) : ℂ)) := by
  simp only [laguerreNormalizerProduct, Complex.ofReal_mul, Complex.ofReal_prod,
    StripPfaffian.schurProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simp only [StripPfaffian.schurEntry, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  congr 1 <;> ring

 

theorem laguerreMomentMatrix_pfaffian_even {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : Even n) :
    StripPfaffian.pfaffian n (laguerreMomentMatrix n a) = laguerreNormalizerProduct n a := by
  rw [laguerreMomentMatrix_eq ha, laguerreNormalizerProduct_eq]
  exact pfaffian_weighted_schur_even n hn _ _ (laguerre_schur_denominators ha n)
    (laguerre_schur_injective a n)

theorem laguerreMomentMatrix_pfaffian_odd {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : Odd n) :
    StripPfaffian.pfaffian (n+1) (StripPfaffian.border (laguerreMomentMatrix n a)
      (laguerreMomentColumn n a)) = laguerreNormalizerProduct n a := by
  rw [laguerreMomentMatrix_eq ha, laguerreMomentColumn_eq ha, laguerreNormalizerProduct_eq]
  exact pfaffian_weighted_schur_odd n hn _ _ (laguerre_schur_denominators ha n)
    (laguerre_schur_injective a n)

end
end CriticalStrip

 

namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma sum_pow_list {ι E : Type*} [Fintype ι] [Semiring E] (f : ι → E) (m : ℕ) :
    (∑ i, f i) ^ m = ∑ v : Fin m → ι, (List.ofFn (fun j => f (v j))).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    conv_lhs => simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin m → ι) =>
      f p.1 * (List.ofFn (fun j => f (p.2 j))).prod)]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => ι))
    intro p
    simp [List.ofFn_succ, Fin.consEquiv]

lemma ofFn_smul_prod {n m : ℕ} (s : Fin m → ℂ) (v : Fin m → Grassmann n) :
    (List.ofFn (fun i => s i • v i)).prod =
      (∏ i, s i) • (List.ofFn v).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ih, smul_mul_smul_comm]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma pair_wedge_product {n m : ℕ} (v : Fin (m*2) → Vec n) :
    (List.ofFn (fun i : Fin m => ExteriorAlgebra.ι ℂ (v (pairLeft i)) *
      ExteriorAlgebra.ι ℂ (v (pairRight i)))).prod = ExteriorAlgebra.ιMulti ℂ (m*2) v := by
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 2
  funext i
  simp [List.ofFn_succ, pairLeft, pairRight, finProdFinEquiv, mul_comm, add_comm]

lemma twoForm_pow_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (m : ℕ) :
    twoForm A ^ m = (1/2:ℂ)^m • ∑ v : Fin (m*2) → Fin n,
      (∏ k : Fin m, A (v (pairLeft k)) (v (pairRight k))) •
        ExteriorAlgebra.ιMulti ℂ (m*2) (standardBasis n ∘ v) := by
  rw [twoForm_full A hA, smul_pow]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
    A p.1 p.2 • (generator n p.1 * generator n p.2)), sum_pow_list]
  simp_rw [ofFn_smul_prod]
  apply Fintype.sum_equiv (pairArrayEquiv (Fin n) m).symm
  intro p
  have hp : pairArrayEquiv (Fin n) m ((pairArrayEquiv (Fin n) m).symm p) = p :=
    Equiv.apply_symm_apply _ p
  conv_lhs => rw [← hp]
  simp only [pairArrayEquiv_apply, generator]
  congr 1
  exact pair_wedge_product (standardBasis n ∘ (pairArrayEquiv (Fin n) m).symm p)

lemma sum_basis_determinant (n : ℕ) (w : (Fin n → Fin n) → ℂ) :
    (∑ v : Fin n → Fin n, w v * (standardBasis n).det (standardBasis n ∘ v)) =
      ∑ σ : Equiv.Perm (Fin n), w σ * (Equiv.Perm.sign σ : ℂ) := by
  classical
  have hz : (∑ v : {f : Fin n → Fin n // ¬Function.Injective f},
      w v.val * (standardBasis n).det (standardBasis n ∘ v.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hd : (standardBasis n).det (standardBasis n ∘ v.val) = 0 := by
      apply AlternatingMap.map_eq_zero_of_not_injective
      intro hi
      exact v.property (fun a b hab => hi (by simp only [Function.comp_apply, hab]))
    rw [hd, mul_zero]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun v : Fin n → Fin n => Function.Injective v),
    hz, add_zero]
  apply Fintype.sum_equiv (permInjectiveEquiv n).symm
  intro v
  let σ := (permInjectiveEquiv n).symm v
  change w σ * (standardBasis n).det (standardBasis n ∘ σ) = w σ * _
  rw [AlternatingMap.map_perm, Module.Basis.det_self]
  simp [σ, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]



theorem pfaffian_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ) (hA : ∀ i j, A j i = -A i j) :
    pfaffian (m*2) A = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => A (σ i) (σ j)) := by
  change topCoord (m*2) (twoForm A ^ ((m*2)/2)) / _ = _
  rw [Nat.mul_div_cancel m (by norm_num : 0 < 2), twoForm_pow_expansion A hA,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold pairEntries
  simp only [mul_comm (∏ i : Fin m, _) (Equiv.Perm.sign _ : ℂ)]
  ring

end

 

noncomputable section
open scoped BigOperators
open MeasureTheory Set

lemma pairArray_preimage_pi {α : Type*} {m : ℕ} (s : Fin (m*2) → Set α) :
    (pairArrayEquiv α m).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i : Fin m => s (pairLeft i) ×ˢ s (pairRight i)) := by
  ext p
  simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
  constructor
  · intro hp i
    exact ⟨by simpa using hp (pairLeft i), by simpa using hp (pairRight i)⟩
  · intro hp j
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases j
    · change (pairArrayEquiv α m).symm p (pairLeft i) ∈ s (pairLeft i)
      simpa using (hp i).1
    · change (pairArrayEquiv α m).symm p (pairRight i) ∈ s (pairRight i)
      simpa using (hp i).2

lemma measurePreserving_pairArray {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) :
    MeasurePreserving (pairArrayMeasurableEquiv α m)
      (Measure.pi (fun _ : Fin (m*2) => μ))
        (Measure.pi (fun _ : Fin m => μ.prod μ)) := by
  suffices hs : MeasurePreserving (pairArrayMeasurableEquiv α m).symm
      (Measure.pi (fun _ : Fin m => μ.prod μ))
        (Measure.pi (fun _ : Fin (m*2) => μ)) from hs.symm
  refine ⟨(pairArrayMeasurableEquiv α m).symm.measurable, ?_⟩
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [MeasurableEquiv.map_apply]
  change (Measure.pi (fun _ : Fin m => μ.prod μ))
    ((pairArrayEquiv α m).symm ⁻¹' univ.pi s) = _
  rw [pairArray_preimage_pi, Measure.pi_pi]
  simp only [Measure.prod_prod]
  have h := finProdFinEquiv.prod_comp (fun i : Fin (m*2) => μ (s i))
  simpa only [Fintype.prod_prod_type, Fin.prod_univ_two, pairLeft, pairRight] using h

lemma integral_pair_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (f : Fin m → α × α → ℂ) :
    (∫ x : Fin (m*2) → α, ∏ i : Fin m, f i (x (pairLeft i), x (pairRight i))
      ∂Measure.pi (fun _ => μ)) = ∏ i, ∫ rs, f i rs ∂μ.prod μ := by
  rw [← integral_fintype_prod_eq_prod f (μ := fun _ : Fin m => μ.prod μ)]
  exact (measurePreserving_pairArray μ m).integral_comp' (fun p => ∏ i, f i (p i))

lemma integrable_pair_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) {f : Fin m → α × α → ℂ}
    (hf : ∀ i, Integrable (f i) (μ.prod μ)) :
    Integrable (fun x : Fin (m*2) → α => ∏ i : Fin m,
      f i (x (pairLeft i), x (pairRight i))) (Measure.pi (fun _ => μ)) := by
  exact (measurePreserving_pairArray μ m).integrable_comp_of_integrable
    (Integrable.fintype_prod hf)

lemma prod_pairs {M : Type*} [CommMonoid M] {m : ℕ} (f : Fin (m*2) → M) :
    (∏ i : Fin m, f (pairLeft i) * f (pairRight i)) = ∏ i, f i := by
  simpa only [Fintype.prod_prod_type, Fin.prod_univ_two, pairLeft, pairRight] using
    finProdFinEquiv.prod_comp f

lemma piCongrLeft_const_apply {α : Type*} [MeasurableSpace α] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ) x = x ∘ σ.symm := by
  ext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  simp [MeasurableEquiv.coe_piCongrLeft]

lemma integral_alternating_times_perm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {n : ℕ} (F G : (Fin n → α) → ℂ)
    (hF : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x)
    (σ : Equiv.Perm (Fin n)) :
    (∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ)) =
      (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ).integral_comp'
    (fun x => F x * G (x ∘ σ))
  simp only [piCongrLeft_const_apply] at h
  change (∫ x, F (x ∘ σ.symm) * G ((x ∘ σ.symm) ∘ σ) ∂Measure.pi (fun _ => μ)) = _ at h
  have hc (x : Fin n → α) : (x ∘ σ.symm) ∘ σ = x := by ext i; simp
  simp only [hc, hF, Equiv.Perm.sign_symm, mul_assoc, integral_const_mul] at h
  exact h.symm

lemma integrable_alternating_times_perm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {n : ℕ} (F G : (Fin n → α) → ℂ)
    (hF : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x)
    (hi : Integrable (fun x => F x * G x) (Measure.pi (fun _ => μ)))
    (σ : Equiv.Perm (Fin n)) :
    Integrable (fun x => F x * G (x ∘ σ)) (Measure.pi (fun _ => μ)) := by
  apply ((measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ).integrable_comp_emb
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ).measurableEmbedding).mp
  have hc (x : Fin n → α) : (x ∘ σ.symm) ∘ σ = x := by ext i; simp
  simp only [Function.comp_def, piCongrLeft_const_apply]
  change Integrable (fun x => F (x ∘ σ.symm) * G ((x ∘ σ.symm) ∘ σ)) _
  simp only [hc, hF, mul_assoc]
  exact hi.const_mul _

lemma doubleMomentMatrix_skew {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    [SigmaFinite μ] (φ : Fin n → α → ℂ) (k : α → α → ℂ)
    (hk : ∀ r s, k s r = -k r s) (i j : Fin n) :
    doubleMomentMatrix μ φ k j i = -doubleMomentMatrix μ φ k i j := by
  unfold doubleMomentMatrix
  rw [← integral_prod_swap (doubleIntegrand φ k j i), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with rs
  simp only [doubleIntegrand, Prod.fst_swap, Prod.snd_swap]
  rw [hk rs.1 rs.2]
  ring

lemma evaluationMatrix_det_perm {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det = (Equiv.Perm.sign σ : ℂ) * (evaluationMatrix φ x).det := by
  exact Matrix.det_permute' σ (evaluationMatrix φ x)

lemma product_doubleIntegrand {α : Type*} {m : ℕ} (φ : Fin (m*2) → α → ℂ)
    (k : α → α → ℂ) (σ : Equiv.Perm (Fin (m*2))) (x : Fin (m*2) → α) :
    (∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i)) (σ (pairRight i))
      (x (pairLeft i), x (pairRight i))) =
      (∏ i : Fin (m*2), φ (σ i) (x i)) * pairEntries (fun i j => k (x i) (x j)) := by
  unfold doubleIntegrand pairEntries
  rw [← prod_pairs (fun i => φ (σ i) (x i))]
  simp only [Finset.prod_mul_distrib]
  ring

lemma determinant_times_pairs {α : Type*} {m : ℕ} (φ : Fin (m*2) → α → ℂ)
    (k : α → α → ℂ) (x : Fin (m*2) → α) :
    (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j)) =
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i)) (σ (pairRight i))
          (x (pairLeft i), x (pairRight i)) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [product_doubleIntegrand]
  simp only [evaluationMatrix, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  ring

lemma integrable_determinant_times_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    Integrable (fun x => (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j)))
      (Measure.pi (fun _ => μ)) := by
  simp only [determinant_times_pairs]
  exact integrable_finsetSum _ (fun σ _ => (integrable_pair_product μ m (fun i => hi _ _)).const_mul _)

lemma integral_determinant_times_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    (∫ x, (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j))
      ∂Measure.pi (fun _ => μ)) =
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => doubleMomentMatrix μ φ k (σ i) (σ j)) := by
  simp only [determinant_times_pairs]
  rw [integral_finsetSum _ (fun σ _ => (integrable_pair_product μ m (fun i => hi _ _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul, integral_pair_product]
  rfl

 

theorem deBruijn_even {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hk : ∀ r s, k s r = -k r s)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    (∫ x, (evaluationMatrix φ x).det * pfaffian (m*2) (fun i j => k (x i) (x j))
      ∂Measure.pi (fun _ => μ)) =
        (Nat.factorial (m*2) : ℂ) * pfaffian (m*2) (doubleMomentMatrix μ φ k) := by
  let F : (Fin (m*2) → α) → ℂ := fun x => (evaluationMatrix φ x).det
  let G : (Fin (m*2) → α) → ℂ := fun x => pairEntries (fun i j => k (x i) (x j))
  have hF (σ : Equiv.Perm (Fin (m*2))) (x : Fin (m*2) → α) :
      F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x := evaluationMatrix_det_perm φ σ x
  have hI := integrable_determinant_times_pairs μ φ k hi
  have hII (σ : Equiv.Perm (Fin (m*2))) :
      Integrable (fun x => F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)))
        (Measure.pi (fun _ => μ)) := by
    have h := (integrable_alternating_times_perm μ F G hF hI σ).const_mul (Equiv.Perm.sign σ : ℂ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hpoint (x : Fin (m*2) → α) :
      F x * pfaffian (m*2) (fun i j => k (x i) (x j)) =
        ((1/2:ℂ)^m / m.factorial) *
          ∑ σ : Equiv.Perm (Fin (m*2)), F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) := by
    rw [pfaffian_permutation_expansion m _ (fun i j => hk _ _)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [F, G, Function.comp_def]
    ring
  change (∫ x, F x * pfaffian (m*2) _ ∂Measure.pi (fun _ => μ)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hII σ)]
  have he (σ : Equiv.Perm (Fin (m*2))) :
      (∫ x, F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) ∂Measure.pi (fun _ => μ)) =
        ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
    calc
      _ = (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ = _ := by
        rw [integral_alternating_times_perm μ F G hF, ← mul_assoc]
        have hs : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
          have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
            congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          exact_mod_cast hs
        rw [hs, one_mul]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    pfaffian_permutation_expansion m _ (doubleMomentMatrix_skew μ φ k hk),
    ← integral_determinant_times_pairs μ φ k hi]
  dsimp [F,G]
  ring


 


lemma borderLinear_eq_topCoord {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    borderLinear A u = topCoord n (twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u) / (n/2).factorial := by
  have hn' : 2*(n/2)+1 = n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hhom : twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u ∈
      ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hn'] using SetLike.mul_mem_graded (twoForm_pow_mem A (n/2))
      (show ExteriorAlgebra.ι ℂ u ∈ ExteriorAlgebra.exteriorPower ℂ 1 (Vec n) from by
        simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
          (LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) u))
  change topCoord (n+1) (ExteriorAlgebra.map (embedMap n) (twoForm A) ^ (n/2) *
    (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n+1) (Fin.last n))) / _ = _
  rw [← mul_assoc, ← ExteriorAlgebra.map_apply_ι, ← map_pow, ← map_mul,
    topCoord_embed_mul_last _ hhom]

lemma wedge_snoc {n l : ℕ} (v : Fin l → Vec n) (u : Vec n) :
    ExteriorAlgebra.ιMulti ℂ l v * ExteriorAlgebra.ι ℂ u =
      ExteriorAlgebra.ιMulti ℂ (l+1) (Fin.snoc v u) := by
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ', List.prod_concat,
    Fin.snoc_castSucc, Fin.snoc_last]

lemma twoForm_pow_mul_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (m : ℕ) :
    twoForm A ^ m * ExteriorAlgebra.ι ℂ u =
      (1/2:ℂ)^m • ∑ v : Fin (m*2+1) → Fin n,
      ((∏ k : Fin m, A (v (pairLeft k).castSucc) (v (pairRight k).castSucc)) *
         u (v (Fin.last (m*2)))) •
        ExteriorAlgebra.ιMulti ℂ (m*2+1) (standardBasis n ∘ v) := by
  rw [twoForm_pow_expansion A hA m, ← generator_expansion n u, smul_mul_assoc,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, generator, wedge_snoc]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : (Fin (m*2) → Fin n) × Fin n =>
    ((∏ k : Fin m, A (p.1 (pairLeft k)) (p.1 (pairRight k)))*u p.2) •
      ExteriorAlgebra.ιMulti ℂ (m*2+1) (Fin.snoc (standardBasis n ∘ p.1) (standardBasis n p.2)))]
  apply Fintype.sum_equiv ((Equiv.prodComm _ _).trans
    (Fin.snocEquiv (fun _ : Fin (m*2+1) => Fin n)))
  intro p
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def]

 
theorem pfaffian_border_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2+1)) (Fin (m*2+1)) ℂ) (hA : ∀ i j, A j i = -A i j)
    (u : Fin (m*2+1) → ℂ) :
    pfaffian (m*2+2) (border A u) = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        oddPairEntries (fun i j => A (σ i) (σ j)) (u ∘ σ) := by
  have hn : Odd (m*2+1) := ⟨m, by omega⟩
  rw [pfaffian_border hn A hA u, borderLinear_eq_topCoord hn,
    show (m*2+1)/2=m by omega, twoForm_pow_mul_expansion A hA u m,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold oddPairEntries
  simp only [Function.comp_apply, mul_comm ((∏ i : Fin m, _) * _) (Equiv.Perm.sign _ : ℂ)]
  ring

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set
lemma integral_pair_single_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (f : Fin m → α × α → ℂ) (g : α → ℂ) :
    (∫ x : Fin (m*2+1) → α, (∏ i : Fin m,
      f i (x (pairLeft i).castSucc, x (pairRight i).castSucc)) * g (x (Fin.last (m*2)))
      ∂Measure.pi (fun _ => μ)) = (∏ i, ∫ rs, f i rs ∂μ.prod μ) * ∫ t, g t ∂μ := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m*2+1) => μ)
    (Fin.last (m*2))).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last, Fin.snoc_castSucc, Fin.snoc_last, cast_eq]
  simp_rw [mul_comm _ (g _)]
  rw [integral_prod_mul (μ := μ) (ν := Measure.pi (fun _ : Fin (m*2) => μ)) g
    (fun x : Fin (m*2) → α => ∏ i, f i (x (pairLeft i), x (pairRight i))),
    integral_pair_product, mul_comm]

lemma integrable_pair_single_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) {f : Fin m → α × α → ℂ} {g : α → ℂ}
    (hf : ∀ i, Integrable (f i) (μ.prod μ)) (hg : Integrable g μ) :
    Integrable (fun x : Fin (m*2+1) → α => (∏ i : Fin m,
      f i (x (pairLeft i).castSucc, x (pairRight i).castSucc)) * g (x (Fin.last (m*2))))
      (Measure.pi (fun _ => μ)) := by
  apply (((measurePreserving_piFinSuccAbove (fun _ : Fin (m*2+1) => μ)
    (Fin.last (m*2))).symm).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m*2+1) => α)
        (Fin.last (m*2))).symm.measurableEmbedding).mp
  simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last,
    Fin.snoc_castSucc, Fin.snoc_last, cast_eq]
  simp_rw [mul_comm _ (g _)]
  exact hg.mul_prod (integrable_pair_product μ m hf)

lemma product_double_singleIntegrand {α : Type*} {m : ℕ} (φ : Fin (m*2+1) → α → ℂ)
    (k : α → α → ℂ) (g : α → ℂ) (σ : Equiv.Perm (Fin (m*2+1))) (x : Fin (m*2+1) → α) :
    (∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc)
      (x (pairLeft i).castSucc, x (pairRight i).castSucc)) *
        (φ (σ (Fin.last (m*2))) (x (Fin.last (m*2))) * g (x (Fin.last (m*2)))) =
      (∏ i : Fin (m*2+1), φ (σ i) (x i)) *
        oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x) := by
  unfold doubleIntegrand oddPairEntries
  rw [Fin.prod_univ_castSucc, ← prod_pairs (fun i => φ (σ i.castSucc) (x i.castSucc))]
  simp only [Finset.prod_mul_distrib, Function.comp_apply]
  ring

lemma determinant_times_oddPairs {α : Type*} {m : ℕ} (φ : Fin (m*2+1) → α → ℂ)
    (k : α → α → ℂ) (g : α → ℂ) (x : Fin (m*2+1) → α) :
    (evaluationMatrix φ x).det * oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x) =
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        ((∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc)
          (x (pairLeft i).castSucc, x (pairRight i).castSucc)) *
        (φ (σ (Fin.last (m*2))) (x (Fin.last (m*2))) * g (x (Fin.last (m*2))))) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [product_double_singleIntegrand]
  simp only [evaluationMatrix, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  ring

lemma integrable_determinant_times_oddPairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    Integrable (fun x => (evaluationMatrix φ x).det *
      oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)) (Measure.pi (fun _ => μ)) := by
  simp only [determinant_times_oddPairs]
  exact integrable_finsetSum _ (fun σ _ =>
    (integrable_pair_single_product μ m (fun i => hi _ _) (hs _)).const_mul _)

lemma integral_determinant_times_oddPairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    (∫ x, (evaluationMatrix φ x).det * oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)
      ∂Measure.pi (fun _ => μ)) =
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        oddPairEntries (fun i j => doubleMomentMatrix μ φ k (σ i) (σ j))
          (singleMoment μ φ g ∘ σ) := by
  simp only [determinant_times_oddPairs]
  rw [integral_finsetSum _ (fun σ _ =>
    (integrable_pair_single_product μ m (fun i => hi _ _) (hs _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul]
  congr 1
  exact integral_pair_single_product μ m
    (fun i => doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc))
    (fun t => φ (σ (Fin.last (m*2))) t * g t)

 

theorem deBruijn_odd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hk : ∀ r s, k s r = -k r s)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    (∫ x, (evaluationMatrix φ x).det *
      pfaffian (m*2+2) (border (fun i j => k (x i) (x j)) (g ∘ x))
      ∂Measure.pi (fun _ => μ)) =
        (Nat.factorial (m*2+1) : ℂ) * pfaffian (m*2+2)
          (border (doubleMomentMatrix μ φ k) (singleMoment μ φ g)) := by
  let F : (Fin (m*2+1) → α) → ℂ := fun x => (evaluationMatrix φ x).det
  let G : (Fin (m*2+1) → α) → ℂ := fun x => oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)
  have hF (σ : Equiv.Perm (Fin (m*2+1))) (x : Fin (m*2+1) → α) :
      F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x := evaluationMatrix_det_perm φ σ x
  have hI := integrable_determinant_times_oddPairs μ φ k g hi hs
  have hII (σ : Equiv.Perm (Fin (m*2+1))) :
      Integrable (fun x => F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)))
        (Measure.pi (fun _ => μ)) := by
    have h := (integrable_alternating_times_perm μ F G hF hI σ).const_mul (Equiv.Perm.sign σ : ℂ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hpoint (x : Fin (m*2+1) → α) :
      F x * pfaffian (m*2+2) (border (fun i j => k (x i) (x j)) (g ∘ x)) =
        ((1/2:ℂ)^m / m.factorial) *
          ∑ σ : Equiv.Perm (Fin (m*2+1)), F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) := by
    rw [pfaffian_border_permutation_expansion m _ (fun i j => hk _ _)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [F, G, Function.comp_def]
    ring
  change (∫ x, F x * pfaffian (m*2+2) _ ∂Measure.pi (fun _ => μ)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hII σ)]
  have he (σ : Equiv.Perm (Fin (m*2+1))) :
      (∫ x, F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) ∂Measure.pi (fun _ => μ)) =
        ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
    calc
      _ = (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ = _ := by
        rw [integral_alternating_times_perm μ F G hF, ← mul_assoc]
        have hs : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
          have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
            congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          exact_mod_cast hs
        rw [hs, one_mul]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    pfaffian_border_permutation_expansion m _ (doubleMomentMatrix_skew μ φ k hk),
    ← integral_determinant_times_oddPairs μ φ k g hi hs]
  dsimp [F,G]
  ring

end
end StripPfaffian

 

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

lemma laguerreDomain_subset_positive (n : ℕ) :
    laguerreDomain n ⊆ univ.pi (fun _ : Fin n => Ioi (0 : ℝ)) :=
  fun _ hr i _ => hr.2 i

lemma positive_product_restrict_chamber (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ₊)).restrict (laguerreDomain n) =
      volume.restrict (laguerreDomain n) := by
  rw [← Measure.restrict_pi_pi, ← volume_pi,
    Measure.restrict_restrict (isOpen_laguerreDomain n).measurableSet,
    inter_eq_left.mpr (laguerreDomain_subset_positive n)]

lemma ae_positive_product (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => μ₊), ∀ i, 0 < x i := by
  rw [← Measure.restrict_pi_pi, ← volume_pi]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)).mono
    fun _ hx i => hx i (mem_univ i)

lemma sum_ordered_indicator {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (∑ σ : Equiv.Perm (Fin n), (laguerreDomain n).indicator F (x ∘ σ)) = F x := by
  classical
  by_cases hi : Function.Injective x
  · have hs : x ∘ Tuple.sort x ∈ laguerreDomain n :=
      ⟨(Tuple.monotone_sort x).strictMono_of_injective (hi.comp (Tuple.sort x).injective),
        fun i => hx _⟩
    rw [Finset.sum_eq_single (Tuple.sort x)]
    · rw [indicator_of_mem hs, hperm]
    · intro σ hσ hne
      apply indicator_of_notMem
      intro hσs
      apply hne
      apply Equiv.ext
      intro i
      exact hi (congrFun (Tuple.unique_monotone hσs.1.monotone (Tuple.monotone_sort x)) i)
    · simp
  · rw [hzero x hi]
    apply Finset.sum_eq_zero
    intro σ hσ
    by_cases hm : x ∘ σ ∈ laguerreDomain n
    · rw [indicator_of_mem hm, hperm, hzero x hi]
    · exact indicator_of_notMem hm _

 

lemma integral_symmetric_ordered {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (hint : IntegrableOn F (laguerreDomain n)) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * ∫ x in laguerreDomain n, F x := by
  classical
  let G := (laguerreDomain n).indicator F
  have hi : Integrable G (Measure.pi (fun _ : Fin n => μ₊)) := by
    rw [integrable_indicator_iff (isOpen_laguerreDomain n).measurableSet]
    simpa only [IntegrableOn, positive_product_restrict_chamber] using hint
  have his (σ : Equiv.Perm (Fin n)) :
      Integrable (fun x => G (x ∘ σ)) (Measure.pi (fun _ : Fin n => μ₊)) := by
    simpa only [Function.comp_def, piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin n => μ₊) σ.symm).integrable_comp_of_integrable hi
  have heq (σ : Equiv.Perm (Fin n)) :
      (∫ x, G (x ∘ σ) ∂Measure.pi (fun _ : Fin n => μ₊)) =
        ∫ x in laguerreDomain n, F x := by
    have he := (measurePreserving_piCongrLeft (fun _ : Fin n => μ₊) σ.symm).integral_comp' G
    simp only [piCongrLeft_const_apply, Equiv.symm_symm] at he
    rw [he, integral_indicator (isOpen_laguerreDomain n).measurableSet,
      positive_product_restrict_chamber]
  calc
    _ = ∫ x, ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) ∂Measure.pi (fun _ => μ₊) := by
      apply integral_congr_ae
      exact (ae_positive_product n).mono fun x hx => (sum_ordered_indicator F hperm hzero x hx).symm
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ x, G (x ∘ σ) ∂Measure.pi (fun _ => μ₊) :=
      integral_finsetSum _ (fun σ _ => his σ)
    _ = _ := by simp only [heq, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end
end CriticalStrip

namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set

lemma permMap_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Vec n) :
    permMap n σ u = u ∘ σ.symm := by
  have hu : ∑ i : Fin n, u i • standardBasis n i = u := by
    simpa only [standardBasis, Pi.basisFun_repr] using (standardBasis n).sum_repr u
  calc
    _ = ∑ i : Fin n, u i • standardBasis n (σ i) := by
      conv_lhs => rw [← hu]
      simp only [map_sum, map_smul, permMap_basis]
    _ = ∑ i : Fin n, u (σ.symm i) • standardBasis n i := by
      apply Fintype.sum_equiv σ
      intro i
      simp
    _ = _ := by simpa only [standardBasis, Pi.basisFun_repr, Function.comp_apply] using
      (standardBasis n).sum_repr (u ∘ σ.symm)

lemma pfaffian_border_perm {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (u : Vec n)
    (σ : Equiv.Perm (Fin n)) :
    pfaffian (n+1) (border (fun i j => A (σ.symm i) (σ.symm j)) (u ∘ σ.symm)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian (n+1) (border A u) := by
  have hn' : 2*(n/2)+1 = n := by obtain ⟨k, hk⟩ := hn; omega
  have hhom : twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u ∈
      ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hn'] using SetLike.mul_mem_graded (twoForm_pow_mem A (n/2))
      (show ExteriorAlgebra.ι ℂ u ∈ ExteriorAlgebra.exteriorPower ℂ 1 (Vec n) from by
        simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
          (LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) u))
  erw [pfaffian_border hn _ (fun i j => hA _ _), pfaffian_border hn A hA,
    borderLinear_eq_topCoord hn, borderLinear_eq_topCoord hn,
    ← twoForm_perm A hA σ, ← permMap_apply σ u, ← ExteriorAlgebra.map_apply_ι,
    ← map_pow, ← map_mul, topCoord_map _ _ _ hhom, permMap_det]
  ring

lemma perm_sign_mul_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
  have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
    congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
  exact_mod_cast hs

lemma determinantPfaffian_symmetric_even {α : Type*} {n : ℕ} (hn : Even n)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) (hk : ∀ r s, k s r = -k r s)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det * pfaffian n (fun i j => k (x (σ i)) (x (σ j))) =
      (evaluationMatrix φ x).det * pfaffian n (fun i j => k (x i) (x j)) := by
  rw [evaluationMatrix_det_perm]
  have hp := pfaffian_perm n hn (fun i j => k (x i) (x j)) (fun i j => hk _ _) σ.symm
  simp only [Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  erw [hp]
  calc
    _ = ((Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)) *
      ((evaluationMatrix φ x).det * pfaffian n (fun i j => k (x i) (x j))) := by ring
    _ = _ := by rw [perm_sign_mul_self, one_mul]

lemma determinantPfaffian_symmetric_odd {α : Type*} {n : ℕ} (hn : Odd n)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) (g : α → ℂ) (hk : ∀ r s, k s r = -k r s)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det * pfaffian (n+1)
      (border (fun i j => k (x (σ i)) (x (σ j))) (g ∘ x ∘ σ)) =
      (evaluationMatrix φ x).det * pfaffian (n+1)
        (border (fun i j => k (x i) (x j)) (g ∘ x)) := by
  rw [evaluationMatrix_det_perm]
  have hp := pfaffian_border_perm hn (fun i j => k (x i) (x j))
    (fun i j => hk _ _) (g ∘ x) σ.symm
  simp only [Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  erw [hp]
  calc
    _ = ((Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)) *
      ((evaluationMatrix φ x).det * pfaffian (n+1)
        (border (fun i j => k (x i) (x j)) (g ∘ x))) := by ring
    _ = _ := by rw [perm_sign_mul_self, one_mul]

lemma evaluationMatrix_det_of_not_injective {α : Type*} {n : ℕ}
    (φ : Fin n → α → ℂ) {x : Fin n → α} (hx : ¬Function.Injective x) :
    (evaluationMatrix φ x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (φ r) hij)

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

lemma laguerreWeight_shift_nat (a : ℝ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerreWeight (a+i) x = laguerreWeight a x * x^i := by
  unfold laguerreWeight
  rw [show a+(i:ℝ)-1=(a-1)+(i:ℝ) by ring, Real.rpow_add hx, Real.rpow_natCast]
  ring

lemma laguerre_evaluation_determinant {n : ℕ} (a : ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    (evaluationMatrix (laguerrePhi n a) x).det =
      (∏ i, (laguerreWeight a (x i) : ℂ)) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ)) := by
  have he : evaluationMatrix (laguerrePhi n a) x =
      Matrix.of (fun i j => (laguerreWeight a (x j) : ℂ) *
        (Matrix.vandermonde (fun i => (x i : ℂ))).transpose i j) := by
    ext i j
    simp only [evaluationMatrix, laguerrePhi, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.vandermonde_apply, laguerreWeight_shift_nat a i.val (hx j),
      Complex.ofReal_mul, Complex.ofReal_pow]
  rw [he, Matrix.det_mul_row, Matrix.det_transpose, Matrix.det_vandermonde]

lemma vandermonde_schur_density (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    ((∏ i, (laguerreWeight a (x i) : ℂ)) *
      ∏ i, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ))) *
        schurProduct (fun i => (x i : ℂ)) = (laguerreDensity n a x : ℂ) := by
  simp only [laguerreDensity, Complex.ofReal_mul, Complex.ofReal_prod, mul_assoc, schurProduct]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [schurEntry, pairKernel, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (x j : ℂ) (x i : ℂ)]
  ring

lemma laguerreEvenIntegrand_eq {n : ℕ} (hn : Even n) (a : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
    laguerreEvenIntegrand n a x = laguerreDensity n a x := by
  have hd (i j : Fin n) : (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hi : Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  rw [laguerreEvenIntegrand, pfaffian_schur_even n hn _ hd hi,
    laguerre_evaluation_determinant a hx.2, vandermonde_schur_density]

lemma laguerreOddIntegrand_eq {n : ℕ} (hn : Odd n) (a : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
    laguerreOddIntegrand n a x = laguerreDensity n a x := by
  have hd (i j : Fin n) : (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hi : Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  rw [laguerreOddIntegrand, pfaffian_schur_odd n hn _ hd hi,
    laguerre_evaluation_determinant a hx.2, vandermonde_schur_density]

lemma integral_laguerreEvenIntegrand {n : ℕ} (hn : Even n) {a : ℝ} (ha : 0 < a) :
    (∫ x, laguerreEvenIntegrand n a x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * (laguerreNormalizer n a : ℂ) := by
  have he : ∀ᵐ x ∂volume.restrict (laguerreDomain n),
      laguerreEvenIntegrand n a x = (laguerreDensity n a x : ℂ) :=
    (ae_restrict_mem (isOpen_laguerreDomain n).measurableSet).mono
      fun x hx => laguerreEvenIntegrand_eq hn a hx
  rw [integral_symmetric_ordered _
    (fun σ x => determinantPfaffian_symmetric_even hn _
      (fun r s : ℝ => schurEntry r s) (fun r s => schurEntry_swap _ _) σ x)
    (fun x hx => by
      unfold laguerreEvenIntegrand
      rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul])
    (by
      have hi := (integrableOn_laguerreDensity n ha).ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (he.mono fun _ h => h.symm))]
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian
local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))
lemma integral_laguerreOddIntegrand {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a) :
    (∫ x, laguerreOddIntegrand n a x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * (laguerreNormalizer n a : ℂ) := by
  have he : ∀ᵐ x ∂volume.restrict (laguerreDomain n),
      laguerreOddIntegrand n a x = (laguerreDensity n a x : ℂ) :=
    (ae_restrict_mem (isOpen_laguerreDomain n).measurableSet).mono
      fun x hx => laguerreOddIntegrand_eq hn a hx
  rw [integral_symmetric_ordered _
    (fun σ x => determinantPfaffian_symmetric_odd hn _
      (fun r s : ℝ => schurEntry r s) (fun _ => 1) (fun r s => schurEntry_swap _ _) σ x)
    (fun x hx => by
      unfold laguerreOddIntegrand
      rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul])
    (by
      have hi := (integrableOn_laguerreDensity n ha).ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (he.mono fun _ h => h.symm))]
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

lemma laguerre_doubleIntegrand_eq {n : ℕ} (a : ℝ) (i j : Fin n) (rs : ℝ × ℝ) :
    doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j rs =
      (gammaSkewIntegrand (a+i.val) (a+j.val) rs : ℂ) := by
  simp only [doubleIntegrand, laguerrePhi, gammaSkewIntegrand, schurEntry,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (rs.2 : ℂ) (rs.1 : ℂ)]
  ring

lemma integrable_laguerre_doubleIntegrand {n : ℕ} {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    Integrable (doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j)
      (μ₊.prod μ₊) := by
  have he : doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j =
      fun rs => (gammaSkewIntegrand (a+i.val) (a+j.val) rs : ℂ) :=
    funext (laguerre_doubleIntegrand_eq a i j)
  rw [he]
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (laguerre_double_moment ha i.val j.val).1.ofReal (𝕜 := ℂ)

lemma laguerre_doubleMomentMatrix_eq {a : ℝ} (n : ℕ) :
    doubleMomentMatrix μ₊ (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) =
      laguerreMomentMatrix n a := by
  ext i j
  simp only [doubleMomentMatrix, laguerre_doubleIntegrand_eq, integral_complex_ofReal,
    laguerreMomentMatrix]

lemma laguerre_singleMoment_eq (n : ℕ) (a : ℝ) :
    singleMoment μ₊ (laguerrePhi n a) (fun _ => 1) = laguerreMomentColumn n a := by
  ext i
  simp only [singleMoment, laguerrePhi, mul_one, integral_complex_ofReal, laguerreMomentColumn]

 

theorem laguerreNormalizer_eq_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer n a = laguerreNormalizerProduct n a := by
  apply Complex.ofReal_injective
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2 := by omega
    clear hm
    subst n
    have he : Even (m*2) := ⟨m, by omega⟩
    have h := deBruijn_even μ₊ m (laguerrePhi (m*2) a)
      (fun r s : ℝ => schurEntry r s) (fun r s => schurEntry_swap _ _)
        (integrable_laguerre_doubleIntegrand ha)
    change (∫ x, laguerreEvenIntegrand (m*2) a x ∂Measure.pi (fun _ => μ₊)) = _ at h
    rw [integral_laguerreEvenIntegrand he ha, laguerre_doubleMomentMatrix_eq,
      laguerreMomentMatrix_pfaffian_even ha _ he] at h
    exact mul_left_cancel₀ (show ((m*2).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2)) h
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2+1 := by omega
    clear hm
    subst n
    have he : Odd (m*2+1) := ⟨m, by omega⟩
    have hs (i : Fin (m*2+1)) : Integrable (fun t => laguerrePhi (m*2+1) a i t * 1) μ₊ := by
      simpa only [IntegrableOn, laguerrePhi, mul_one, RCLike.ofReal_eq_complex_ofReal] using
        (integrableOn_laguerreWeight (show 0 < a+i.val by positivity)).ofReal (𝕜 := ℂ)
    have h := deBruijn_odd μ₊ m (laguerrePhi (m*2+1) a)
      (fun r s : ℝ => schurEntry r s) (fun _ => 1) (fun r s => schurEntry_swap _ _)
        (integrable_laguerre_doubleIntegrand ha) hs
    change (∫ x, laguerreOddIntegrand (m*2+1) a x ∂Measure.pi (fun _ => μ₊)) = _ at h
    rw [integral_laguerreOddIntegrand he ha, laguerre_doubleMomentMatrix_eq,
      laguerre_singleMoment_eq] at h
    rw [laguerreMomentMatrix_pfaffian_odd ha _ he] at h
    exact mul_left_cancel₀ (show ((m*2+1).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2+1)) h

end
end CriticalStrip



namespace CriticalStrip

noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian


lemma gammaSchurProduct_laguerre (n : ℕ) (a : ℝ) :
    gammaSchurProduct (fun i : Fin n => a+i.val) = laguerreNormalizerProduct n a := by
  unfold gammaSchurProduct laguerreNormalizerProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  congr 1 <;> ring


end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_QuarterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open scoped BigOperators
open Set MeasureTheory StripPfaffian

lemma orderedPairProduct_snoc {α M : Type*} [CommMonoid M] (k : α → α → M)
    {n : ℕ} (x : α) (r : Fin n → α) :
    (∏ i : Fin (n+1), ∏ j ∈ Finset.Ioi i, k ((Fin.snoc r x : Fin (n+1) → α) i) ((Fin.snoc r x : Fin (n+1) → α) j)) =
      (∏ i, ∏ j ∈ Finset.Ioi i, k (r i) (r j)) * ∏ i, k (r i) x := by
  classical
  have he {m : ℕ} (s : Fin m → α) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, k (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then k (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp [Fin.prod_univ_castSucc, Finset.prod_mul_distrib, not_lt.mpr (Fin.le_last _)]

lemma gammaSchurProduct_snoc {n : ℕ} (r : ℝ) (q : Fin n → ℝ) :
    gammaSchurProduct (Fin.snoc q r) =
      gammaSchurProduct q * Real.Gamma r * (∏ i, (r-q i)/(q i+r)) := by
  unfold gammaSchurProduct
  rw [orderedPairProduct_snoc (fun r s : ℝ => (s-r)/(r+s))]
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

lemma laguerreNormalizer_snoc_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer (n+1) a = laguerreNormalizer n a * Real.Gamma (a+n) *
      (∏ i : Fin n, ((n:ℝ)-i.val)/(2*a+i.val+n)) := by
  rw [laguerreNormalizer_eq_product _ ha,
    ← gammaSchurProduct_laguerre, laguerreNormalizer_eq_product _ ha,
    ← gammaSchurProduct_laguerre]
  have hq : (fun i : Fin (n+1) => a+i.val) = Fin.snoc (fun i => a+i.val) (a+n) := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  rw [hq, gammaSchurProduct_snoc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1 <;> ring

lemma prod_nat_sub (n : ℕ) : (∏ i : Fin n, ((n:ℝ)-i.val)) = n.factorial := by
  have he : (fun i : Fin n => (n:ℝ)-i.val) = (fun i => ((n-i.val:ℕ):ℝ)) := by
    ext i
    exact (Nat.cast_sub i.isLt.le).symm
  rw [he, ← Nat.cast_prod, Fin.prod_univ_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_self]

lemma prod_nat_add (n : ℕ) : (∏ i : Fin n, (1+(i.val:ℝ)+n)) = ((n+1).ascFactorial n:ℝ) := by
  have he : (fun i : Fin n => 1+(i.val:ℝ)+n) = (fun i => ((n+1+i.val:ℕ):ℝ)) := by
    ext i
    push_cast
    ring
  rw [he, ← Nat.cast_prod, Fin.prod_univ_eq_prod_range, ← Nat.ascFactorial_eq_prod_range]

lemma laguerreNormalizer_max_half_ratio (n : ℕ) :
    laguerreNormalizer n (1/2) / laguerreNormalizer (n+1) (1/2) * Real.Gamma (1/2+n) =
      ((n+n).choose n:ℝ) := by
  rw [laguerreNormalizer_snoc_product n (by norm_num : (0:ℝ)<1/2)]
  norm_num only
  rw [Finset.prod_div_distrib, prod_nat_sub, prod_nat_add, Nat.cast_add_choose ℝ]
  have he : (n.factorial:ℝ) * ((n+1).ascFactorial n:ℝ) = ((n+n).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial n n
  rw [← he]
  have hz : laguerreNormalizer n (1/2) ≠ 0 := (laguerreNormalizer_pos n (by norm_num)).ne'
  have hg : Real.Gamma (1/2+n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : (0:ℝ)<1/2+n)).ne'
  have hf : (n.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hF : ((n+1).ascFactorial n:ℝ) ≠ 0 := by
    have : 0 < (n+1).ascFactorial n := Nat.ascFactorial_pos n n
    exact_mod_cast this.ne'
  field_simp

lemma choose_double_le_four_pow (n : ℕ) : ((n+n).choose n:ℝ) ≤ (4:ℝ)^n := by
  have h := Nat.choose_le_two_pow (n+n) n
  have he : (2:ℕ)^(n+n) = 4^n := by rw [pow_add, ← mul_pow]; norm_num
  rw [he] at h
  exact_mod_cast h

lemma elementary_exp_half_bound (n : ℕ) :
    (4:ℝ)^n * (Real.exp (-(16*((n:ℝ)+1))/2) * 2^((1/2:ℝ)+n)) ≤ 1/4 := by
  have hh : (2:ℝ)^((1/2:ℝ)+n) ≤ (2:ℝ)^(n+1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have he : Real.exp (-8) ≤ (1/8:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<8)
      (by linarith [Real.add_one_le_exp (8:ℝ)] : 8 ≤ Real.exp 8)
  have hn : (Real.exp (-8))^(n+1) ≤ (1/8:ℝ)^(n+1) :=
    pow_le_pow_left₀ (Real.exp_nonneg _) he _
  have hexp : Real.exp (-(16*((n:ℝ)+1))/2) = (Real.exp (-8))^(n+1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (4:ℝ)^n * ((1/8:ℝ)^(n+1) * (2:ℝ)^(n+1)) := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hn hh (by positivity) (by positivity)) (by positivity)
    _ = 1/4 := by
      rw [← mul_pow, pow_succ, ← mul_assoc, ← mul_pow]
      norm_num

 

theorem laguerreLaw_max_half_uniform (n : ℕ) :
    (laguerreLaw (n+1) (1/2)).real {r | 16*((n:ℝ)+1) < r (Fin.last n)} ≤ 1/4 := by
  have h := laguerreLaw_max_tail_exp_bound n (by norm_num : (0:ℝ)<1/2)
    (by positivity : 0 ≤ 16*((n:ℝ)+1))
  have he : (laguerreNormalizer n (1/2) / laguerreNormalizer (n+1) (1/2)) *
      (Real.exp (-(16*((n:ℝ)+1))/2) * (2^((1/2:ℝ)+n)*Real.Gamma (1/2+n))) =
      ((n+n).choose n:ℝ) * (Real.exp (-(16*((n:ℝ)+1))/2) * 2^((1/2:ℝ)+n)) := by
    rw [← laguerreNormalizer_max_half_ratio]
    ring
  rw [he] at h
  calc
    _ ≤ _ := h
    _ ≤ (4:ℝ)^n * (Real.exp (-(16*((n:ℝ)+1))/2) * 2^((1/2:ℝ)+n)) :=
      mul_le_mul_of_nonneg_right (choose_double_le_four_pow n) (by positivity)
    _ ≤ _ := elementary_exp_half_bound n

end

 

noncomputable section
open scoped BigOperators
open Set MeasureTheory

lemma laguerreLaw_cutoff_half_uniform (n : ℕ) :
    (1/2:ℝ) ≤ (laguerreLaw (n+1) (1/2)).real (cutoffEvent (n+1) (32*((n:ℝ)+1))) := by
  let μ := laguerreLaw (n+1) (1/2)
  have : IsProbabilityMeasure μ := laguerreLaw_isProbabilityMeasure _ (by norm_num)
  have hsubset : (cutoffEvent (n+1) (32*((n:ℝ)+1)))ᶜ ≤ᵐ[μ]
      {r | 16*((n:ℝ)+1) < r (Fin.last n)} := by
    filter_upwards [ae_laguerreDomain (n+1) (1/2)] with r hr
    intro h
    change r ∉ cutoffEvent (n+1) (32*((n:ℝ)+1)) at h
    have hh : ¬ r (Fin.last n) < 32*((n:ℝ)+1) := by
      simpa only [mem_compl_iff, mem_cutoffEvent_iff_last hr.1.monotone] using h
    have hn := Nat.cast_nonneg (α := ℝ) n
    change 16*((n:ℝ)+1) < r (Fin.last n)
    linarith [le_of_not_gt hh]
  have hreal : μ.real (cutoffEvent (n+1) (32*((n:ℝ)+1)))ᶜ ≤
      μ.real {r | 16*((n:ℝ)+1) < r (Fin.last n)} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
  rw [measureReal_compl (measurableSet_cutoffEvent _ _), probReal_univ] at hreal
  have H := laguerreLaw_max_half_uniform n
  change μ.real {r | 16*((n:ℝ)+1) < r (Fin.last n)} ≤ 1/4 at H
  change (1/2:ℝ) ≤ μ.real (cutoffEvent (n+1) (32*((n:ℝ)+1)))
  linarith

lemma referenceUpperConstant_pos : 0 < referenceUpperConstant := by
  have hg : 0 < Real.Gamma (1/2) := Real.Gamma_pos_of_pos (by norm_num)
  dsimp [referenceUpperConstant]
  positivity

 
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MomentGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
theorem positiveLaw_inverseQuarterSum_growth_upper_oai (n : ℕ) :
    (∫ y, inverseQuarterStatistic (n+1) y ∂positiveLaw (n+1)) ≤
      (2*(64:ℝ)^(1/4:ℝ)*referenceUpperConstant) * ((n:ℝ)+1)^(3/4:ℝ) := by
  let b : ℝ := 64*((n:ℝ)+1)
  have hb : 4 ≤ b := by dsimp [b]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb0 : 0 < b := by linarith
  have hp : (1/2:ℝ) ≤ (laguerreLaw (n+1) (1/2)).real (cutoffEvent (n+1) (b/2)) := by
    have he : b/2 = 32*((n:ℝ)+1) := by dsimp [b]; ring
    rw [he]
    exact laguerreLaw_cutoff_half_uniform n
  have H := positiveLaw_inverseQuarter_le_reference (n+1) hb
  have hRef := laguerre_inverseQuarterSum_upper n
  change (∫ r, inverseQuarterStatistic (n+1) r ∂laguerreLaw (n+1) (1/2)) ≤
    referenceUpperConstant*((n:ℝ)+1)^(1/2:ℝ) at hRef
  have hbpow : 0 ≤ b^(1/4:ℝ) := (Real.rpow_pos_of_pos hb0 _).le
  calc
    _ ≤ _ := H
    _ ≤ b^(1/4:ℝ)*(referenceUpperConstant*((n:ℝ)+1)^(1/2:ℝ)) /
        (laguerreLaw (n+1) (1/2)).real (cutoffEvent (n+1) (b/2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRef hbpow) (by linarith)
    _ ≤ b^(1/4:ℝ)*(referenceUpperConstant*((n:ℝ)+1)^(1/2:ℝ)) / (1/2) :=
      div_le_div_of_nonneg_left (by positivity [referenceUpperConstant_pos]) (by norm_num) hp
    _ = _ := by
      dsimp only [b]
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤64) (by positivity)]
      have hn : 0 < (n:ℝ)+1 := by positivity
      have he : ((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ) = ((n:ℝ)+1)^(3/4:ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      calc
        _ = (2*(64:ℝ)^(1/4:ℝ)*referenceUpperConstant) *
            (((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ)) := by ring
        _ = _ := by rw [he]



end
end CriticalStrip

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.positiveLaw_inverseQuarterSum_growth_upper_oai := @OAI.CriticalStrip.positiveLaw_inverseQuarterSum_growth_upper_oai
