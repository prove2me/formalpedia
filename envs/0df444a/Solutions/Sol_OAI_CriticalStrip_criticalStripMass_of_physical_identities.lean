-- Prove2me | solution 1 for OAI.CriticalStrip.criticalStripMass_of_physical_identities
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:47:43.464265+00:00
-- url     : https://prove2.me/submissions/457e587e-1825-41dc-83e0-d1ab1361cf73

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S004
import Theorems.Thm_OAI_CriticalStrip_homogeneous_arch_coefficient_integral
import Theorems.Thm_OAI_CriticalStrip_laguerre_least_inverseQuarter_lower
import Theorems.Thm_OAI_CriticalStrip_positiveLaw_inverseQuarterSum_growth_upper

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

theorem abs_one_sub_prod_le {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, |r i| ≤ 1) : |1 - ∏ i ∈ s, r i| ≤ ∑ i ∈ s, |1 - r i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have his : ∀ j ∈ s, |r j| ≤ 1 := fun j hj => hr j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      |1 - r i * ∏ j ∈ s, r j| = |(1 - r i) + r i * (1 - ∏ j ∈ s, r j)| := by congr 1; ring
      _ ≤ |1 - r i| + |r i * (1 - ∏ j ∈ s, r j)| := abs_add_le _ _
      _ = |1 - r i| + |r i| * |1 - ∏ j ∈ s, r j| := by rw [abs_mul]
      _ ≤ |1 - r i| + 1 * |1 - ∏ j ∈ s, r j| :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (hr i (Finset.mem_insert_self _ _)) (abs_nonneg _))
      _ ≤ |1 - r i| + ∑ j ∈ s, |1 - r j| := by simpa using add_le_add (le_refl |1 - r i|) (ih his)

theorem abs_reflectionFactor_le_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |(y - x) / (y + x)| ≤ 1 := by
  apply abs_le.2
  have hxy : 0 < y + x := by linarith
  constructor
  · apply (le_div_iff₀ hxy).2
    linarith
  · apply (div_le_iff₀ hxy).2
    linarith

theorem abs_one_sub_reflectionFactor_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |1 - (y - x) / (y + x)| ≤ Real.sqrt x * y ^ (-(1 / 2 : ℝ)) := by
  have hxy : 0 < y + x := add_pos hy hx
  have hxS := Real.sq_sqrt hx.le
  have hyS := Real.sq_sqrt hy.le
  have hxsp := Real.sqrt_pos.2 hx
  have hysp := Real.sqrt_pos.2 hy
  have hAM : 2 * Real.sqrt x * Real.sqrt y ≤ x + y := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y)]
  rw [show 1 - (y - x) / (y + x) = 2 * x / (y + x) by field_simp; ring,
      abs_of_pos (div_pos (by positivity) hxy), Real.rpow_neg hy.le,
      ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hxy hysp).2
  nlinarith [mul_le_mul_of_nonneg_left hAM hxsp.le]

theorem abs_reflectionProduct_le_one {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 ≤ x) : |reflectionProduct N x y| ≤ 1 := by
  rw [reflectionProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ =>
    abs_reflectionFactor_le_one hx (hy.2 i).1)

theorem reflectionProduct_endpoint_bound {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 < x) :
    |1 - reflectionProduct N x y| ≤ Real.sqrt x * inverseHalfSum N y := by
  calc
    |1 - reflectionProduct N x y| ≤ ∑ i : Fin N, |1 - (y i - x) / (y i + x)| :=
      abs_one_sub_prod_le _ _ fun i _ => abs_reflectionFactor_le_one hx.le (hy.2 i).1
    _ ≤ ∑ i : Fin N, Real.sqrt x * (y i) ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_le_sum fun i _ => abs_one_sub_reflectionFactor_le hx (hy.2 i).1
    _ = Real.sqrt x * inverseHalfSum N y := by rw [inverseHalfSum, Finset.mul_sum]

theorem measurable_reflectionProduct (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => reflectionProduct N p.1 p.2) := by
  unfold reflectionProduct
  apply Finset.measurable_prod
  intro i _
  fun_prop

theorem integrableOn_reflectionProduct_density (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun y => reflectionProduct N x y * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y => reflectionProduct N x y * density N y) :=
    ((measurable_reflectionProduct N).comp (measurable_const.prodMk measurable_id)).mul (measurable_density N)
  apply (integrableOn_density N).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (density_pos hy)]
  exact (mul_le_mul_of_nonneg_right (abs_reflectionProduct_le_one hy hx) (density_pos hy).le).trans_eq (one_mul _)

theorem expectation_deficit (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expectation N (fun y => 1 - reflectionProduct N x y) = 1 - expectation N (reflectionProduct N x) := by
  unfold expectation
  simp only [sub_mul, one_mul]
  rw [integral_sub (integrableOn_density N) (integrableOn_reflectionProduct_density N hx)]
  rw [sub_div, show (∫ y in orderedDomain N, density N y) = normalizer N from rfl]
  rw [div_self (normalizer_pos N).ne']

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianConfluentLimit
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


theorem c_pos : 0 < c := by
  unfold c
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem archWeight_nonneg (N : ℕ) (k : ℤ) (p : List Triangle) :
    0 ≤ archWeight N k p := by
  classical
  unfold archWeight
  split_ifs
  · exact pow_nonneg rho_pos.le _
  · exact le_rfl

theorem bridgeWeight_nonneg (N : ℕ) (k : ℤ) (p : List Triangle) :
    0 ≤ bridgeWeight N k p := by
  classical
  unfold bridgeWeight
  split_ifs
  · exact pow_nonneg rho_pos.le _
  · exact le_rfl

theorem K_nonneg (N : ℕ) (k : ℤ) : 0 ≤ K N k :=
  tsum_nonneg (archWeight_nonneg N k)

theorem bridgeKernel_nonneg (N : ℕ) (k : ℤ) : 0 ≤ bridgeKernel N k :=
  tsum_nonneg (bridgeWeight_nonneg N k)

theorem bridgeMass_nonneg (N : ℕ) : 0 ≤ bridgeMass N :=
  tsum_nonneg (bridgeKernel_nonneg N)


theorem IsPath.mono {N M : ℕ} {finish : Triangle} {p : List Triangle}
    (hp : IsPath N finish p) (hNM : N ≤ M) : IsPath M finish p := by
  obtain ⟨hfirst, hlast, hsimple, hchain, hbands⟩ := hp
  exact ⟨hfirst, hlast, hsimple, hchain,
    fun v hv => (hbands v hv).trans_le hNM⟩

theorem archWeight_mono {N M : ℕ} (hNM : N ≤ M) (k : ℤ) (p : List Triangle) :
    archWeight N k p ≤ archWeight M k p := by
  classical
  by_cases hp : k ≠ 0 ∧ IsPath N (up k 0) p
  · have hp' : k ≠ 0 ∧ IsPath M (up k 0) p := ⟨hp.1, hp.2.mono hNM⟩
    simp only [archWeight, ite_eq_left hp, ite_eq_left hp', le_refl]
  · rw [archWeight, ite_eq_right hp]
    exact archWeight_nonneg M k p

 

theorem K_le_of_summable {N M : ℕ} (hNM : N ≤ M) (k : ℤ)
    (hM : Summable (archWeight M k)) : K N k ≤ K M k := by
  have hN : Summable (archWeight N k) :=
    Summable.of_nonneg_of_le (archWeight_nonneg N k) (archWeight_mono hNM k) hM
  exact Summable.tsum_le_tsum (archWeight_mono hNM k) hN hM

theorem archMass_le_of_finite {N M : ℕ} (hNM : N ≤ M) (hM : StripSumsFinite M) :
    archMass N ≤ archMass M := by
  have hk : ∀ k, K N k ≤ K M k := fun k => K_le_of_summable hNM k (hM.1 k)
  have hN : Summable (K N) :=
    Summable.of_nonneg_of_le (K_nonneg N) hk hM.2.2.1
  exact Summable.tsum_le_tsum hk hN hM.2.2.1



theorem bridgeMass_le_of_finite_and_flux {N M : ℕ} (hNM : N ≤ M)
    (hM : StripSumsFinite M)
    (hfluxN : c * archMass N + bridgeMass N = 1)
    (hfluxM : c * archMass M + bridgeMass M = 1) :
    bridgeMass M ≤ bridgeMass N := by
  have hA := mul_le_mul_of_nonneg_left (archMass_le_of_finite hNM hM) c_pos.le
  linarith

 
theorem sum_increment_bounds {M B : ℕ → ℝ} {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hB : AntitoneOn B (Set.Ici 1))
    (hinc : ∀ n : ℕ, 1 ≤ n → lo * B n ≤ M (n + 1) - M n ∧
      M (n + 1) - M n ≤ hi * B n)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a : ℕ) * lo * B b ≤ M b - M a ∧
      M b - M a ≤ (b - a : ℕ) * hi * B a := by
  have h₁ : ∑ j ∈ Finset.Ico a b, lo * B b ≤
      ∑ j ∈ Finset.Ico a b, (M (j + 1) - M j) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨haj, hjb⟩ := Finset.mem_Ico.mp hj
    exact (mul_le_mul_of_nonneg_left (hB (ha.trans haj) (ha.trans hab) hjb.le) hlo).trans
      (hinc j (ha.trans haj)).1
  have h₂ : ∑ j ∈ Finset.Ico a b, (M (j + 1) - M j) ≤
      ∑ j ∈ Finset.Ico a b, hi * B a := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨haj, _⟩ := Finset.mem_Ico.mp hj
    exact (hinc j (ha.trans haj)).2.trans
      (mul_le_mul_of_nonneg_left (hB ha (ha.trans haj) haj) hhi)
  constructor
  · simpa only [Finset.sum_Ico_sub _ hab, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_assoc] using h₁
  · simpa only [Finset.sum_Ico_sub _ hab, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_assoc] using h₂

 

theorem comparable_of_antitone_increments {M B : ℕ → ℝ} {α : ℝ}
    (hα : 0 < α)
    (hBnon : ∀ n : ℕ, 1 ≤ n → 0 ≤ B n)
    (hBsucc : ∀ n : ℕ, 1 ≤ n → B (n + 1) ≤ B n)
    (hdiff : Comparable (fun n => M (n + 1) - M n) B)
    (hM : Comparable M (fun n => (n : ℝ) ^ α)) :
    Comparable B (fun n => (n : ℝ) ^ (α - 1)) := by
  obtain ⟨loD, hiD, hloD, hhiD, hD⟩ := hdiff
  obtain ⟨loM, hiM, hloM, hhiM, hM⟩ := hM
  have hB : AntitoneOn B (Set.Ici 1) := antitoneOn_nat_Ici_of_succ_le hBsucc
  have hM1 : 0 ≤ M 1 := by
    have h := (hM 1 le_rfl).1
    norm_num at h
    exact hloM.le.trans h
  have hupper : ∀ n : ℕ, 2 ≤ n →
      B n ≤ (2 * hiM / loD) * (n : ℝ) ^ (α - 1) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := by linarith
    have hinterval := (sum_increment_bounds hloD.le hhiD.le hB hD
      (a := 1) (b := n) le_rfl hn1).1
    rw [Nat.cast_sub hn1, Nat.cast_one] at hinterval
    have hbound : ((n : ℝ) - 1) * loD * B n ≤ hiM * (n : ℝ) ^ α :=
      (hinterval.trans (sub_le_self _ hM1)).trans (hM n hn1).2
    have hnon : 0 ≤ ((n : ℝ) - 2) * (loD * B n) :=
      mul_nonneg (by linarith) (mul_nonneg hloD.le (hBnon n hn1))
    have hmul : (n : ℝ) * loD * B n ≤ 2 * hiM * (n : ℝ) ^ α := by
      nlinarith only [hbound, hnon]
    calc
      B n ≤ (2 * hiM * (n : ℝ) ^ α) / ((n : ℝ) * loD) :=
        (le_div_iff₀ (mul_pos hnpos hloD)).2 (by nlinarith only [hmul])
      _ = (2 * hiM / loD) * (n : ℝ) ^ (α - 1) := by
        rw [Real.rpow_sub hnpos, Real.rpow_one]
        field_simp
  obtain ⟨L, hLbig⟩ := exists_nat_gt (max (2 : ℝ) ((2 * hiM / loM) ^ α⁻¹))
  have hLr : (2 : ℝ) ≤ L := (le_max_left _ _).trans hLbig.le
  have hL : 2 ≤ L := by exact_mod_cast hLr
  have hscale : 2 * hiM ≤ loM * (L : ℝ) ^ α := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
      ((le_max_right _ _).trans hLbig.le) hα.le
    rw [Real.rpow_inv_rpow (by positivity) hα.ne'] at hpow
    simpa only [mul_comm] using (div_le_iff₀ hloM).mp hpow
  have hdenom : 0 < ((L : ℝ) - 1) * hiD :=
    mul_pos (by linarith) hhiD
  refine ⟨hiM / (((L : ℝ) - 1) * hiD), max (B 1) (2 * hiM / loD),
    div_pos hhiM hdenom, lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnpow : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hnpos.le _
  constructor
  · have hnLN : n ≤ L * n := by
      calc
        n = 1 * n := (one_mul n).symm
        _ ≤ L * n := Nat.mul_le_mul_right n (by omega)
    have hgrowth : hiM * (n : ℝ) ^ α ≤ M (L * n) - M n := by
      have hlarge := (hM (L * n) (hn.trans hnLN)).1
      dsimp only at hlarge
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) hnpos.le] at hlarge
      have hsmall := (hM n hn).2
      have hscale' := mul_le_mul_of_nonneg_right hscale hnpow
      nlinarith only [hlarge, hsmall, hscale']
    have hinterval := (sum_increment_bounds hloD.le hhiD.le hB hD hn hnLN).2
    rw [Nat.cast_sub hnLN, Nat.cast_mul] at hinterval
    have hbound : hiM * (n : ℝ) ^ α ≤
        B n * (((L : ℝ) - 1) * hiD * (n : ℝ)) := by
      nlinarith only [hgrowth, hinterval]
    calc
      (hiM / (((L : ℝ) - 1) * hiD)) * (n : ℝ) ^ (α - 1) =
          (hiM * (n : ℝ) ^ α) / (((L : ℝ) - 1) * hiD * (n : ℝ)) := by
        rw [Real.rpow_sub hnpos, Real.rpow_one]
        field_simp
      _ ≤ B n := (div_le_iff₀ (mul_pos hdenom hnpos)).2 hbound
  · rcases eq_or_lt_of_le hn with hn' | hn'
    · subst n
      simp
    · exact (hupper n (by omega)).trans (mul_le_mul_of_nonneg_right
        (le_max_right _ _) (Real.rpow_nonneg hnpos.le _))

 

theorem criticalStripMass_iff_four_estimates : CriticalStripMass ↔
    (∀ N : ℕ, 1 ≤ N → StripSumsFinite N) ∧
    (∀ N : ℕ, 1 ≤ N → c * archMass N + bridgeMass N = 1) ∧
    Comparable (fun N => moment (N + 1) - moment N) bridgeMass ∧
    Comparable moment (fun N => (N : ℝ) ^ (3 / 4 : ℝ)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · rintro ⟨hfinite, hflux, hinc, hmoment⟩
    have hmono : ∀ N : ℕ, 1 ≤ N → bridgeMass (N + 1) ≤ bridgeMass N := by
      intro N hN
      exact bridgeMass_le_of_finite_and_flux (Nat.le_succ N)
        (hfinite (N + 1) (by omega)) (hflux N hN) (hflux (N + 1) (by omega))
    have hbridge := comparable_of_antitone_increments (by norm_num : (0 : ℝ) < 3 / 4)
      (fun N _ => bridgeMass_nonneg N) hmono hinc hmoment
    refine ⟨hfinite, hflux, hinc, hmoment, ?_, hmono⟩
    simpa only [show (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) by norm_num] using hbridge



 
theorem reflection_deficit_bounds {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - reflectionProduct N x y ∧
    1 - reflectionProduct N x y ≤ 2 * min 1 (x * ∑ i, (y i)⁻¹) := by
  have hR := abs_reflectionProduct_le_one hy hx.le
  refine ⟨by linarith [(abs_le.mp hR).2], ?_⟩
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_min
  · linarith [(abs_le.mp hR).1]
  · calc
      1 - reflectionProduct N x y ≤ |1 - reflectionProduct N x y| := le_abs_self _
      _ ≤ ∑ i : Fin N, |1 - (y i - x) / (y i + x)| :=
        abs_one_sub_prod_le _ _ fun i _ => abs_reflectionFactor_le_one hx.le (hy.2 i).1
      _ ≤ ∑ i : Fin N, 2 * x * (y i)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        have hyi := (hy.2 i).1
        have hdenom : 0 < y i + x := add_pos hyi hx
        rw [show 1 - (y i - x) / (y i + x) = 2 * x / (y i + x) by field_simp; ring,
          abs_of_pos (div_pos (by positivity) hdenom)]
        change 2 * x / (y i + x) ≤ 2 * x / y i
        exact div_le_div_of_nonneg_left (by positivity) hyi (le_add_of_nonneg_right hx.le)
      _ = 2 * (x * ∑ i : Fin N, (y i)⁻¹) := by rw [← Finset.mul_sum]; ring

 
theorem reflection_deficit_lower {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N)
    (i : Fin N) (hsmall : ∀ j, y i ≤ y j) {x : ℝ}
    (hx : x ∈ Ioo (y i / 3) (y i / 2)) :
    (1 / 2 : ℝ) ≤ 1 - reflectionProduct N x y := by
  classical
  have hyi := (hy.2 i).1
  have hxpos : 0 < x := (by positivity : 0 < y i / 3).trans hx.1
  have hnon : ∀ j : Fin N, 0 ≤ (y j - x) / (y j + x) := by
    intro j
    exact div_nonneg (by linarith [hsmall j, hx.2]) (add_pos (hy.2 j).1 hxpos).le
  have hproduct : reflectionProduct N x y ≤ (y i - x) / (y i + x) := by
    have h := Finset.prod_le_prod_of_subset_of_le_one
      (s := {i}) (t := Finset.univ) (f := fun j : Fin N => (y j - x) / (y j + x))
      (Finset.subset_univ _) (fun j _ => hnon j)
      (fun j _ _ => (le_abs_self _).trans (abs_reflectionFactor_le_one hxpos.le (hy.2 j).1))
    simpa only [reflectionProduct, Finset.prod_singleton] using h
  have hhalf : (y i - x) / (y i + x) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (add_pos hyi hxpos)).2
    linarith [hx.1]
  linarith

 
theorem rpow_le_eight_omega {x : ℝ} (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) :
    (1 / 8 : ℝ) * x ^ (-(1 / 4 : ℝ)) ≤ omega x := by
  have hx0 := hx.1
  have hq : (3 / 2 : ℝ) ≤ (1 + x) / (2 * x) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * x)).2
    nlinarith [hx.2]
  have hqnon : 0 ≤ (1 + x) / (2 * x) := by positivity
  have hsq := Real.sq_sqrt hqnon
  have hsnon := Real.sqrt_nonneg ((1 + x) / (2 * x))
  have hs : (6 / 5 : ℝ) ≤ Real.sqrt ((1 + x) / (2 * x)) := by
    nlinarith
  have hsn : 0 ≤ Real.sqrt ((1 + x) / (2 * x)) - 1 := by linarith
  have hosq : (omega x) ^ 2 = (Real.sqrt ((1 + x) / (2 * x)) - 1) / 4 := by
    unfold omega
    nlinarith [Real.sq_sqrt hsn]
  have hsub : Real.sqrt ((1 + x) / (2 * x)) / 6 ≤
      Real.sqrt ((1 + x) / (2 * x)) - 1 := by linarith
  have hpow : ((1 / 8 : ℝ) * x ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) ≤ (omega x) ^ 4 := by
    have hcomp : Real.sqrt ((1 + x) / (2 * x)) / 24 ≤ (omega x) ^ 2 := by linarith
    have hcomp' := mul_self_le_mul_self (by positivity) hcomp
    have hquart : (1 + x) / (2 * x) / 576 ≤ (omega x) ^ 4 := by nlinarith only [hcomp', hsq]
    have hxinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.1.le
    have hqinv : x⁻¹ / 2 ≤ (1 + x) / (2 * x) := by
      calc
        x⁻¹ / 2 = 1 / (2 * x) := by ring
        _ ≤ (1 + x) / (2 * x) := div_le_div_of_nonneg_right (by linarith [hx.1]) (by positivity)
    have he : (x ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
      norm_num [Real.rpow_neg_one]
    rw [mul_pow, he]
    nlinarith only [hquart, hqinv, hxinv]
  exact (pow_le_pow_iff_left₀ (by positivity) (omega_nonneg x) (by norm_num : (4 : ℕ) ≠ 0)).mp hpow



theorem measurable_pointwiseArchIntegrand (N : ℕ) (y : Fin N → ℝ) :
    Measurable (pointwiseArchIntegrand N y) := by
  have hR : Measurable (fun x : ℝ => reflectionProduct N x y) := (measurable_reflectionProduct N).comp (measurable_id.prodMk measurable_const)
  exact ((measurable_const.sub hR).mul measurable_omega).div measurable_id

theorem pointwiseArchIntegrand_bounds {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ pointwiseArchIntegrand N y x ∧
      pointwiseArchIntegrand N y x ≤ inverseHalfSum N y * x ^ (-(3 / 4 : ℝ)) := by
  have hdef := (reflection_deficit_bounds hy hx.1).1
  have hb := (le_abs_self (1 - reflectionProduct N x y)).trans
    (reflectionProduct_endpoint_bound hy hx.1)
  have hS : 0 ≤ inverseHalfSum N y :=
    Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (hy.2 i).1 _).le
  constructor
  · exact div_nonneg (mul_nonneg hdef (omega_nonneg x)) hx.1.le
  · have hpow : Real.sqrt x * x ^ (-(1 / 4 : ℝ)) / x = x ^ (-(3 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx.1]
      calc
        x ^ (1 / 2 + -(1 / 4) : ℝ) / x = x ^ (1 / 4 : ℝ) / x ^ (1 : ℝ) := by norm_num
        _ = x ^ ((1 / 4 : ℝ) - 1) := (Real.rpow_sub hx.1 _ _).symm
        _ = _ := by norm_num
    calc
      pointwiseArchIntegrand N y x ≤ (Real.sqrt x * inverseHalfSum N y) * omega x / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (omega_nonneg x)) hx.1.le
      _ ≤ (Real.sqrt x * inverseHalfSum N y) * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (omega_le_rpow hx)
          (mul_nonneg (Real.sqrt_nonneg x) hS)) hx.1.le
      _ = inverseHalfSum N y * (Real.sqrt x * x ^ (-(1 / 4 : ℝ)) / x) := by ring
      _ = _ := by rw [hpow]

theorem integrableOn_pointwiseArchIntegrand {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) :
    IntegrableOn (pointwiseArchIntegrand N y) (Ioo 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  apply (hp.const_mul (inverseHalfSum N y)).mono'
    (measurable_pointwiseArchIntegrand N y).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pointwiseArchIntegrand_bounds hy hx).1]
  exact (pointwiseArchIntegrand_bounds hy hx).2

 
end
end CriticalStrip

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
theorem pointwiseArchIntegral_lower {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) (i : Fin N) (hsmall : ∀ j, y i ≤ y j) :
    (1 / 96 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤ pointwiseArchIntegral N y := by
  have hyi := (hy.2 i).1
  have hyi1 := (hy.2 i).2
  have hab : y i / 3 ≤ y i / 2 := by linarith
  have hsub : Ioo (y i / 3) (y i / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hint := integrableOn_pointwiseArchIntegrand hy
  have hlocal : ∀ x ∈ Ioo (y i / 3) (y i / 2),
      (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) / y i ≤ pointwiseArchIntegrand N y x := by
    intro x hx
    have hx0 : 0 < x := (hsub hx).1
    have hxi : x ≤ y i := by linarith [hx.2]
    have hr := Real.rpow_le_rpow_of_nonpos hx0 hxi (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    have homega : (1 / 8 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤ omega x :=
      (mul_le_mul_of_nonneg_left hr (by norm_num)).trans
        (rpow_le_eight_omega ⟨hx0, by linarith [hx.2]⟩)
    have hmul : (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤
        (1 - reflectionProduct N x y) * omega x := by
      calc
        (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) =
            (1 / 2 : ℝ) * ((1 / 8 : ℝ) * (y i) ^ (-(1 / 4 : ℝ))) := by ring
        _ ≤ (1 - reflectionProduct N x y) * omega x :=
          mul_le_mul (reflection_deficit_lower hy i hsmall hx) homega
            (by positivity) (reflection_deficit_bounds hy hx0).1
    exact (div_le_div_of_nonneg_left (by positivity) hx0 hxi).trans
      (div_le_div_of_nonneg_right hmul hx0.le)
  have hinterval : (1 / 96 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) ≤
      ∫ x in Ioo (y i / 3) (y i / 2), pointwiseArchIntegrand N y x := by
    have h := setIntegral_mono_on
      (show IntegrableOn (fun _ : ℝ => (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) / y i)
        (Ioo (y i / 3) (y i / 2)) from integrable_const _)
      (hint.mono_set hsub) measurableSet_Ioo hlocal
    calc
      (1 / 96 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) =
          ∫ _x in Ioo (y i / 3) (y i / 2), (1 / 16 : ℝ) * (y i) ^ (-(1 / 4 : ℝ)) / y i := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]
        field_simp
        ring
      _ ≤ _ := h
  apply hinterval.trans
  apply setIntegral_mono_set hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (pointwiseArchIntegrand_bounds hy hx).1
  · exact Filter.Eventually.of_forall hsub

 
theorem pointwiseArchIntegrand_two_majorants {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    pointwiseArchIntegrand N y x ≤
      (2 * ∑ i, (y i)⁻¹) * x ^ (-(1 / 4 : ℝ)) ∧
    pointwiseArchIntegrand N y x ≤ 2 * x ^ (-(5 / 4 : ℝ)) := by
  have hx0 := hx.1
  have hS : 0 ≤ ∑ i, (y i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hy.2 i).1.le
  have hdef := (reflection_deficit_bounds hy hx0).2
  have h₁ : 1 - reflectionProduct N x y ≤ 2 * (x * ∑ i, (y i)⁻¹) :=
    hdef.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
  have h₂ : 1 - reflectionProduct N x y ≤ (2 : ℝ) := by
    simpa only [mul_one] using hdef.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  constructor
  · calc
      pointwiseArchIntegrand N y x ≤
          (2 * (x * ∑ i, (y i)⁻¹)) * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul h₁ (omega_le_rpow hx)
          (omega_nonneg x) (by positivity)) hx0.le
      _ = _ := by field_simp
  · calc
      pointwiseArchIntegrand N y x ≤ 2 * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul h₂ (omega_le_rpow hx)
          (omega_nonneg x) (by norm_num)) hx0.le
      _ = 2 * x ^ (-(5 / 4 : ℝ)) := by
        rw [show -(5 / 4 : ℝ) = -(1 / 4 : ℝ) - 1 by norm_num,
          Real.rpow_sub hx0, Real.rpow_one]
        ring

 

theorem pointwiseArchIntegral_upper {N : ℕ} (hN : 1 ≤ N) {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) :
    pointwiseArchIntegral N y ≤ (32 / 3 : ℝ) * (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ) := by
  let S : ℝ := ∑ i, (y i)⁻¹
  let t : ℝ := S⁻¹
  have hS : 1 ≤ S := by
    let i : Fin N := ⟨0, by omega⟩
    calc
      1 ≤ (y i)⁻¹ := (one_le_inv₀ (hy.2 i).1).mpr (hy.2 i).2.le
      _ ≤ S := Finset.single_le_sum (fun j _ => inv_nonneg.mpr (hy.2 j).1.le) (Finset.mem_univ _)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have htpos : 0 < t := inv_pos.mpr hSpos
  have ht1 : t ≤ 1 := (inv_le_one₀ hSpos).mpr hS
  have hsub₁ : Ioo 0 t ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo le_rfl ht1
  have hsub₂ : Ioo t 1 ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo htpos.le le_rfl
  have hi := integrableOn_pointwiseArchIntegrand hy
  have hi₁ := hi.mono_set hsub₁
  have hi₂ := hi.mono_set hsub₂
  have hit₁ := (intervalIntegrable_iff_integrableOn_Ioo_of_le htpos.le).mpr hi₁
  have hit₂ := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht1).mpr hi₂
  have hpow₁ : S * t ^ (3 / 4 : ℝ) = S ^ (1 / 4 : ℝ) := by
    calc
      S * t ^ (3 / 4 : ℝ) = S ^ (1 : ℝ) * S ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_one, Real.rpow_neg hSpos.le, ← Real.inv_rpow hSpos.le]
      _ = S ^ ((1 : ℝ) + -(3 / 4 : ℝ)) := (Real.rpow_add hSpos _ _).symm
      _ = S ^ (1 / 4 : ℝ) := by norm_num
  have hpow₂ : t ^ (-(1 / 4 : ℝ)) = S ^ (1 / 4 : ℝ) := by
    change (S⁻¹) ^ (-(1 / 4 : ℝ)) = _
    rw [Real.inv_rpow hSpos.le, Real.rpow_neg hSpos.le, inv_inv]
  have hbound₁ : ∫ x in Ioo 0 t, pointwiseArchIntegrand N y x ≤
      (8 / 3 : ℝ) * S ^ (1 / 4 : ℝ) := by
    have hir : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (Ioo 0 t) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff htpos).mpr (by norm_num)
    calc
      ∫ x in Ioo 0 t, pointwiseArchIntegrand N y x ≤
          ∫ x in Ioo 0 t, (2 * S) * x ^ (-(1 / 4 : ℝ)) :=
        setIntegral_mono_on hi₁ (hir.const_mul _) measurableSet_Ioo
          (fun x hx => (pointwiseArchIntegrand_two_majorants hy (hsub₁ hx)).1)
      _ = (8 / 3 : ℝ) * S ^ (1 / 4 : ℝ) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le htpos.le,
          integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 4 : ℝ)))]
        norm_num only [show -(1 / 4 : ℝ) + 1 = 3 / 4 by norm_num,
          Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0), sub_zero]
        calc
          (2 * S) * (t ^ (3 / 4 : ℝ) / (3 / 4 : ℝ)) =
              (8 / 3 : ℝ) * (S * t ^ (3 / 4 : ℝ)) := by ring
          _ = _ := by rw [hpow₁]
  have hbound₂ : ∫ x in Ioo t 1, pointwiseArchIntegrand N y x ≤
      8 * S ^ (1 / 4 : ℝ) := by
    have hzero : (0 : ℝ) ∉ uIcc t 1 := by
      rw [uIcc_of_le ht1]
      intro hz
      linarith [hz.1]
    have hir' : IntervalIntegrable (fun x : ℝ => x ^ (-(5 / 4 : ℝ))) volume t 1 :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
    have hir := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht1).mp hir'
    calc
      ∫ x in Ioo t 1, pointwiseArchIntegrand N y x ≤
          ∫ x in Ioo t 1, 2 * x ^ (-(5 / 4 : ℝ)) :=
        setIntegral_mono_on hi₂ (hir.const_mul _) measurableSet_Ioo
          (fun x hx => (pointwiseArchIntegrand_two_majorants hy (hsub₂ hx)).2)
      _ = 8 * (S ^ (1 / 4 : ℝ) - 1) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le ht1,
          integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
        norm_num only [show -(5 / 4 : ℝ) + 1 = -(1 / 4 : ℝ) by norm_num,
          Real.one_rpow, hpow₂]
        ring
      _ ≤ 8 * S ^ (1 / 4 : ℝ) := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hit₁ hit₂
  rw [intervalIntegral.integral_of_le htpos.le, intervalIntegral.integral_of_le ht1,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hsplit
  change pointwiseArchIntegral N y ≤ (32 / 3 : ℝ) * S ^ (1 / 4 : ℝ)
  unfold pointwiseArchIntegral
  rw [← hsplit]
  linarith



 

theorem integrable_jointArchIntegrand (N : ℕ) :
    Integrable (fun p : ℝ × (Fin N → ℝ) =>
      pointwiseArchIntegrand N p.2 p.1 * density N p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (orderedDomain N))) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  have hm : Measurable (fun p : ℝ × (Fin N → ℝ) =>
      pointwiseArchIntegrand N p.2 p.1 * density N p.2) := by
    exact (((measurable_const.sub (measurable_reflectionProduct N)).mul
      (measurable_omega.comp measurable_fst)).div measurable_fst).mul
        ((measurable_density N).comp measurable_snd)
  apply (hp.mul_prod (integrableOn_inverseHalfSum_density N)).mono' hm.aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (isOpen_orderedDomain N).measurableSet)] with p hp
  have hb := pointwiseArchIntegrand_bounds hp.2 hp.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (density_pos hp.2).le)]
  exact (mul_le_mul_of_nonneg_right hb.2 (density_pos hp.2).le).trans_eq (by ring)

theorem integrableOn_pointwiseArchIntegral_density (N : ℕ) :
    IntegrableOn (fun y => pointwiseArchIntegral N y * density N y) (orderedDomain N) := by
  simpa only [IntegrableOn, pointwiseArchIntegral, integral_mul_const] using
    (integrable_jointArchIntegrand N).integral_prod_right

theorem expectation_pointwiseArchIntegrand (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expectation N (fun y => pointwiseArchIntegrand N y x) = momentIntegrand N x := by
  have he (y : Fin N → ℝ) :
      pointwiseArchIntegrand N y x * density N y =
        ((1 - reflectionProduct N x y) * density N y) * (omega x / x) := by
    unfold pointwiseArchIntegrand
    ring
  unfold expectation
  simp_rw [he]
  rw [integral_mul_const]
  unfold momentIntegrand
  rw [← expectation_deficit N hx]
  unfold expectation
  ring

 
theorem integral_momentIntegrand_eq_expectation (N : ℕ) :
    (∫ x in Ioo 0 1, momentIntegrand N x) = expectation N (pointwiseArchIntegral N) := by
  calc
    (∫ x in Ioo 0 1, momentIntegrand N x) =
        ∫ x in Ioo 0 1, expectation N (fun y => pointwiseArchIntegrand N y x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact (expectation_pointwiseArchIntegrand N hx.1.le).symm
    _ = (∫ x in Ioo 0 1, ∫ y in orderedDomain N,
        pointwiseArchIntegrand N y x * density N y) / normalizer N := by
      simp only [expectation, integral_div]
    _ = expectation N (pointwiseArchIntegral N) := by
      rw [integral_integral_swap (integrable_jointArchIntegrand N)]
      simp only [expectation, pointwiseArchIntegral, integral_mul_const]

 
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

theorem integrableOn_inverseQuarterCoordinate_density (N : ℕ) (i : Fin N) :
    IntegrableOn (fun y => (y i) ^ (-(1 / 4 : ℝ)) * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y : Fin N → ℝ => (y i) ^ (-(1 / 4 : ℝ)) * density N y) :=
    ((measurable_pi_apply i).pow_const _).mul (measurable_density N)
  apply (integrableOn_coordinate_weight N i).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hy.2 i).1 _).le (density_pos hy).le)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge (hy.2 i).1 (hy.2 i).2.le (by norm_num)) (density_pos hy).le

theorem expectation_mono {N : ℕ} {f g : (Fin N → ℝ) → ℝ}
    (hf : IntegrableOn (fun y => f y * density N y) (orderedDomain N))
    (hg : IntegrableOn (fun y => g y * density N y) (orderedDomain N))
    (hfg : ∀ y ∈ orderedDomain N, f y ≤ g y) : expectation N f ≤ expectation N g := by
  apply div_le_div_of_nonneg_right _ (normalizer_pos N).le
  apply setIntegral_mono_on hf hg (isOpen_orderedDomain N).measurableSet
  intro y hy
  exact mul_le_mul_of_nonneg_right (hfg y hy) (density_pos hy).le

theorem expectation_const_mul (N : ℕ) (a : ℝ) (f : (Fin N → ℝ) → ℝ) :
    expectation N (fun y => a * f y) = a * expectation N f := by
  simp only [expectation, mul_assoc, integral_const_mul, mul_div_assoc]

 

theorem integral_inverse_comparison {N : ℕ} (hN : 1 ≤ N) :
    (1 / 96 : ℝ) * expectation N (fun y => (y ⟨0, by omega⟩) ^ (-(1 / 4 : ℝ))) ≤
      (∫ x in Ioo 0 1, momentIntegrand N x) ∧
    (∫ x in Ioo 0 1, momentIntegrand N x) ≤
      (32 / 3 : ℝ) * expectation N (fun y => (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ)) := by
  let i : Fin N := ⟨0, by omega⟩
  rw [integral_momentIntegrand_eq_expectation]
  constructor
  · rw [← expectation_const_mul]
    apply expectation_mono
    · simpa only [IntegrableOn, i, mul_assoc] using (integrableOn_inverseQuarterCoordinate_density N i).const_mul (1 / 96 : ℝ)
    · exact integrableOn_pointwiseArchIntegral_density N
    · intro y hy
      apply pointwiseArchIntegral_lower hy i
      intro j
      exact hy.1.monotone (show i ≤ j by exact Nat.zero_le _)
  · rw [← expectation_const_mul]
    apply expectation_mono (integrableOn_pointwiseArchIntegral_density N)
    · simpa only [IntegrableOn, mul_assoc] using (integrableOn_inverseQuarterSum_density N).const_mul (32 / 3 : ℝ)
    · intro y hy
      exact pointwiseArchIntegral_upper hN hy

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

theorem integrable_laguerreLaw_inverse_coordinate {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) :
    Integrable (fun r => (r i) ^ (-p)) (laguerreLaw N a) :=
  integrable_laguerreLaw ha (integrableOn_laguerre_inverse_coordinate ha i hp)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TailIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory



theorem integrable_of_power_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) {b q : ℝ}
    (hb : 0 < b) (hq : 1 < q)
    (htail : ∀ t > b, μ.real {x | t < f x} ≤ b ^ q * t ^ (-q)) :
    Integrable f μ := by
  let g : ℝ → ℝ := fun t => if t ≤ b then 1 else b ^ q * t ^ (-q)
  have hg₁ : IntegrableOn g (Ioc 0 b) := by
    apply (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun _ measurableSet_Ioc
    intro t ht
    simp [g, ht.2]
  have hg₂ : IntegrableOn g (Ioi b) := by
    apply IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt
      (by linarith : -q < -1) hb).const_mul (b ^ q)) _ measurableSet_Ioi
    intro t ht
    simp [g, not_le.mpr (mem_Ioi.1 ht)]
  have hg : IntegrableOn g (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le, integrableOn_union]
    exact ⟨hg₁, hg₂⟩
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hfn).2 ?_⟩
  rw [lintegral_eq_lintegral_meas_lt μ hfn hf]
  apply lt_of_le_of_lt _ hg.lintegral_lt_top
  apply lintegral_mono
  intro t
  change μ {x | t < f x} ≤ ENNReal.ofReal (g t)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {x | t < f x})]
  apply ENNReal.ofReal_le_ofReal
  change μ.real {x | t < f x} ≤ g t
  by_cases ht : t ≤ b
  · simpa only [g, ite_eq_left ht] using (measureReal_le_one (μ := μ) (s := {x | t < f x}))
  · simpa only [g, ite_eq_right ht] using htail t (lt_of_not_ge ht)



end

noncomputable section
open scoped BigOperators
open Set MeasureTheory





theorem laguerreDomain_cons_iff {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    Fin.cons x r ∈ laguerreDomain (n + 1) ↔
      0 < x ∧ r ∈ laguerreDomain n ∧ ∀ i, x < r i := by
  simp only [laguerreDomain, mem_ofPred_eq, Fin.strictMono_cons, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  tauto

theorem pairProduct_cons {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      pairKernel ((Fin.cons x r : Fin (n + 1) → ℝ) i) ((Fin.cons x r : Fin (n + 1) → ℝ) j)) =
      (∏ j, pairKernel x (r j)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j) := by
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
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff, one_mul]

theorem laguerreDensity_cons {n : ℕ} (a x : ℝ) (r : Fin n → ℝ) :
    laguerreDensity (n + 1) a (Fin.cons x r) =
      laguerreWeight a x * laguerreDensity n a r * ∏ i, pairKernel x (r i) := by
  unfold laguerreDensity
  rw [pairProduct_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem laguerreDensity_succ_parameter {n : ℕ} (a : ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    laguerreDensity n (a + 1) r = laguerreDensity n a r * ∏ i, r i := by
  have he : ∀ i, laguerreWeight (a + 1) (r i) = laguerreWeight a (r i) * r i := by
    intro i
    unfold laguerreWeight
    rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add (hr i), Real.rpow_one]
    ring
  simp only [laguerreDensity, he, Finset.prod_mul_distrib]
  ring

theorem laguerreDensity_cons_le {n : ℕ} (a : ℝ) {x : ℝ} {r : Fin n → ℝ}
    (hr : Fin.cons x r ∈ laguerreDomain (n + 1)) :
    laguerreDensity (n + 1) a (Fin.cons x r) ≤
      x ^ (a - 1) * laguerreDensity n (a + 1) r := by
  obtain ⟨hx, hr, hxr⟩ := (laguerreDomain_cons_iff x r).1 hr
  rw [laguerreDensity_cons, laguerreDensity_succ_parameter a r hr.2]
  have hw : laguerreWeight a x ≤ x ^ (a - 1) := by
    apply mul_le_of_le_one_right (Real.rpow_pos_of_pos hx _).le
    exact Real.exp_le_one_iff.2 (by linarith)
  have hp : (∏ i, pairKernel x (r i)) ≤ ∏ i, r i := by
    apply Finset.prod_le_prod
    · intro i _
      exact pairKernel_nonneg hx.le (hr.2 i).le
    · intro i _
      exact pairKernel_le_right hx.le (hr.2 i) (hxr i).le
  calc
    _ ≤ (x ^ (a - 1) * laguerreDensity n a r) * ∏ i, r i :=
      mul_le_mul (mul_le_mul_of_nonneg_right hw (laguerreDensity_pos a hr).le) hp
        (Finset.prod_nonneg fun i _ => pairKernel_nonneg hx.le (hr.2 i).le)
        (mul_nonneg (Real.rpow_pos_of_pos hx _).le (laguerreDensity_pos a hr).le)
    _ = _ := by ring


theorem measurableSet_laguerreCut (n k : ℕ) (h : ℝ) :
    MeasurableSet (laguerreCut n k h) := by
  apply (isOpen_laguerreDomain n).measurableSet.inter
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) measurable_const

theorem laguerreCut_zero (n : ℕ) (h : ℝ) : laguerreCut n 0 h = laguerreDomain n := by
  ext r
  simp [laguerreCut]

theorem integral_fin_cons_eq (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ r, f r) = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).integral_comp' f

theorem integrable_fin_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).integrable_comp_of_integrable hf

theorem integral_Ioo_rpow_sub_one {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    (∫ x in Ioo 0 h, x ^ (a - 1)) = h ^ a / a := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hh.le,
    integral_rpow (Or.inl (by linarith : -1 < a - 1))]
  simp [Real.zero_rpow ha.ne']

theorem integrable_laguerreCut_indicator (n : ℕ) {a : ℝ} (ha : 0 < a) (k : ℕ) (h : ℝ) :
    Integrable ((laguerreCut n k h).indicator (laguerreDensity n a)) := by
  apply (integrable_indicator_iff (measurableSet_laguerreCut n k h)).2
  exact (integrableOn_laguerreDensity n ha).mono_set inter_subset_left

theorem laguerreCut_indicator_nonneg (n : ℕ) (a : ℝ) (k : ℕ) (h : ℝ) (r : Fin n → ℝ) :
    0 ≤ (laguerreCut n k h).indicator (laguerreDensity n a) r := by
  by_cases hr : r ∈ laguerreCut n k h
  · rw [Set.indicator_of_mem hr]
    exact (laguerreDensity_pos a hr.1).le
  · rw [Set.indicator_of_notMem hr]

 

theorem laguerreCutIntegral_succ_le (n k : ℕ) {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    laguerreCutIntegral (n + 1) a (k + 1) h ≤
      (h ^ a / a) * laguerreCutIntegral n (a + 1) k h := by
  let f : ℝ → ℝ := (Ioo 0 h).indicator (fun x => x ^ (a - 1))
  let g : (Fin n → ℝ) → ℝ := (laguerreCut n k h).indicator (laguerreDensity n (a + 1))
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioo).2
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hh).2 (by linarith))
  have hgi : Integrable g := integrable_laguerreCut_indicator n (by linarith) k h
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : x ∈ Ioo 0 h
    · simpa only [f, indicator_of_mem hx] using (Real.rpow_pos_of_pos hx.1 (a - 1)).le
    · simp only [f, indicator_of_notMem hx, le_refl]
  have hn (p : ℝ × (Fin n → ℝ)) :
      (laguerreCut (n + 1) (k + 1) h).indicator (laguerreDensity (n + 1) a)
        (Fin.cons p.1 p.2) ≤ f p.1 * g p.2 := by
    by_cases hp : Fin.cons p.1 p.2 ∈ laguerreCut (n + 1) (k + 1) h
    · have hm := (laguerreDomain_cons_iff p.1 p.2).1 hp.1
      have hx : p.1 ∈ Ioo 0 h := ⟨hm.1, by simpa using hp.2 0 (by simp)⟩
      have hr : p.2 ∈ laguerreCut n k h := ⟨hm.2.1, fun i hi => by
        simpa using hp.2 i.succ (by simpa using hi)⟩
      simpa only [f, g, indicator_of_mem hp, indicator_of_mem hx, indicator_of_mem hr] using
        laguerreDensity_cons_le a hp.1
    · rw [indicator_of_notMem hp]
      exact mul_nonneg (hfn _) (laguerreCut_indicator_nonneg n (a + 1) k h _)
  calc
    laguerreCutIntegral (n + 1) a (k + 1) h =
        ∫ p : ℝ × (Fin n → ℝ), (laguerreCut (n + 1) (k + 1) h).indicator
          (laguerreDensity (n + 1) a) (Fin.cons p.1 p.2) := by
      rw [laguerreCutIntegral, ← integral_indicator (measurableSet_laguerreCut _ _ _), integral_fin_cons_eq]
    _ ≤ ∫ p : ℝ × (Fin n → ℝ), f p.1 * g p.2 :=
      integral_mono (integrable_fin_cons (integrable_laguerreCut_indicator _ ha _ _))
        (hfi.mul_prod hgi) hn
    _ = (∫ x, f x) * ∫ r, g r := integral_prod_mul f g
    _ = (h ^ a / a) * laguerreCutIntegral n (a + 1) k h := by
      simp only [f, g, integral_indicator measurableSet_Ioo,
        integral_Ioo_rpow_sub_one ha hh, integral_indicator (measurableSet_laguerreCut n k h),
        laguerreCutIntegral]

 
theorem laguerreCutIntegral_le_product (n k : ℕ) {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) :
    laguerreCutIntegral (n + k) a k h ≤
      (∏ i : Fin k, h ^ (a + i.val) / (a + i.val)) * laguerreNormalizer n (a + k) := by
  induction k generalizing a with
  | zero => simp [laguerreCutIntegral, laguerreCut_zero, laguerreNormalizer]
  | succ k ih =>
    calc
      _ ≤ (h ^ a / a) * laguerreCutIntegral (n + k) (a + 1) k h :=
        laguerreCutIntegral_succ_le (n + k) k ha hh
      _ ≤ (h ^ a / a) * ((∏ i : Fin k, h ^ (a + 1 + i.val) / (a + 1 + i.val)) *
          laguerreNormalizer n (a + 1 + k)) :=
        mul_le_mul_of_nonneg_left (ih (by linarith)) (by positivity)
      _ = _ := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        simp_rw [show ∀ i : Fin k, a + 1 + i.val = a + (i.val + 1) by intro i; ring]
        rw [show a + 1 + (k : ℝ) = a + (k + 1) by ring]
        ring


theorem laguerreDimension_succ (a : ℝ) (k : ℕ) :
    laguerreDimension a (k + 1) = a + laguerreDimension (a + 1) k := by
  simp only [laguerreDimension, Nat.cast_add, Nat.cast_one]
  ring

theorem product_coordinate_power_quotient (k : ℕ) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    (∏ i : Fin k, h ^ (a + i.val) / (a + i.val)) =
      h ^ (laguerreDimension a k) / ∏ i : Fin k, (a + i.val) := by
  induction k generalizing a with
  | zero => simp [laguerreDimension]
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    simp_rw [show ∀ i : Fin k, a + (i.val + 1) = a + 1 + i.val by intro i; ring]
    rw [ih (a + 1), ← mul_div_mul_comm, ← Real.rpow_add hh, laguerreDimension_succ]

theorem laguerreCutIntegral_le_normalizer_ratio (n k : ℕ) {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) :
    laguerreCutIntegral (n + k) a k h ≤
      (h ^ laguerreDimension a k / ∏ i : Fin k, (a + i.val)) * laguerreNormalizer n (a + k) := by
  simpa only [product_coordinate_power_quotient k hh a] using
    laguerreCutIntegral_le_product n k ha hh

theorem laguerreCut_eq_coordinate_cut {n : ℕ} (i : Fin n) (h : ℝ) :
    laguerreCut n (i.val + 1) h = laguerreDomain n ∩ {r | r i < h} := by
  ext r
  constructor
  · intro hr
    exact ⟨hr.1, hr.2 i (by omega)⟩
  · rintro ⟨hr, hi⟩
    refine ⟨hr, fun j hj => ?_⟩
    exact lt_of_le_of_lt (hr.1.monotone (by change j.val ≤ i.val; omega)) hi

theorem laguerreLaw_small_coordinate_eq {n : ℕ} {a : ℝ} (ha : 0 < a)
    (i : Fin n) (h : ℝ) :
    (laguerreLaw n a).real {r | r i < h} =
      laguerreCutIntegral n a (i.val + 1) h / laguerreNormalizer n a := by
  have hm : MeasurableSet {r : Fin n → ℝ | r i < h} :=
    measurableSet_lt (measurable_pi_apply i) measurable_const
  rw [← integral_indicator_one hm, integral_laguerreLaw n ha]
  unfold laguerreExpectation laguerreCutIntegral
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hm, laguerreCut_eq_coordinate_cut]

 

theorem laguerreLaw_small_coordinate_le_normalizer_ratio {N : ℕ} {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (i : Fin N) :
    (laguerreLaw N a).real {r | r i < h} ≤
      h ^ laguerreDimension a (i.val + 1) /
        (∏ j : Fin (i.val + 1), (a + j.val)) *
      (laguerreNormalizer (N - (i.val + 1)) (a + (i.val + 1)) / laguerreNormalizer N a) := by
  rw [laguerreLaw_small_coordinate_eq ha i h]
  have H := laguerreCutIntegral_le_normalizer_ratio (N - (i.val + 1)) (i.val + 1) ha hh
  have hN : N - (i.val + 1) + (i.val + 1) = N := by omega
  rw [hN] at H
  have hh' := div_le_div_of_nonneg_right H (laguerreNormalizer_pos N ha).le
  simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using hh'



theorem laguerreSmallCoefficient_pos (N k : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < laguerreSmallCoefficient N a k := by
  apply div_pos (laguerreNormalizer_pos _ (by positivity))
  exact mul_pos (laguerreNormalizer_pos _ ha) (Finset.prod_pos fun j _ => by positivity)

theorem laguerreDimension_pos {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    0 < laguerreDimension a k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold laguerreDimension
  have hp : 0 < a * (k : ℝ) := mul_pos ha (by linarith)
  have hq : 0 ≤ (k : ℝ) * (k - 1) := mul_nonneg (by positivity) (by linarith)
  linarith

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
theorem laguerreLaw_small_coordinate_le {N : ℕ} {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (i : Fin N) :
    (laguerreLaw N a).real {r | r i < h} ≤
      min 1 (laguerreSmallCoefficient N a (i.val + 1) *
        h ^ laguerreDimension a (i.val + 1)) := by
  let := laguerreLaw_isProbabilityMeasure N ha
  refine le_min (measureReal_le_one (μ := laguerreLaw N a)) ?_
  have H := laguerreLaw_small_coordinate_le_normalizer_ratio ha hh i
  apply H.trans_eq
  simp only [laguerreSmallCoefficient, Nat.cast_add, Nat.cast_one]
  ring

theorem laguerreLaw_small_coordinate_power_bound {N : ℕ} {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (i : Fin N) :
    (laguerreLaw N a).real {r | r i < h} ≤
      (laguerreSmallCoefficient N a (i.val + 1) ^
        (1 / laguerreDimension a (i.val + 1)) * h) ^ laguerreDimension a (i.val + 1) := by
  have hb := laguerreSmallCoefficient_pos N (i.val + 1) ha
  have hD := laguerreDimension_pos ha (show 1 ≤ i.val + 1 by omega)
  have H := (laguerreLaw_small_coordinate_le ha hh i).trans (min_le_right _ _)
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hb _).le hh.le,
    ← Real.rpow_mul hb.le, one_div_mul_cancel hD.ne', Real.rpow_one]
  exact H

 

theorem integrable_inverse_of_small_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ}
    (hX : ∀ᵐ x ∂μ, 0 < X x) {A D p : ℝ} (hA : 0 < A) (hp : 0 < p)
    (hpD : p < D) (hXm : AEMeasurable X μ)
    (htail : ∀ h > 0, μ.real {x | X x < h} ≤ (A * h) ^ D) :
    Integrable (fun x => (X x) ^ (-p)) μ := by
  have hq : 1 < D / p := (lt_div_iff₀ hp).2 (by simpa using hpD)
  have hnn : 0 ≤ᵐ[μ] (fun x => (X x) ^ (-p)) := by
    filter_upwards [hX] with x hx
    exact (Real.rpow_pos_of_pos hx _).le
  apply integrable_of_power_tail (hXm.pow_const _) hnn (Real.rpow_pos_of_pos hA p) hq
  intro t ht
  have htpos : 0 < t := (Real.rpow_pos_of_pos hA p).trans ht
  have htpow : 0 < t ^ (-1 / p) := Real.rpow_pos_of_pos htpos _
  have hsets : {x | t < (X x) ^ (-p)} =ᵐ[μ] {x | X x < t ^ (-1 / p)} := by
    filter_upwards [hX] with x hx
    have hh := Real.rpow_lt_rpow_iff_of_neg htpow hx (by linarith : -p < 0)
    rw [← Real.rpow_mul htpos.le, show (-1 / p) * -p = (1 : ℝ) by field_simp, Real.rpow_one] at hh
    exact propext hh
  have hmeas : μ.real {x | t < (X x) ^ (-p)} = μ.real {x | X x < t ^ (-1 / p)} :=
    congrArg ENNReal.toReal (measure_congr hsets)
  rw [hmeas]
  calc
    _ ≤ (A * t ^ (-1 / p)) ^ D := htail _ htpow
    _ = (A ^ p) ^ (D / p) * t ^ (-(D / p)) := by
      rw [Real.mul_rpow hA.le htpow.le, ← Real.rpow_mul htpos.le, ← Real.rpow_mul hA.le,
        show p * (D / p) = D by field_simp,
        show (-1 / p) * D = -(D / p) by ring]

 
theorem integrable_laguerreLaw_inverse_coordinate_full {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hpD : p < laguerreDimension a (i.val + 1)) :
    Integrable (fun r => (r i) ^ (-p)) (laguerreLaw N a) := by
  by_cases hp : 0 < p
  · let := laguerreLaw_isProbabilityMeasure N ha
    apply integrable_inverse_of_small_tail (D := laguerreDimension a (i.val + 1))
      (A := laguerreSmallCoefficient N a (i.val + 1) ^ (1 / laguerreDimension a (i.val + 1)))
      ?_ (Real.rpow_pos_of_pos (laguerreSmallCoefficient_pos _ _ ha) _) hp hpD
      (measurable_pi_apply i).aemeasurable
      (fun h hh => laguerreLaw_small_coordinate_power_bound ha hh i)
    filter_upwards [ae_laguerreDomain N a] with r hr
    exact hr.2 i
  · apply integrable_laguerreLaw_inverse_coordinate ha i
    have hi : (0 : ℝ) ≤ i.val := by positivity
    linarith



theorem laguerreLaw_measureReal (N : ℕ) {a : ℝ} (ha : 0 < a)
    {s : Set (Fin N → ℝ)} (hs : MeasurableSet s) :
    (laguerreLaw N a).real s =
      (∫ r in laguerreDomain N ∩ s, laguerreDensity N a r) / laguerreNormalizer N a := by
  rw [← integral_indicator_one hs, integral_laguerreLaw N ha]
  unfold laguerreExpectation
  simp_rw [← Set.indicator_mul_left, Pi.one_apply, one_mul]
  rw [setIntegral_indicator hs]

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

lemma positiveWindow_mono : Monotone (fun n : ℕ => Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ)) := by
  intro n m hnm x hx
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  exact ⟨(one_div_le_one_div_of_le (by positivity) (by linarith)).trans hx.1, by linarith [hx.2]⟩

lemma positiveWindow_cover : (⋃ n : ℕ, Icc (1 / (n + 1 : ℝ)) (n + 1 : ℝ)) = Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (by positivity : (0 : ℝ) < 1 / (n + 1 : ℝ)).trans_le hn.1
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x from hx)
    obtain ⟨m, hm⟩ := exists_nat_gt x
    apply mem_iUnion.mpr
    refine ⟨max n m, ?_, ?_⟩
    · exact (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (le_max_left n m) 1)).trans hn.le
    · have h : (m : ℝ) ≤ max n m := by exact_mod_cast le_max_right n m
      linarith

 

theorem ordered_density_covariance_Ioi {N : ℕ} (w : Fin N → ℝ → ℝ)
    (hwc : ∀ i, ContinuousOn (w i) (Ioi 0))
    (hw : ∀ i x, 0 < x → 0 ≤ w i x) (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hh : IntegrableOn (rawProductDensity N w) (laguerreDomain N))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (laguerreDomain N))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (laguerreDomain N))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (laguerreDomain N)) :
    (∫ x in laguerreDomain N, rawProductDensity N w x * f x) *
      (∫ x in laguerreDomain N, rawProductDensity N w x * g x) ≤
    (∫ x in laguerreDomain N, rawProductDensity N w x) *
      (∫ x in laguerreDomain N, rawProductDensity N w x * (f x * g x)) := by
  apply ordered_density_covariance_exhaustion (fun n => 1 / (n + 1 : ℝ)) (fun n => n + 1)
      (fun _ => by positivity) (fun n => ?_) positiveWindow_mono positiveWindow_cover
      w hwc hw f g hfc hgc hfm hgm hh hf hg hfg
  have hn : (1 : ℝ) ≤ n + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact le_trans (one_div_le_one_div_of_le (by norm_num) hn) (by simp)

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

lemma continuousOn_laguerreWeight (a : ℝ) : ContinuousOn (laguerreWeight a) (Ioi 0) := by
  unfold laguerreWeight
  exact (continuousOn_id.rpow_const (fun _ hx => Or.inl (ne_of_gt hx))).mul
    ((Real.continuous_exp.comp continuous_neg).continuousOn)

 

theorem integrable_laguerreLaw_iff {N : ℕ} {a : ℝ} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ} :
    Integrable f (laguerreLaw N a) ↔
      IntegrableOn (fun r => laguerreDensity N a r * f r) (laguerreDomain N) := by
  rw [laguerreLaw, integrable_smul_measure (by simp)
    (by simpa using laguerreNormalizer_pos N ha),
    integrable_withDensity_iff_integrable_smul' (measurable_laguerreDensity N a).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp [smul_eq_mul, ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le]

 

theorem laguerreLaw_covariance {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) (hg : Integrable g (laguerreLaw N a))
    (hfg : Integrable (fun r => f r * g r) (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) * (∫ r, g r ∂laguerreLaw N a) ≤
      ∫ r, f r * g r ∂laguerreLaw N a := by
  simp only [integral_laguerreLaw N ha, laguerreExpectation]
  apply weighted_covariance_normalize (laguerreNormalizer_pos N ha)
  have h := ordered_density_covariance_Ioi (fun _ : Fin N => laguerreWeight a)
    (fun _ => continuousOn_laguerreWeight a) (fun _ _ hx => (laguerreWeight_pos a hx).le)
    f g hfc hgc hfm hgm (integrableOn_laguerreDensity N ha)
    ((integrable_laguerreLaw_iff ha).1 hf) ((integrable_laguerreLaw_iff ha).1 hg)
    ((integrable_laguerreLaw_iff ha).1 hfg)
  simpa only [rawProductDensity, laguerreNormalizer, laguerreDensity, mul_comm] using h



lemma continuousOn_omega_Ioi : ContinuousOn omega (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  apply ContinuousAt.continuousWithinAt
  unfold omega
  fun_prop (disch := positivity)


theorem laguerreLaw_covariance_antitone {N : ℕ} {a : ℝ} (ha : 0 < a)
    (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hgm : AntitoneOn g (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) (hg : Integrable g (laguerreLaw N a))
    (hfg : Integrable (fun r => f r * g r) (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) * (∫ r, g r ∂laguerreLaw N a) ≤
      ∫ r, f r * g r ∂laguerreLaw N a := by
  have h := laguerreLaw_covariance ha (fun r => -f r) (fun r => -g r) hfc.neg hgc.neg
    (fun _ hx _ hy hxy => neg_le_neg (hfm hx hy hxy))
    (fun _ hx _ hy hxy => neg_le_neg (hgm hx hy hxy)) hf.neg hg.neg (by simpa using hfg)
  simpa only [integral_neg, neg_mul_neg] using h




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

 

theorem laguerreLaw_cutoff_covariance {N : ℕ} {a : ℝ} (ha : 0 < a) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) * (laguerreLaw N a).real (cutoffEvent N R) ≤
      ∫ r in cutoffEvent N R, f r ∂laguerreLaw N a := by
  let := laguerreLaw_isProbabilityMeasure N ha
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (cutoffProduct_integral_tendsto (laguerreLaw N a) R))
    (cutoffProduct_weighted_tendsto (laguerreLaw N a) R f hf)
  apply Eventually.of_forall
  intro n
  exact laguerreLaw_covariance_antitone ha f (cutoffProduct N n R) hfc
    (continuous_cutoffProduct N n R).continuousOn hfm
    ((antitone_cutoffProduct N n R).antitoneOn _) hf (cutoffProduct_integrable _ n R)
    (hf.mul_bdd (continuous_cutoffProduct N n R).aestronglyMeasurable
      (Eventually.of_forall (cutoffProduct_norm_le N n R)))

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

 

theorem laguerreLaw_conditioned_antitone {N : ℕ} {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (f : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioi 0)))
    (hfm : AntitoneOn f (coordinateBox (Fin N) (Ioi 0)))
    (hf : Integrable f (laguerreLaw N a)) :
    (∫ r, f r ∂laguerreLaw N a) ≤
      (∫ r in cutoffEvent N R, f r ∂laguerreLaw N a) /
        (laguerreLaw N a).real (cutoffEvent N R) := by
  exact (le_div_iff₀ (laguerreLaw_cutoff_pos N ha hR)).2
    (laguerreLaw_cutoff_covariance ha R f hfc hfm hf)



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

lemma continuousOn_inverse_coordinate {ι : Type*} [Fintype ι] (i : ι) (p : ℝ) :
    ContinuousOn (fun r : ι → ℝ => (r i) ^ (-p)) (coordinateBox ι (Ioi 0)) :=
  (continuous_apply i).continuousOn.rpow_const (fun _ hr => Or.inl (hr i).ne')

lemma antitoneOn_inverse_coordinate {ι : Type*} [Fintype ι] (i : ι) {p : ℝ}
    (hp : 0 ≤ p) :
    AntitoneOn (fun r : ι → ℝ => (r i) ^ (-p)) (coordinateBox ι (Ioi 0)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (hx i) (hxy i) (neg_nonpos.mpr hp)

theorem laguerreLaw_cutoff_inverse_coordinate {N : ℕ} {a R p : ℝ} (ha : 0 < a)
    (hR : 0 < R) (i : Fin N) (hp : 0 ≤ p) (hpD : p < laguerreDimension a (i.val + 1)) :
    (∫ r, (r i) ^ (-p) ∂laguerreLaw N a) ≤
      (∫ r in cutoffEvent N R, (r i) ^ (-p) ∂laguerreLaw N a) /
        (laguerreLaw N a).real (cutoffEvent N R) := by
  exact laguerreLaw_conditioned_antitone ha hR _
    (continuousOn_inverse_coordinate i p) (antitoneOn_inverse_coordinate i hp)
    (integrable_laguerreLaw_inverse_coordinate_full ha i hpD)

end

noncomputable section
open scoped BigOperators
open Set MeasureTheory

 

theorem omega_antitoneOn : AntitoneOn omega (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * y) (by positivity : 0 < 2 * x)).2
  nlinarith


lemma mobiusCoordinate_mem {z : ℝ} (hz : z ∈ Ioo 0 1) :
    mobiusCoordinate z ∈ Ioo 0 1 := by
  have hd : 0 < 1 + z := by linarith [hz.1]
  exact ⟨div_pos (by linarith [hz.1]) hd, (div_lt_one hd).2 (by linarith [hz.2])⟩

lemma mobiusCoordinate_strictMonoOn : StrictMonoOn mobiusCoordinate (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  apply (div_lt_div_iff₀ (by linarith : 0 < 1 + x) (by linarith : 0 < 1 + y)).2
  nlinarith

lemma pairKernel_mobius {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    pairKernel (mobiusCoordinate x) (mobiusCoordinate y) =
      2 * pairKernel x y / ((1 + x) * (1 + y) * (1 + 2 * x * y / (x + y))) := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hx1 : 1 + x ≠ 0 := by positivity
  have hy1 : 1 + y ≠ 0 := by positivity
  have ht : x + y + 2 * x * y ≠ 0 := by positivity
  unfold pairKernel mobiusCoordinate
  field_simp
  ring

lemma harmonicPair_monotone {x x' y y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxx' : x ≤ x') (hyy' : y ≤ y') :
    2 * x * y / (x + y) ≤ 2 * x' * y' / (x' + y') := by
  have hx' := hx.trans_le hxx'
  have hy' := hy.trans_le hyy'
  calc
    2 * x * y / (x + y) ≤ 2 * x' * y / (x' + y) := by
      apply (div_le_div_iff₀ (add_pos hx hy) (add_pos hx' hy)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hxx') (sq_nonneg y)]
    _ ≤ 2 * x' * y' / (x' + y') := by
      apply (div_le_div_iff₀ (add_pos hx' hy) (add_pos hx' hy')).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hyy') (sq_nonneg x')]


lemma mobiusPairFactor_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < mobiusPairFactor x y := by unfold mobiusPairFactor; positivity

lemma mobiusPairFactor_antitone {x x' y y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxx' : x ≤ x') (hyy' : y ≤ y') :
    mobiusPairFactor x' y' ≤ mobiusPairFactor x y := by
  exact inv_anti₀ (by positivity : 0 < 1 + 2 * x * y / (x + y))
    (by linarith [harmonicPair_monotone hx hy hxx' hyy'])

lemma exponential_over_power_antitone {m β : ℝ} (hm : 0 ≤ m) (hb : β ≤ m / 2) :
    AntitoneOn (fun x : ℝ => Real.exp (β * x - m * Real.log (1 + x))) (Ioo 0 1) := by
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => β * x - m * Real.log (1 + x)) (β - m / (1 + x)) x := by
    have hd0 : (1 : ℝ) + id x ≠ 0 := by change 1 + x ≠ 0; linarith [hx.1]
    apply (((hasDerivAt_id x).const_mul β).sub
      ((((hasDerivAt_id x).const_add 1).log hd0).const_mul m)).congr_deriv
    simp only [id_eq, mul_one, div_eq_mul_inv, one_mul]
  have hder (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : β - m / (1 + x) ≤ 0 := by
    have : m / 2 ≤ m / (1 + x) := div_le_div_of_nonneg_left hm (by linarith [hx.1]) (by linarith [hx.2])
    linarith
  have hlog : AntitoneOn (fun x : ℝ => β * x - m * Real.log (1 + x)) (Ioo 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo (0 : ℝ) 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (by simpa only [interior_Ioo] using hx)).hasDerivWithinAt)
      (fun x hx => hder x (by simpa only [interior_Ioo] using hx))
  intro x hx y hy hxy
  exact Real.exp_le_exp.mpr (hlog hx hy hxy)

lemma exponential_over_natPower_eq (k : ℕ) (β : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.exp (β * x - (k : ℝ) * Real.log (1 + x)) = Real.exp (β * x) / (1 + x) ^ k := by
  rw [Real.exp_sub, mul_comm (k : ℝ), ← Real.rpow_def_of_pos (by linarith : 0 < 1 + x),
    Real.rpow_natCast]


lemma lowerLikelihoodWeight_pos (N : ℕ) (β : ℝ) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    0 < lowerLikelihoodWeight N β z := by
  have hz0 := hz.1
  exact mul_pos (omega_pos (mobiusCoordinate_mem hz)) (by positivity)

lemma lowerLikelihoodWeight_antitone (N : ℕ) {β : ℝ} (hb : β ≤ (N + 1 : ℝ) / 2) :
    AntitoneOn (lowerLikelihoodWeight N β) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hω : omega (mobiusCoordinate y) ≤ omega (mobiusCoordinate x) :=
    omega_antitoneOn (mobiusCoordinate_mem hx).1 (mobiusCoordinate_mem hy).1
      (mobiusCoordinate_strictMonoOn.monotoneOn hx.1 hy.1 hxy)
  have he := exponential_over_power_antitone (by positivity : 0 ≤ (N + 1 : ℝ)) hb hx hy hxy
  simp only [← Nat.cast_add_one, exponential_over_natPower_eq (N + 1) β hx.1,
    exponential_over_natPower_eq (N + 1) β hy.1] at he
  have hy0 := hy.1
  exact mul_le_mul hω he (by positivity) (omega_nonneg _)



theorem lowerLikelihood_antitone (N : ℕ) {β : ℝ} (hb : β ≤ (N + 1 : ℝ) / 2) :
    AntitoneOn (lowerLikelihood N β) (coordinateBox (Fin N) (Ioo 0 1)) := by
  intro x hx y hy hxy
  have hw : (∏ i, lowerLikelihoodWeight N β (y i)) ≤ ∏ i, lowerLikelihoodWeight N β (x i) :=
    Finset.prod_le_prod (fun i _ => (lowerLikelihoodWeight_pos N β (hy i)).le)
      (fun i _ => lowerLikelihoodWeight_antitone N hb (hx i) (hy i) (hxy i))
  have hp : (∏ i, ∏ j ∈ Finset.univ.filter (i < ·), mobiusPairFactor (y i) (y j)) ≤
      ∏ i, ∏ j ∈ Finset.univ.filter (i < ·), mobiusPairFactor (x i) (x j) := by
    apply Finset.prod_le_prod
    · exact fun i _ => Finset.prod_nonneg fun j _ => (mobiusPairFactor_pos (hy i).1 (hy j).1).le
    · intro i _
      exact Finset.prod_le_prod (fun j _ => (mobiusPairFactor_pos (hy i).1 (hy j).1).le)
        (fun j _ => mobiusPairFactor_antitone (hx i).1 (hx j).1 (hxy i) (hxy j))
  exact mul_le_mul hw hp
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => (mobiusPairFactor_pos (hy i).1 (hy j).1).le)
    (Finset.prod_nonneg fun i _ => (lowerLikelihoodWeight_pos N β (hx i)).le)


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

lemma scaled_quotient {A Z B W c J p : ℝ} (hc : c ≠ 0) (hJ : J ≠ 0) (hp : p ≠ 0)
    (h0 : c * Z = J * W) (h1 : (c * p⁻¹) * A = J * B) :
    A / Z = p * (B / W) := by
  have hZ : Z = J * W / c := (eq_div_iff hc).2 (by simpa [mul_comm] using h0)
  have hA : A = J * B / (c * p⁻¹) := (eq_div_iff (mul_ne_zero hc (inv_ne_zero hp))).2
    (by simpa [mul_comm] using h1)
  rw [hZ, hA]
  field_simp



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



lemma mobiusInverse_mem {y : ℝ} (hy : y ∈ Ioo 0 1) : y / (2 - y) ∈ Ioo 0 1 := by
  have hd : 0 < 2 - y := by linarith [hy.2]
  exact ⟨div_pos hy.1 hd, (div_lt_one hd).2 (by linarith [hy.2])⟩

lemma mobiusCoordinate_inverse {y : ℝ} (hy : y < 1) :
    mobiusCoordinate (y / (2 - y)) = y := by
  have hd : 2 - y ≠ 0 := by linarith
  unfold mobiusCoordinate
  field_simp
  ring

lemma mobiusMap_mem {N : ℕ} {z : Fin N → ℝ} (hz : z ∈ orderedDomain N) :
    mobiusMap N z ∈ orderedDomain N := by
  exact ⟨fun i j hij => mobiusCoordinate_strictMonoOn (hz.2 i).1 (hz.2 j).1 (hz.1 hij),
    fun i => mobiusCoordinate_mem (hz.2 i)⟩

lemma mobiusMap_injOn (N : ℕ) : InjOn (mobiusMap N) (orderedDomain N) := by
  intro x hx y hy h
  funext i
  exact mobiusCoordinate_strictMonoOn.injOn (hx.2 i).1 (hy.2 i).1 (congrFun h i)

lemma mobiusMap_image (N : ℕ) : mobiusMap N '' orderedDomain N = orderedDomain N := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mobiusMap_mem hx
  · intro y hy
    let x : Fin N → ℝ := fun i => y i / (2 - y i)
    have heq : mobiusMap N x = y := funext fun i => mobiusCoordinate_inverse (hy.2 i).2
    refine ⟨x, ⟨?_, fun i => mobiusInverse_mem (hy.2 i)⟩, heq⟩
    intro i j hij
    have h := hy.1 hij
    rw [← congrFun heq i, ← congrFun heq j] at h
    exact (mobiusCoordinate_strictMonoOn.lt_iff_lt (mobiusInverse_mem (hy.2 i)).1
      (mobiusInverse_mem (hy.2 j)).1).1 h

lemma hasDerivAt_mobiusCoordinate {z : ℝ} (hz : 0 < z) :
    HasDerivAt mobiusCoordinate (2 / (1 + z)^2) z := by
  have hd : (1 : ℝ) + id z ≠ 0 := by change 1 + z ≠ 0; positivity
  apply (((hasDerivAt_id z).const_mul 2).div ((hasDerivAt_id z).const_add 1) hd).congr_deriv
  simp only [id_eq, mul_one]
  ring


lemma hasFDerivAt_mobiusMap {N : ℕ} {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    HasFDerivAt (mobiusMap N) (mobiusDifferential N z) z := by
  unfold mobiusMap mobiusDifferential
  rw [hasFDerivAt_pi]
  intro i
  have h1 : HasFDerivAt mobiusCoordinate
      (ContinuousLinearMap.toSpanSingleton ℝ (2 / (1 + z i)^2)) (z i) :=
    (hasDerivAt_mobiusCoordinate (hz i)).hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
    h1.comp z ((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt)

lemma det_mobiusDifferential (N : ℕ) (z : Fin N → ℝ) :
    (mobiusDifferential N z).det = mobiusJacobian N z := by
  simp only [mobiusDifferential, ContinuousLinearMap.det_pi,
    ContinuousLinearMap.det_toSpanSingleton, mobiusJacobian]

lemma mobiusJacobian_pos {N : ℕ} {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    0 < mobiusJacobian N z := by
  exact Finset.prod_pos fun i _ => div_pos (by norm_num) (sq_pos_of_pos (by linarith [hz i]))

 

theorem integral_mobiusMap (N : ℕ) (g : (Fin N → ℝ) → ℝ) :
    (∫ y in orderedDomain N, g y) =
      ∫ z in orderedDomain N, mobiusJacobian N z * g (mobiusMap N z) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (isOpen_orderedDomain N).measurableSet
    (fun z hz => (hasFDerivAt_mobiusMap (fun i => (hz.2 i).1)).hasFDerivWithinAt)
    (mobiusMap_injOn N) g
  rw [mobiusMap_image] at h
  apply h.trans
  apply setIntegral_congr_fun (isOpen_orderedDomain N).measurableSet
  intro z hz
  dsimp only
  rw [det_mobiusDifferential, abs_of_pos (mobiusJacobian_pos (fun i => (hz.2 i).1)), smul_eq_mul]

lemma integrableOn_mobiusMap_iff (N : ℕ) (g : (Fin N → ℝ) → ℝ) :
    IntegrableOn g (orderedDomain N) ↔
      IntegrableOn (fun z => mobiusJacobian N z * g (mobiusMap N z)) (orderedDomain N) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (isOpen_orderedDomain N).measurableSet
    (fun z hz => (hasFDerivAt_mobiusMap (fun i => (hz.2 i).1)).hasFDerivWithinAt)
    (mobiusMap_injOn N) g
  rw [mobiusMap_image] at h
  apply h.trans
  apply integrable_congr
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with z hz
  rw [det_mobiusDifferential, abs_of_pos (mobiusJacobian_pos (fun i => (hz.2 i).1)), smul_eq_mul]

lemma prod_pair_coordinates {N : ℕ} (f : Fin N → ℝ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, f i * f j) = (∏ i, f i) ^ (N - 1) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun i _ : Fin N => f i)
  simp only [mul_comm] at h
  rw [h]
  have heq (i : Fin N) : (∏ j ∈ ({i}ᶜ : Finset (Fin N)), f j) =
      ∏ j : Fin N, if i ≠ j then f j else 1 := by
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp [ne_comm]
  simp_rw [heq]
  rw [Finset.prod_comm]
  have heq' (j : Fin N) : (∏ i : Fin N, if i ≠ j then f j else 1) = f j ^ (N - 1) := by
    rw [← Finset.prod_filter]
    have hset : (Finset.univ.filter fun i : Fin N => i ≠ j) = {j}ᶜ := by
      ext i
      simp
    rw [hset]
    simp only [Finset.prod_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  simp_rw [heq']
  rw [Finset.prod_pow]


lemma mobiusDensityConstant_pos (N : ℕ) : 0 < mobiusDensityConstant N := by
  exact mul_pos (Finset.prod_pos fun _ _ => by norm_num)
    (Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => by norm_num)

lemma prod_pairKernel_mobius {N : ℕ} {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (mobiusCoordinate (z i)) (mobiusCoordinate (z j))) =
      (∏ i : Fin N, ∏ _j ∈ Finset.Ioi i, (2 : ℝ)) * (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (z i) (z j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, mobiusPairFactor (z i) (z j)) / (∏ i : Fin N, (1 + z i)) ^ (N - 1) := by
  have h (i j : Fin N) : pairKernel (mobiusCoordinate (z i)) (mobiusCoordinate (z j)) =
      2 * pairKernel (z i) (z j) * mobiusPairFactor (z i) (z j) / ((1 + z i) * (1 + z j)) := by
    rw [pairKernel_mobius (hz i) (hz j)]
    simp only [mobiusPairFactor, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [h, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hd := prod_pair_coordinates (fun i => 1 + z i)
  simp only [Finset.prod_mul_distrib] at hd
  rw [hd]

lemma scaledWeight_mul_lowerLikelihoodWeight (N : ℕ) (β z : ℝ) :
    scaledLaguerreWeight 1 β z * lowerLikelihoodWeight N β z =
      omega (mobiusCoordinate z) / (1 + z) ^ (N + 1) := by
  unfold scaledLaguerreWeight lowerLikelihoodWeight
  norm_num only [sub_self, Real.rpow_zero, one_mul]
  calc
    _ = omega (mobiusCoordinate z) / (1 + z) ^ (N + 1) *
        (Real.exp (-(β * z)) * Real.exp (β * z)) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

lemma scaledDensity_mul_lowerLikelihood (N : ℕ) (β : ℝ) (z : Fin N → ℝ) :
    scaledLaguerreDensity N 1 β z * lowerLikelihood N β z =
      (∏ i, omega (mobiusCoordinate (z i))) / (∏ i : Fin N, (1 + z i)) ^ (N + 1) *
        (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (z i) (z j)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, mobiusPairFactor (z i) (z j)) := by
  have hw : (∏ i, scaledLaguerreWeight 1 β (z i)) *
      (∏ i, lowerLikelihoodWeight N β (z i)) =
        (∏ i, omega (mobiusCoordinate (z i))) / (∏ i : Fin N, (1 + z i)) ^ (N + 1) := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [scaledWeight_mul_lowerLikelihoodWeight,
      Finset.prod_div_distrib, Finset.prod_pow]
  unfold scaledLaguerreDensity rawProductDensity lowerLikelihood
  change ((∏ i, scaledLaguerreWeight 1 β (z i)) * _) * ((∏ i, lowerLikelihoodWeight N β (z i)) * _) = _
  rw [mul_mul_mul_comm, hw]
  have hI (i : Fin N) : Finset.univ.filter (i < ·) = Finset.Ioi i := by ext j; simp
  simp_rw [hI]
  ring

 

theorem density_mobiusMap {N : ℕ} (β : ℝ) {z : Fin N → ℝ} (hz : ∀ i, 0 < z i) :
    mobiusJacobian N z * density N (mobiusMap N z) =
      mobiusDensityConstant N * (scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) := by
  cases N with
  | zero => simp [mobiusJacobian, density, mobiusDensityConstant,
      scaledLaguerreDensity, rawProductDensity, lowerLikelihood]
  | succ n =>
    rw [scaledDensity_mul_lowerLikelihood]
    unfold density mobiusMap mobiusJacobian mobiusDensityConstant
    simp only [Finset.prod_div_distrib, Finset.prod_pow]
    rw [prod_pairKernel_mobius hz]
    simp only [Nat.add_sub_cancel]
    have hd : (∏ i : Fin (n + 1), (1 + z i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by linarith [hz i]
    field_simp
    ring

lemma jacobian_weighted_density {N : ℕ} (β : ℝ) (g : (Fin N → ℝ) → ℝ)
    {z : Fin N → ℝ} (hz : z ∈ orderedDomain N) :
    mobiusJacobian N z * (g (mobiusMap N z) * density N (mobiusMap N z)) =
      mobiusDensityConstant N * (scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z)) := by
  calc
    _ = g (mobiusMap N z) * (mobiusJacobian N z * density N (mobiusMap N z)) := by ring
    _ = _ := by rw [density_mobiusMap β (fun i => (hz.2 i).1)]; ring

lemma integral_density_mobius_likelihood (N : ℕ) (β : ℝ) (g : (Fin N → ℝ) → ℝ) :
    (∫ y in orderedDomain N, g y * density N y) =
      mobiusDensityConstant N * ∫ z in orderedDomain N,
        scaledLaguerreDensity N 1 β z * (g (mobiusMap N z) * lowerLikelihood N β z) := by
  rw [integral_mobiusMap, ← integral_const_mul]
  exact setIntegral_congr_fun (isOpen_orderedDomain N).measurableSet
    (fun z hz => jacobian_weighted_density β g hz)

lemma integrableOn_density_mobius_likelihood_iff (N : ℕ) (β : ℝ) (g : (Fin N → ℝ) → ℝ) :
    IntegrableOn (fun y => g y * density N y) (orderedDomain N) ↔
      IntegrableOn (fun z => scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z)) (orderedDomain N) := by
  rw [integrableOn_mobiusMap_iff]
  have heq : (fun z => mobiusJacobian N z * (g (mobiusMap N z) * density N (mobiusMap N z)))
      =ᵐ[volume.restrict (orderedDomain N)]
      (fun z => mobiusDensityConstant N * (scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z))) := by
    filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with z hz
    exact jacobian_weighted_density β g hz
  unfold IntegrableOn
  rw [integrable_congr heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (mobiusDensityConstant_pos N).ne') _

lemma mobiusLikelihood_Normalizer (N : ℕ) (β : ℝ) :
    normalizer N = mobiusDensityConstant N *
      ∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z := by
  simpa only [one_mul, normalizer] using integral_density_mobius_likelihood N β (fun _ => 1)

lemma integrableOn_mobiusLikelihood (N : ℕ) (β : ℝ) :
    IntegrableOn (fun z => scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) (orderedDomain N) := by
  simpa only [one_mul] using
    (integrableOn_density_mobius_likelihood_iff N β (fun _ => 1)).1
      (by simpa only [one_mul] using integrableOn_density N)

lemma mobiusLikelihood_Normalizer_pos (N : ℕ) (β : ℝ) :
    0 < ∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z := by
  have h := normalizer_pos N
  rw [mobiusLikelihood_Normalizer N β] at h
  exact (mul_pos_iff_of_pos_left (mobiusDensityConstant_pos N)).1 h

lemma continuousOn_mobiusCoordinate : ContinuousOn mobiusCoordinate (Ioi 0) := by
  exact (continuous_const.mul continuous_id).continuousOn.div
    (continuous_const.add continuous_id).continuousOn (fun z hz => (add_pos (by norm_num : (0:ℝ) < 1) hz).ne')

lemma continuousOn_lowerLikelihood (N : ℕ) (β : ℝ) :
    ContinuousOn (lowerLikelihood N β) (coordinateBox (Fin N) (Ioo 0 1)) := by
  unfold lowerLikelihood
  apply ContinuousOn.mul
  · apply continuousOn_finsetProd
    intro i _
    have hmob : ContinuousOn (fun z : Fin N → ℝ => mobiusCoordinate (z i))
        (coordinateBox (Fin N) (Ioo 0 1)) :=
      continuousOn_mobiusCoordinate.comp (continuous_apply i).continuousOn (fun z hz => (hz i).1)
    exact (continuousOn_omega_Ioi.comp hmob (fun z hz => (mobiusCoordinate_mem (hz i)).1)).mul
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).continuousOn.div
        ((continuous_const.add (continuous_apply i)).pow (N + 1)).continuousOn
        (fun z hz => pow_ne_zero _ (by linarith [(hz i).1])))
  · apply continuousOn_finsetProd
    intro i _
    apply continuousOn_finsetProd
    intro j _
    have hq : ContinuousOn (fun z : Fin N → ℝ => 2 * z i * z j / (z i + z j))
        (coordinateBox (Fin N) (Ioo 0 1)) :=
      ((continuous_const.mul (continuous_apply i)).mul (continuous_apply j)).continuousOn.div
        ((continuous_apply i).add (continuous_apply j)).continuousOn
        (fun z hz => (add_pos (hz i).1 (hz j).1).ne')
    exact (continuousOn_const.add hq).inv₀ (fun z hz =>
      (add_pos (by norm_num : (0:ℝ)<1)
        (div_pos (mul_pos (mul_pos (by norm_num) (hz i).1) (hz j).1)
          (add_pos (hz i).1 (hz j).1))).ne')

lemma mobiusCoordinate_le_double {z : ℝ} (hz : 0 < z) : mobiusCoordinate z ≤ 2 * z := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + z)).2
  nlinarith [sq_nonneg z]

lemma self_le_mobiusCoordinate {z : ℝ} (hz : z ∈ Ioo 0 1) : z ≤ mobiusCoordinate z := by
  apply (le_div_iff₀ (by linarith [hz.1] : 0 < 1 + z)).2
  nlinarith [mul_nonneg hz.1.le (sub_nonneg.mpr hz.2.le)]

lemma mobius_inverseQuarter_bounds {z : ℝ} (hz : z ∈ Ioo 0 1) :
    (2 : ℝ) ^ (-(1/4:ℝ)) * z ^ (-(1/4:ℝ)) ≤ (mobiusCoordinate z) ^ (-(1/4:ℝ)) ∧
    (mobiusCoordinate z) ^ (-(1/4:ℝ)) ≤ z ^ (-(1/4:ℝ)) := by
  constructor
  · rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤2) hz.1.le]
    exact Real.rpow_le_rpow_of_nonpos (mobiusCoordinate_mem hz).1
      (mobiusCoordinate_le_double hz.1) (by norm_num)
  · exact Real.rpow_le_rpow_of_nonpos hz.1 (self_le_mobiusCoordinate hz) (by norm_num)

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


namespace CriticalStrip
noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter
lemma integrableOn_scaledLaguerre_inverse_coordinate {N : ℕ} {a p β : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) (hb : 1 ≤ β) :
    IntegrableOn (fun r => (r i) ^ (-p) * scaledLaguerreDensity N a β r) (laguerreDomain N) := by
  apply (integrableOn_laguerre_inverse_coordinate ha i hp).mono'
    (((measurable_pi_apply i).pow_const _).mul
      (measurable_scaledLaguerreDensity N a β)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hr.2 i) _).le
    (scaledLaguerreDensity_pos a β hr).le)]
  exact mul_le_mul_of_nonneg_left (scaledLaguerreDensity_le a hb hr)
    (Real.rpow_pos_of_pos (hr.2 i) _).le

lemma continuousOn_mobiusInverseQuarter {N : ℕ} (i : Fin N) :
    ContinuousOn (mobiusInverseQuarter i) (coordinateBox (Fin N) (Ioo 0 1)) := by
  exact (continuousOn_mobiusCoordinate.comp (continuous_apply i).continuousOn
    (fun z hz => (hz i).1)).rpow_const (fun z hz => Or.inl (mobiusCoordinate_mem (hz i)).1.ne')

lemma antitoneOn_mobiusInverseQuarter {N : ℕ} (i : Fin N) :
    AntitoneOn (mobiusInverseQuarter i) (coordinateBox (Fin N) (Ioo 0 1)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (mobiusCoordinate_mem (hx i)).1
    (mobiusCoordinate_strictMonoOn.monotoneOn (hx i).1 (hy i).1 (hxy i)) (by norm_num)

lemma integrableOn_scaledLaguerre_mobiusInverseQuarter {N : ℕ} {β : ℝ} (i : Fin N) (hb : 1 ≤ β) :
    IntegrableOn (fun z => mobiusInverseQuarter i z * scaledLaguerreDensity N 1 β z)
      (orderedDomain N) := by
  have hs : orderedDomain N ⊆ laguerreDomain N := fun _ hz => ⟨hz.1, fun i => (hz.2 i).1⟩
  have hm : Measurable (fun z => mobiusInverseQuarter i z * scaledLaguerreDensity N 1 β z) := by
    unfold mobiusInverseQuarter mobiusCoordinate
    apply Measurable.mul
    · fun_prop
    · exact measurable_scaledLaguerreDensity N 1 β
  apply ((integrableOn_scaledLaguerre_inverse_coordinate (by norm_num : (0:ℝ)<1)
    i (by linarith [Nat.cast_nonneg (α:=ℝ) i.val] : (1/4:ℝ) < 1 + i.val) hb).mono_set hs).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_pos_of_pos (mobiusCoordinate_mem (hz.2 i)).1 _).le
    (scaledLaguerreDensity_pos 1 β (hs hz)).le)]
  exact mul_le_mul_of_nonneg_right (mobius_inverseQuarter_bounds (hz.2 i)).2
    (scaledLaguerreDensity_pos 1 β (hs hz)).le

lemma positiveLaw_mobius_expectation {N : ℕ} (β : ℝ) (g : (Fin N → ℝ) → ℝ) :
    (∫ y, g y ∂positiveLaw N) =
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z)) /
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) := by
  rw [integral_positiveLaw]
  unfold expectation
  rw [integral_density_mobius_likelihood N β g, mobiusLikelihood_Normalizer N β,
    mul_div_mul_left _ _ (mobiusDensityConstant_pos N).ne']

 

theorem positiveLaw_inverseQuarter_ge_scaled_reference {N : ℕ} (i : Fin N) {β : ℝ}
    (hb : 1 ≤ β) (hb' : β ≤ (N + 1 : ℝ) / 2) :
    (2 : ℝ) ^ (-(1/4:ℝ)) *
      ((∫ z in orderedDomain N, (z i) ^ (-(1/4:ℝ)) * scaledLaguerreDensity N 1 β z) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z)) ≤
      ∫ y, (y i) ^ (-(1/4:ℝ)) ∂positiveLaw N := by
  have hS : orderedDomain N ⊆ laguerreDomain N := fun _ hz => ⟨hz.1, fun j => (hz.2 j).1⟩
  have hiB : IntegrableOn (scaledLaguerreDensity N 1 β) (orderedDomain N) :=
    (integrableOn_scaledLaguerreDensity (by norm_num : (0:ℝ)<1) hb).mono_set hS
  have hiBF : IntegrableOn (fun z => scaledLaguerreDensity N 1 β z * mobiusInverseQuarter i z)
      (orderedDomain N) := by
    simpa only [mul_comm] using integrableOn_scaledLaguerre_mobiusInverseQuarter i hb
  have hiBL := integrableOn_mobiusLikelihood N β
  have hiBFL : IntegrableOn (fun z => scaledLaguerreDensity N 1 β z *
      (mobiusInverseQuarter i z * lowerLikelihood N β z)) (orderedDomain N) :=
    (integrableOn_density_mobius_likelihood_iff N β (fun y => (y i) ^ (-(1/4:ℝ)))).1
      (integrableOn_inverseQuarterCoordinate_density N i)
  have hiBcoord := (integrableOn_scaledLaguerre_inverse_coordinate (by norm_num : (0:ℝ)<1)
    i (by linarith [Nat.cast_nonneg (α:=ℝ) i.val] : (1/4:ℝ) < 1 + i.val) hb).mono_set hS
  have hcov := ordered_density_covariance_Ioo (by norm_num : (0:ℝ)<1)
    (fun _ : Fin N => scaledLaguerreWeight 1 β)
    (fun _ => (continuousOn_scaledLaguerreWeight 1 β).mono (fun _ hx => hx.1))
    (fun _ _ hx => (scaledLaguerreWeight_pos 1 β hx.1).le)
    (fun z => -mobiusInverseQuarter i z) (fun z => -lowerLikelihood N β z)
    (continuousOn_mobiusInverseQuarter i).neg (continuousOn_lowerLikelihood N β).neg
    (fun _ hx _ hy hxy => neg_le_neg (antitoneOn_mobiusInverseQuarter i hx hy hxy))
    (fun _ hx _ hy hxy => neg_le_neg (lowerLikelihood_antitone N hb' hx hy hxy))
    hiB (by simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, mul_neg, Pi.neg_def] using hiBF.neg)
    (by simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, mul_neg, Pi.neg_def] using hiBL.neg)
    (by simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, neg_mul_neg] using hiBFL)
  have hZ : 0 < ∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z :=
    scaledLaguerre_cutoffNormalizer_pos N (by norm_num) hb (by norm_num)
  have hL := mobiusLikelihood_Normalizer_pos N β
  have hcomp :
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * mobiusInverseQuarter i z) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z) ≤
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z *
        (mobiusInverseQuarter i z * lowerLikelihood N β z)) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) := by
    apply (div_le_div_iff₀ hZ hL).2
    simp only [mul_neg, neg_mul, neg_neg, integral_neg] at hcov
    simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, mul_comm] using hcov
  calc
    _ ≤ (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * mobiusInverseQuarter i z) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z) := by
      rw [← mul_div_assoc, ← integral_const_mul]
      apply div_le_div_of_nonneg_right _ hZ.le
      apply setIntegral_mono_on (hiBcoord.const_mul _) hiBF (isOpen_orderedDomain N).measurableSet
      intro z hz
      have h := mul_le_mul_of_nonneg_right (mobius_inverseQuarter_bounds (hz.2 i)).1
        (scaledLaguerreDensity_pos 1 β (hS hz)).le
      simpa only [mobiusInverseQuarter, _root_.mul_assoc] using
        h.trans_eq (_root_.mul_comm _ _)
    _ ≤ _ := hcomp
    _ = _ := (positiveLaw_mobius_expectation β (fun y => (y i) ^ (-(1/4:ℝ)))).symm

lemma integral_scaledLaguerre_cutoff_inverse_coordinate {N : ℕ} (a p R : ℝ) (i : Fin N)
    {β : ℝ} (hb : 0 < β) :
    (laguerreDensityScale N a β * (β ^ p)⁻¹) *
      (∫ y in orderedChamber N (Ioo 0 R), (y i) ^ (-p) * scaledLaguerreDensity N a β y) =
      (β ^ N)⁻¹ * (∫ r in orderedChamber N (Ioo 0 (β * R)), (r i) ^ (-p) * laguerreDensity N a r) := by
  rw [← integral_const_mul]
  calc
    (∫ y in orderedChamber N (Ioo 0 R), (laguerreDensityScale N a β * (β ^ p)⁻¹) *
        ((y i) ^ (-p) * scaledLaguerreDensity N a β y)) =
        ∫ y in orderedChamber N (Ioo 0 R), ((β • y) i) ^ (-p) * laguerreDensity N a (β • y) := by
      apply setIntegral_congr_fun (measurableSet_orderedChamber_Ioo N R)
      intro y hy
      dsimp only
      rw [laguerreDensity_scaled a hb (fun j => (hy.2 j).1)]
      simp only [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hb.le (hy.2 i).1.le, Real.rpow_neg hb.le]
      ring
    _ = _ := integral_orderedChamber_scaled R hb (fun r => (r i) ^ (-p) * laguerreDensity N a r)

lemma scaled_reference_cutoff_inverse_coordinate {N : ℕ} (a p R : ℝ) (i : Fin N)
    {β : ℝ} (hb : 0 < β) :
    (∫ y in orderedChamber N (Ioo 0 R), (y i) ^ (-p) * scaledLaguerreDensity N a β y) /
      (∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y) =
      β ^ p *
        ((∫ r in orderedChamber N (Ioo 0 (β * R)), (r i) ^ (-p) * laguerreDensity N a r) /
          (∫ r in orderedChamber N (Ioo 0 (β * R)), laguerreDensity N a r)) := by
  exact scaled_quotient (laguerreDensityScale_pos N a hb).ne'
    (inv_ne_zero (pow_ne_zero _ hb.ne')) (Real.rpow_pos_of_pos hb _).ne'
    (integral_scaledLaguerre_cutoff N a R hb) (integral_scaledLaguerre_cutoff_inverse_coordinate a p R i hb)

 

theorem positiveLaw_inverseQuarter_ge_reference {N : ℕ} (i : Fin N) {β : ℝ}
    (hb : 1 ≤ β) (hb' : β ≤ (N + 1 : ℝ) / 2) :
    (2 : ℝ) ^ (-(1/4:ℝ)) * β ^ (1/4:ℝ) *
      (∫ r, (r i) ^ (-(1/4:ℝ)) ∂laguerreLaw N 1) ≤
        ∫ y, (y i) ^ (-(1/4:ℝ)) ∂positiveLaw N := by
  have hb0 : 0 < β := by linarith
  have hpD : (1/4:ℝ) < laguerreDimension 1 (i.val + 1) := by
    unfold laguerreDimension
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [sq_nonneg (i.val : ℝ)]
  have hcut := laguerreLaw_cutoff_inverse_coordinate (by norm_num : (0:ℝ)<1) hb0 i
    (by norm_num : (0:ℝ)≤1/4) hpD
  have hscale := scaled_reference_cutoff_inverse_coordinate 1 (1/4) 1 i hb0
  simp only [mul_one] at hscale
  calc
    _ ≤ (2 : ℝ) ^ (-(1/4:ℝ)) * (β ^ (1/4:ℝ) *
        ((∫ r in cutoffEvent N β, (r i) ^ (-(1/4:ℝ)) ∂laguerreLaw N 1) /
          (laguerreLaw N 1).real (cutoffEvent N β))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hcut
        (mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
          (Real.rpow_pos_of_pos hb0 _).le)
    _ = (2 : ℝ) ^ (-(1/4:ℝ)) *
        ((∫ z in orderedDomain N, (z i) ^ (-(1/4:ℝ)) * scaledLaguerreDensity N 1 β z) /
          (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z)) := by
      rw [laguerreLaw_conditioned_eq N (by norm_num), ← hscale]
      rfl
    _ ≤ _ := positiveLaw_inverseQuarter_ge_scaled_reference i hb hb'

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
open Set MeasureTheory

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



theorem positiveLaw_least_inverseQuarter_growth_lower (n : ℕ) :
    ((2:ℝ)^(-(1/4:ℝ))*(1/2:ℝ)^(1/4:ℝ)*(Real.exp (-1)/48)) * ((n:ℝ)+1)^(3/4:ℝ) ≤
      ∫ y, (y 0)^(-(1/4:ℝ)) ∂positiveLaw (n+1) := by
  let b : ℝ := ((n:ℝ)+2)/2
  have hb : 1 ≤ b := by dsimp [b]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb' : b ≤ ((n+1:ℕ)+1:ℝ)/2 := by dsimp [b]; push_cast; linarith
  have hb0 : 0 < b := by linarith
  have H := positiveLaw_inverseQuarter_ge_reference (0 : Fin (n+1)) hb hb'
  have hRef := laguerre_least_inverseQuarter_lower n
  rw [← integral_laguerreLaw _ (by norm_num : (0:ℝ)<1)] at hRef
  have hscale : ((1/2:ℝ)*((n:ℝ)+1))^(1/4:ℝ) ≤ b^(1/4:ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    dsimp [b]
    linarith
  have hlow : 0 ≤ (Real.exp (-1)/48)*((n:ℝ)+1)^(1/2:ℝ) := by positivity
  calc
    _ = (2:ℝ)^(-(1/4:ℝ)) * (((1/2:ℝ)*((n:ℝ)+1))^(1/4:ℝ)) *
        ((Real.exp (-1)/48) * ((n:ℝ)+1)^(1/2:ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) (by positivity)]
      have hn : 0 < (n:ℝ)+1 := by positivity
      have he : ((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ) = ((n:ℝ)+1)^(3/4:ℝ) := by
        rw [← Real.rpow_add hn]
        norm_num
      calc
        _ = ((2:ℝ)^(-(1/4:ℝ))*(1/2:ℝ)^(1/4:ℝ)*(Real.exp (-1)/48)) *
          (((n:ℝ)+1)^(1/4:ℝ)*((n:ℝ)+1)^(1/2:ℝ)) := by rw [he]
        _ = _ := by ring
    _ ≤ (2:ℝ)^(-(1/4:ℝ))*b^(1/4:ℝ)*
        ((Real.exp (-1)/48)*((n:ℝ)+1)^(1/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) hlow
    _ ≤ (2:ℝ)^(-(1/4:ℝ))*b^(1/4:ℝ)*
        (∫ r, (r 0)^(-(1/4:ℝ)) ∂laguerreLaw (n+1) 1) :=
      mul_le_mul_of_nonneg_left hRef (by positivity)
    _ ≤ _ := H

 

theorem positive_arch_integral_growth :
    Comparable (fun N => ∫ x in Ioo 0 1, momentIntegrand N x)
      (fun N => (N:ℝ)^(3/4:ℝ)) := by
  refine ⟨(1/96) * ((2:ℝ)^(-(1/4:ℝ))*(1/2:ℝ)^(1/4:ℝ)*(Real.exp (-1)/48)),
    (32/3) * (2*(64:ℝ)^(1/4:ℝ)*referenceUpperConstant), by positivity,
    by have := referenceUpperConstant_pos; positivity, ?_⟩
  intro N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hI := integral_inverse_comparison hN
  have hL := positiveLaw_least_inverseQuarter_growth_lower n
  have hU := positiveLaw_inverseQuarterSum_growth_upper n
  rw [integral_positiveLaw] at hL hU
  constructor
  · have H := (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤1/96)).trans hI.1
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using H
  · have H := hI.2.trans (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤32/3))
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using H





end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReflectionIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators

lemma eta_pos : 0 < eta := by
  have hd : d = Real.sqrt 2 / 2 := by
    rw [d, lambda, show 2*(Real.pi/8)=Real.pi/4 by ring, Real.cos_pi_div_four]
  have hs : 1 < Real.sqrt 2 := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<2)
  unfold eta
  rw [hd]
  linarith


theorem homogeneous_arch_coefficient_growth :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ g : Polynomial ℝ, MonicProblem N g →
        lo*(N:ℝ)^(3/4:ℝ) ≤ (N:ℝ)*C - eta*g.coeff (N-1) ∧
          (N:ℝ)*C - eta*g.coeff (N-1) ≤ hi*(N:ℝ)^(3/4:ℝ) := by
  obtain ⟨lo, hi, hl, hh, hbound⟩ := positive_arch_integral_growth
  have hc : 0 < eta/Real.pi := div_pos eta_pos Real.pi_pos
  refine ⟨(eta/Real.pi)*lo, (eta/Real.pi)*hi, mul_pos hc hl, mul_pos hc hh, ?_⟩
  intro N hN g hg
  rw [homogeneous_arch_coefficient_integral N hN hg]
  obtain ⟨h1, h2⟩ := hbound N hN
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h1 hc.le
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h2 hc.le

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/




namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical


lemma PathBetween.reverse {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) : PathBetween N b a p.reverse := by
  refine ⟨by simpa using hp.2.1,by simpa using hp.1,(by simpa only [List.nodup_reverse] using hp.2.2.1),?_,?_⟩
  · exact List.isChain_reverse.mpr (hp.2.2.2.1.imp (fun _ _ h => adjacent_symmetric.symm _ _ h))
  · intro v hv
    exact hp.2.2.2.2 v (List.mem_reverse.mp hv)


lemma translateTriangle_injective (i : ℤ) : Function.Injective (translateTriangle i) := by
  intro v w h
  have := congrArg (translateTriangle (-i)) h
  simpa using this

lemma adjacent_translate_iff (i : ℤ) (v w : Triangle) :
    adjacent (translateTriangle i v) (translateTriangle i w) ↔ adjacent v w := by
  simp only [adjacent,upDownAdjacent,translateTriangle,add_assoc,add_left_cancel_iff]

lemma PathBetween.translate {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) (i : ℤ) :
    PathBetween N (translateTriangle i a) (translateTriangle i b) (p.map (translateTriangle i)) := by
  refine ⟨?_,?_,hp.2.2.1.map (translateTriangle_injective i),?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · exact (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun _ _ => (adjacent_translate_iff i _ _).mpr))
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact hp.2.2.2.2 w hw

@[simp] lemma pathBetween_translate_iff (N : ℕ) (a b : Triangle) (p : List Triangle) (i : ℤ) :
    PathBetween N (translateTriangle i a) (translateTriangle i b) (p.map (translateTriangle i)) ↔
      PathBetween N a b p := by
  refine ⟨fun h => ?_,fun h => h.translate i⟩
  simpa [List.map_map,Function.comp_def] using h.translate (-i)

lemma betweenArchWeight_nonneg (N : ℕ) (i j : ℤ) (p : List Triangle) :
    0≤betweenArchWeight N i j p := by
  unfold betweenArchWeight
  split
  · exact (pow_pos rho_pos _).le
  · exact le_rfl

lemma betweenArchWeight_translate (N : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenArchWeight N i j (p.map (translateTriangle i))=archWeight N (j-i) p := by
  have hi : up i 0=translateTriangle i (up 0 0) := by simp
  have hj : up j 0=translateTriangle i (up (j-i) 0) := by simp
  have hn : i≠j ↔ j-i≠0 := by omega
  simp only [betweenArchWeight,archWeight,hi,hj,pathBetween_translate_iff,
    pathBetween_source,hn,List.length_map]

 

theorem betweenArchKernel_eq (N : ℕ) (i j : ℤ) : betweenArchKernel N i j=K N (j-i) := by
  rw [betweenArchKernel,←(translatePaths i).tsum_eq]
  exact tsum_congr (betweenArchWeight_translate N i j)

lemma summable_betweenArchWeight_iff (N : ℕ) (i j : ℤ) :
    Summable (betweenArchWeight N i j) ↔ Summable (archWeight N (j-i)) := by
  rw [←(translatePaths i).summable_iff]
  exact summable_congr (betweenArchWeight_translate N i j)

lemma betweenArchWeight_reverse (N : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenArchWeight N j i p.reverse=betweenArchWeight N i j p := by
  have hp : PathBetween N (up j 0) (up i 0) p.reverse ↔ PathBetween N (up i 0) (up j 0) p := by
    refine ⟨fun h => ?_,PathBetween.reverse⟩
    simpa using h.reverse
  simp only [betweenArchWeight,hp,ne_comm,List.length_reverse]



lemma cutArchWeight_nonneg (N : ℕ) (x : (ℕ×ℕ)×List Triangle) : 0 ≤ cutArchWeight N x :=
  betweenArchWeight_nonneg _ _ _ _

lemma cutArchWeight_path_sum (N : ℕ) (x : ℕ×ℕ) :
    (∑' p,cutArchWeight N (x,p))=K N ((x.1+x.2:ℕ)+1) := by
  change betweenArchKernel N (-(x.1:ℤ)) ((x.2:ℤ)+1)=_
  rw [betweenArchKernel_eq]
  congr 1
  omega

 

lemma summable_add_diagonal_iff {f : ℕ→ℝ} (hf : ∀ n,0≤f n) :
    Summable (fun x : ℕ×ℕ => f (x.1+x.2)) ↔ Summable (fun n : ℕ => (n+1:ℝ)*f n) := by
  rw [←Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  change Summable (fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
    f (x.2.val.1+x.2.val.2)) ↔ _
  rw [summable_sigma_of_nonneg (fun x => hf _)]
  have hsum (n : ℕ) : (∑' x : Finset.HasAntidiagonal.antidiagonal n,
      f (x.val.1+x.val.2))=(n+1:ℝ)*f n := by
    have he (x : Finset.HasAntidiagonal.antidiagonal n) : x.val.1+x.val.2=n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp x.property
    simp only [he,tsum_const,Nat.card_eq_fintype_card,nsmul_eq_mul,Fintype.card_coe,Finset.Nat.card_antidiagonal,
      Nat.cast_add,Nat.cast_one]
  simp only [hsum]
  exact ⟨fun h => h.2,fun h => ⟨fun _ => (hasSum_fintype _).summable,h⟩⟩

lemma tsum_add_diagonal {f : ℕ→ℝ} (hf : ∀ n,0≤f n)
    (h : Summable (fun n : ℕ => (n+1:ℝ)*f n)) :
    (∑' x : ℕ×ℕ,f (x.1+x.2))=∑' n : ℕ,(n+1:ℝ)*f n := by
  have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff).mpr
    ((summable_add_diagonal_iff hf).mpr h)
  change Summable (fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
    f (x.2.val.1+x.2.val.2)) at hs
  rw [←Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  change (∑' x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n,
    f (x.2.val.1+x.2.val.2)) = _
  rw [hs.tsum_sigma' (fun _=>(hasSum_fintype _).summable)]
  apply tsum_congr
  intro n
  have he (x : Finset.HasAntidiagonal.antidiagonal n) : x.val.1+x.val.2=n :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp x.property
  simp only [he,tsum_const,Nat.card_eq_fintype_card,nsmul_eq_mul,Fintype.card_coe,Finset.Nat.card_antidiagonal,
    Nat.cast_add,Nat.cast_one]

 

theorem cutArchWeight_summable_iff (N : ℕ)
    (hK : ∀ k : ℤ,Summable (archWeight N k)) :
    Summable (cutArchWeight N) ↔ Summable (fun n : ℕ => (n+1:ℝ)*K N (n+1)) := by
  rw [summable_prod_of_nonneg (cutArchWeight_nonneg N)]
  have hi (x : ℕ×ℕ) : Summable (fun p => cutArchWeight N (x,p)) :=
    (summable_betweenArchWeight_iff N (-(x.1:ℤ)) ((x.2:ℤ)+1)).mpr (hK _)
  have he (x : ℕ×ℕ) : (∑' p, cutArchWeight N (x,p)) =
      (fun n : ℕ => K N (n+1)) (x.1+x.2) := cutArchWeight_path_sum N x
  have hh : Summable (fun x : ℕ×ℕ => ∑' p,cutArchWeight N (x,p)) ↔
      Summable (fun x : ℕ×ℕ => (fun n : ℕ => K N (n+1)) (x.1+x.2)) := summable_congr he
  exact ⟨fun h => (summable_add_diagonal_iff (fun n => K_nonneg N (n+1))).mp (hh.mp h.2),
    fun h => ⟨hi,hh.mpr ((summable_add_diagonal_iff (fun n => K_nonneg N (n+1))).mpr h)⟩⟩

 

theorem physical_moment_eq_cut_sum {N : ℕ} (hN : StripSumsFinite N) :
    moment N=∑' x,cutArchWeight N x := by
  have hs := (cutArchWeight_summable_iff N hN.1).mpr hN.2.2.2.2
  rw [hs.tsum_prod]
  simp only [cutArchWeight_path_sum]
  exact (tsum_add_diagonal (fun n => K_nonneg N (n+1)) hN.2.2.2.2).symm

end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology


lemma stepArchWeight_nonneg (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    0 ≤ stepArchWeight N s i j p := by
  unfold stepArchWeight
  split
  · exact betweenArchWeight_nonneg _ _ _ _
  · exact le_rfl

lemma stepArchWeight_le (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    stepArchWeight N s i j p ≤ betweenArchWeight (N+1) i j p := by
  unfold stepArchWeight
  split
  · exact le_rfl
  · exact betweenArchWeight_nonneg _ _ _ _

lemma stepArchWeight_reverse (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    stepArchWeight N s j i p.reverse=stepArchWeight N s i j p := by
  simp only [stepArchWeight,List.mem_reverse,betweenArchWeight_reverse]

lemma stepArchKernel_reverse (N : ℕ) (s i j : ℤ) :
    stepArchKernel N s j i=stepArchKernel N s i j := by
  rw [stepArchKernel,←reversePaths.tsum_eq]
  exact tsum_congr (stepArchWeight_reverse N s i j)

lemma betweenArchWeight_restrict (N : ℕ) (i j : ℤ) (p : List Triangle) :
    (if ∀ v∈p,v.2.1 < N then betweenArchWeight (N+1) i j p else 0)=betweenArchWeight N i j p := by
  by_cases h : ∀ v∈p,v.2.1 < N
  · have hpath : PathBetween (N+1) (up i 0) (up j 0) p ↔
        PathBetween N (up i 0) (up j 0) p := by
      constructor
      · intro hp; exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,h⟩
      · intro hp; exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,fun v hv => (h v hv).trans_le (Nat.le_succ _)⟩
    simp only [ite_eq_left h,betweenArchWeight,hpath]
  · rw [ite_eq_right h,betweenArchWeight,ite_eq_right]
    rintro ⟨_,hp⟩
    exact h hp.2.2.2.2

lemma stepArchWeight_translate (N : ℕ) (s i j q : ℤ) (p : List Triangle) :
    stepArchWeight N s (q+i) (q+j) (p.map (translateTriangle q)) =
      stepArchWeight N (s-q) i j p := by
  have hb : betweenArchWeight (N+1) (q+i) (q+j) (p.map (translateTriangle q))=
      betweenArchWeight (N+1) i j p := by
    simp only [betweenArchWeight,←translateTriangle_up,pathBetween_translate_iff,List.length_map,
      ne_eq,add_left_cancel_iff]
  have he : (∀ v∈p.map (translateTriangle q),steppedDomain N s v) ↔
      ∀ v∈p,steppedDomain N (s-q) v := by
    simp only [List.forall_mem_map,steppedDomain,translateTriangle]
    exact forall_congr' (fun v => forall_congr' (fun _ => by omega))
  simp only [stepArchWeight,he,hb]


lemma stepCutArchWeight_nonneg (N : ℕ) (s : ℤ) (x : (ℕ×ℕ)×List Triangle) :
    0 ≤ stepCutArchWeight N s x := stepArchWeight_nonneg _ _ _ _ _

lemma stepCutArchWeight_le (N : ℕ) (s : ℤ) (x : (ℕ×ℕ)×List Triangle) :
    stepCutArchWeight N s x ≤ cutArchWeight (N+1) x := stepArchWeight_le _ _ _ _ _

lemma stepCutArchWeight_summable (N : ℕ) (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (stepCutArchWeight N s) :=
  ((cutArchWeight_summable_iff (N+1) h.1).mpr h.2.2.2.2).of_nonneg_of_le
    (stepCutArchWeight_nonneg _ _) (stepCutArchWeight_le _ _)

lemma eventually_stepContains (N : ℕ) (s : ℤ) (p : List Triangle)
    (hp : ∀ v∈p,v.2.1 < N+1) :
    ∀ᶠ L : ℕ in atTop,∀ v∈p,steppedDomain N (s-(L:ℤ)) v := by
  have h : ∀ᶠ L : ℕ in atTop,∀ v∈p.toFinset,s-(L:ℤ) ≤ v.1 := by
    apply (p.toFinset.eventually_all).mpr
    intro v _
    filter_upwards [eventually_ge_atTop (s-v.1).toNat] with L hL
    omega
  filter_upwards [h] with L hL
  intro v hv
  have hband := hp v hv
  have hcol := hL v (List.mem_toFinset.mpr hv)
  unfold steppedDomain
  omega

lemma eventually_stepExcludes (N : ℕ) (s : ℤ) (p : List Triangle) :
    ∀ᶠ L : ℕ in atTop,∀ v∈p,steppedDomain N (s+(L:ℤ)) v ↔ v.2.1 < N := by
  have h : ∀ᶠ L : ℕ in atTop,∀ v∈p.toFinset,v.1 < s+(L:ℤ) := by
    apply (p.toFinset.eventually_all).mpr
    intro v _
    filter_upwards [eventually_ge_atTop (v.1-s+1).toNat] with L hL
    omega
  filter_upwards [h] with L hL
  intro v hv
  have hcol := hL v (List.mem_toFinset.mpr hv)
  unfold steppedDomain
  omega

lemma stepArchWeight_eventually_tall (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    ∀ᶠ L : ℕ in atTop,stepArchWeight N (s-(L:ℤ)) i j p=betweenArchWeight (N+1) i j p := by
  by_cases hp : ∀ v∈p,v.2.1 < N+1
  · filter_upwards [eventually_stepContains N s p hp] with L hL
    exact ite_eq_left hL
  · have hz : betweenArchWeight (N+1) i j p=0 := by
      apply ite_eq_right
      rintro ⟨_,ht⟩
      exact hp ht.2.2.2.2
    exact Eventually.of_forall (fun L => by simp only [stepArchWeight,hz,ite_self])

lemma stepArchWeight_eventually_short (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    ∀ᶠ L : ℕ in atTop,stepArchWeight N (s+(L:ℤ)) i j p=betweenArchWeight N i j p := by
  filter_upwards [eventually_stepExcludes N s p] with L hL
  have he : (∀ v∈p,steppedDomain N (s+(L:ℤ)) v) ↔ ∀ v∈p,v.2.1 < N := by
    exact forall_congr' (fun v => forall_congr' (hL v))
  simpa only [stepArchWeight,he] using betweenArchWeight_restrict N i j p

 

theorem step_cut_mass_tall_limit {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Tendsto (fun L : ℕ => ∑' x,stepCutArchWeight N (s-(L:ℤ)) x) atTop (𝓝 (moment (N+1))) := by
  rw [physical_moment_eq_cut_sum h]
  apply tendsto_tsum_of_dominated_convergence
    ((cutArchWeight_summable_iff (N+1) h.1).mpr h.2.2.2.2)
  · intro x
    exact tendsto_const_nhds.congr' ((stepArchWeight_eventually_tall N s (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2).mono (fun L hL => hL.symm))
  · exact Eventually.of_forall (fun L x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (stepCutArchWeight_nonneg _ _ _)]
      exact stepCutArchWeight_le _ _ _)

 

theorem step_cut_mass_short_limit {N : ℕ} (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N) :
    Tendsto (fun L : ℕ => ∑' x,stepCutArchWeight N (s+(L:ℤ)) x) atTop (𝓝 (moment N)) := by
  rw [physical_moment_eq_cut_sum h₀]
  apply tendsto_tsum_of_dominated_convergence
    ((cutArchWeight_summable_iff (N+1) h.1).mpr h.2.2.2.2)
  · intro x
    exact tendsto_const_nhds.congr' ((stepArchWeight_eventually_short N s (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2).mono (fun L hL => hL.symm))
  · exact Eventually.of_forall (fun L x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (stepCutArchWeight_nonneg _ _ _)]
      exact stepCutArchWeight_le _ _ _)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SidePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical



lemma rotateTriangle_band_lt {H : ℕ} {v : Triangle} (h : v.2.1<H) :
    (rotateTriangle H v).2.1<H := by simp only [rotateTriangle,ite_eq_left h]; omega

lemma rotateTriangle_involutive (H : ℕ) : Function.Involutive (rotateTriangle H) := by
  intro v
  by_cases h : v.2.1<H
  · have h' : H-1-v.2.1<H := by omega
    have he : H-1-(H-1-v.2.1)=v.2.1 := by omega
    simp [rotateTriangle,h,h',he]
  · simp [rotateTriangle,h]

lemma adjacent_rotate_iff {H : ℕ} {v w : Triangle} (hv : v.2.1<H) (hw : w.2.1<H) :
    adjacent (rotateTriangle H v) (rotateTriangle H w) ↔ adjacent v w := by
  rcases v with ⟨i,j,b⟩
  rcases w with ⟨i',j',b'⟩
  change j<H at hv
  change j'<H at hw
  cases b <;> cases b' <;> simp [adjacent,upDownAdjacent,rotateTriangle,hv,hw]
  all_goals omega

lemma PathBetween.rotate {H : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) :
    PathBetween H (rotateTriangle H a) (rotateTriangle H b) (p.map (rotateTriangle H)) := by
  refine ⟨?_,?_,hp.2.2.1.map (rotateTriangle_involutive H).injective,?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · apply (List.isChain_map _).mpr
    apply hp.2.2.2.1.imp_of_mem_imp
    intro v w hv hw h
    exact (adjacent_rotate_iff (hp.2.2.2.2 v hv) (hp.2.2.2.2 w hw)).mpr h
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact rotateTriangle_band_lt (hp.2.2.2.2 w hw)

lemma PathBetween.append_vertex {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v.2.1<H) (hn : v∉p) (hab : adjacent b v) :
    PathBetween H a v (p++[v]) := by
  refine ⟨?_,by simp,?_,?_,?_⟩
  · rw [List.head?_append,hp.1]; rfl
  · apply List.nodup_append.mpr
    refine ⟨hp.2.2.1,by simp,?_⟩
    intro x hx y hy hxy
    have hyv := List.mem_singleton.mp hy
    exact hn ((hxy.trans hyv) ▸ hx)
  · apply List.isChain_append.mpr
    refine ⟨hp.2.2.2.1,by simp,?_⟩
    simpa [hp.2.1] using hab
  · intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · exact hp.2.2.2.2 w hw
    · simpa using List.mem_singleton.mp hw ▸ hv



lemma stepSideWeight_nonneg (N : ℕ) (s i : ℤ) (p : List Triangle) :
    0 ≤ stepSideWeight N s i p := by
  unfold stepSideWeight
  split
  · exact (pow_pos rho_pos _).le
  · exact le_rfl



lemma sideToTallBridge_injective (N : ℕ) (s : ℤ) :
    Function.Injective (sideToTallBridge N s) := by
  intro p q h
  have h₁ := List.map_injective_iff.mpr (translateTriangle_injective (s-1))
  have h₂ := List.map_injective_iff.mpr (rotateTriangle_involutive (N+1)).injective
  unfold sideToTallBridge at h
  exact List.append_cancel_right ((List.reverse_inj).mp (h₂ (h₁ h)))

lemma sideToTallBridge_spec {N : ℕ} (s i : ℤ) {p : List Triangle}
    (hp : PathBetween (N+1) (up i 0) (up s N) p)
    (hD : ∀ v∈p,steppedDomain N s v) :
    IsPath (N+1) (down (s-1-i) N) (sideToTallBridge N s p) := by
  have hn : down (s-1) N ∉ p := by
    intro h
    have hh := hD _ h
    simp only [steppedDomain,down,lt_self_iff_false,false_or,true_and] at hh
    omega
  have hA : adjacent (up s N) (down (s-1) N) := by
    apply Or.inl
    exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inr (by change s-1+1=s; omega)⟩⟩
  have he := ((hp.append_vertex (Nat.lt_succ_self N) hn hA).reverse.rotate).translate (s-1)
  have h₀ : 0<N+1 := by omega
  simpa [sideToTallBridge,rotateTriangle_down,rotateTriangle_up,h₀,
    Nat.lt_succ_self,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using he

lemma sideToTallBridge_weight (N : ℕ) (s i : ℤ) (p : List Triangle) :
    rho * stepSideWeight N s i p ≤ bridgeWeight (N+1) (s-1-i) (sideToTallBridge N s p) := by
  unfold stepSideWeight
  split_ifs with hp
  · rw [bridgeWeight,ite_eq_left ⟨by omega,sideToTallBridge_spec s i hp.1 hp.2⟩]
    simp [sideToTallBridge,pow_succ,mul_comm]
  · simp only [mul_zero]
    exact bridgeWeight_nonneg _ _ _

lemma bridge_all_paths_summable {H : ℕ} (hH : StripSumsFinite H) :
    Summable (fun x : ℤ×List Triangle => bridgeWeight H x.1 x.2) := by
  apply (summable_prod_of_nonneg (fun x => bridgeWeight_nonneg _ _ _)).mpr
  exact ⟨hH.2.1,hH.2.2.2.1⟩

lemma bridge_all_paths_tsum {H : ℕ} (hH : StripSumsFinite H) :
    (∑' x : ℤ×List Triangle,bridgeWeight H x.1 x.2)=bridgeMass H :=
  (bridge_all_paths_summable hH).tsum_prod

 

theorem stepSideWeight_summable {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (fun x : ℤ×List Triangle =>stepSideWeight N s x.1 x.2) := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-1-x.1,sideToTallBridge N s x.2)
  have he : Function.Injective e := by
    intro x y h
    have hi := congrArg Prod.fst h
    have hp := (sideToTallBridge_injective N s) (congrArg Prod.snd h)
    have hxy : x.1=y.1 := by dsimp [e] at hi; omega
    exact Prod.ext hxy hp
  have hg := (bridge_all_paths_summable h).comp_injective he
  have hmul : Summable (fun x : ℤ×List Triangle =>rho * stepSideWeight N s x.1 x.2) :=
    hg.of_nonneg_of_le (fun x =>mul_nonneg rho_pos.le (stepSideWeight_nonneg _ _ _ _))
      (fun x =>sideToTallBridge_weight N s x.1 x.2)
  exact (summable_mul_left_iff rho_pos.ne').mp hmul

theorem stepSideMass_le_tall_bridge {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    rho * stepSideMass N s ≤ bridgeMass (N+1) := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-1-x.1,sideToTallBridge N s x.2)
  have he : Function.Injective e := by
    intro x y h
    have hi := congrArg Prod.fst h
    have hp := (sideToTallBridge_injective N s) (congrArg Prod.snd h)
    have hxy : x.1=y.1 := by dsimp [e] at hi; omega
    exact Prod.ext hxy hp
  have hs := stepSideWeight_summable s h
  have hb := bridge_all_paths_summable h
  have ht : rho * stepSideMass N s=∑' x : ℤ×List Triangle,rho * stepSideWeight N s x.1 x.2 := by
    rw [tsum_mul_left,hs.tsum_prod]; rfl
  rw [ht,←bridge_all_paths_tsum h]
  exact (hs.mul_left rho).tsum_le_tsum_of_inj e he (fun _ _ =>bridgeWeight_nonneg _ _ _)
    (fun x =>sideToTallBridge_weight N s x.1 x.2) hb



lemma bridgeToSide_injective (N : ℕ) (s k : ℤ) :
    Function.Injective (bridgeToSide N s k) := by
  intro p q h
  exact List.map_injective_iff.mpr (translateTriangle_injective (s-k))
    (List.append_cancel_right h)

lemma bridgeToSide_spec {N : ℕ} (hN : 1≤N) (s k : ℤ) {p : List Triangle}
    (hp : IsPath N (down k (N-1)) p) :
    PathBetween (N+1) (up (s-k) 0) (up s N) (bridgeToSide N s k p) ∧
      (∀ v∈bridgeToSide N s k p,steppedDomain N s v) := by
  have ht : PathBetween N (up (s-k) 0) (down s (N-1)) (p.map (translateTriangle (s-k))) := by
    simpa using (show PathBetween N (up 0 0) (down k (N-1)) p from hp).translate (s-k)
  have hn : up s N ∉ p.map (translateTriangle (s-k)) := by
    intro h
    exact (Nat.lt_irrefl N) (ht.2.2.2.2 _ h)
  have hA : adjacent (down s (N-1)) (up s N) := by
    apply Or.inr
    exact ⟨rfl,rfl,Or.inr ⟨by change N=N-1+1; omega,rfl⟩⟩
  have ht' : PathBetween (N+1) (up (s-k) 0) (down s (N-1)) (p.map (translateTriangle (s-k))) :=
    ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,fun v hv => (ht.2.2.2.2 v hv).trans_le (Nat.le_succ _)⟩
  refine ⟨ht'.append_vertex (Nat.lt_succ_self N) hn hA,?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv|hv
  · exact Or.inl (ht.2.2.2.2 v hv)
  · have he : v=up s N := List.mem_singleton.mp hv
    rw [he]
    exact Or.inr ⟨rfl,le_rfl⟩

lemma bridgeToSide_weight {N : ℕ} (hN : 1≤N) (s k : ℤ) (p : List Triangle) :
    rho * bridgeWeight N k p ≤ stepSideWeight N s (s-k) (bridgeToSide N s k p) := by
  unfold bridgeWeight
  split_ifs with hp
  · rw [stepSideWeight,ite_eq_left (bridgeToSide_spec hN s k hp.2)]
    simp [bridgeToSide,pow_succ,mul_comm]
  · simp only [mul_zero]
    exact stepSideWeight_nonneg _ _ _ _

 

theorem stepSideMass_ge_base_bridge {N : ℕ} (hN : 1≤N) (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N) :
    rho * bridgeMass N ≤ stepSideMass N s := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-x.1,bridgeToSide N s x.1 x.2)
  have he : Function.Injective e := by
    intro x y hxy
    have hi := congrArg Prod.fst hxy
    have h₁ : x.1=y.1 := by dsimp [e] at hi; omega
    have hp := congrArg Prod.snd hxy
    change bridgeToSide N s x.1 x.2=bridgeToSide N s y.1 y.2 at hp
    rw [h₁] at hp
    exact Prod.ext h₁ ((bridgeToSide_injective N s y.1) hp)
  have hb := bridge_all_paths_summable h₀
  have hs := stepSideWeight_summable s h
  have hsum : (∑' x : ℤ×List Triangle,stepSideWeight N s x.1 x.2)=stepSideMass N s :=
    hs.tsum_prod
  rw [←hsum,←bridge_all_paths_tsum h₀,←tsum_mul_left]
  exact Summable.tsum_le_tsum_of_inj e he (fun _ _ =>stepSideWeight_nonneg _ _ _ _)
    (fun x =>bridgeToSide_weight hN s x.1 x.2) (hb.mul_left rho) hs

end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology

lemma stepArchKernel_translate (N : ℕ) (s i j q : ℤ) :
    stepArchKernel N s (q+i) (q+j)=stepArchKernel N (s-q) i j := by
  rw [stepArchKernel,←(translatePaths q).tsum_eq]
  exact tsum_congr (stepArchWeight_translate N s i j q)


lemma stepCutKernel_eq (N : ℕ) (s q : ℤ) (x : ℕ×ℕ) :
    stepCutKernel N s q x=(∑' p,stepCutArchWeight N (s-q) (x,p)) := by
  have ha : q-(x.1:ℤ)=q+(-(x.1:ℤ)) := by ring
  have hb : q+(x.2:ℤ)+1=q+((x.2:ℤ)+1) := by ring
  rw [stepCutKernel,ha,hb,stepArchKernel_translate]
  rfl

lemma stepCutKernel_summable {N : ℕ} (s q : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (stepCutKernel N s q) := by
  exact (stepCutArchWeight_summable N (s-q) h).prod.congr
    (fun x => (stepCutKernel_eq N s q x).symm)

lemma stepCutMass_eq {N : ℕ} (s q : ℤ) (h : StripSumsFinite (N+1)) :
    stepCutMass N s q=∑' x,stepCutArchWeight N (s-q) x := by
  rw [stepCutMass,(stepCutArchWeight_summable N (s-q) h).tsum_prod]
  exact tsum_congr (stepCutKernel_eq N s q)

 
lemma tsum_prod_split_column {f : ℕ×ℕ → ℝ} (hf : Summable f) :
    (∑' x,f x)=(∑' a,f (a,0))+(∑' a,∑' b,f (a,b+1)) := by
  have h₀ : Summable (fun a : ℕ =>f (a,0)) :=
    hf.comp_injective (fun a b h =>congrArg Prod.fst h)
  have ht : Summable (fun x : ℕ×ℕ =>f (x.1,x.2+1)) :=
    hf.comp_injective (by intro a b h; apply Prod.ext <;> simp_all)
  rw [hf.tsum_prod,←h₀.tsum_add ht.prod]
  exact tsum_congr (fun a => (hf.prod_factor a).tsum_eq_zero_add)

 

lemma tsum_array_difference {f g : ℕ×ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hfg : ∀ a b,f (a,b+1)=g (a+1,b)) :
    (∑' x,f x)-(∑' x,g x)=(∑' a,f (a,0))-(∑' b,g (0,b)) := by
  rw [tsum_prod_split_column hf,hg.tsum_prod,hg.prod.tsum_eq_zero_add]
  have ht : (∑' a,∑' b,f (a,b+1))=∑' a,∑' b,g (a+1,b) :=
    tsum_congr (fun a =>tsum_congr (fun b =>hfg a b))
  rw [ht]
  ring



theorem step_cut_divergence {N : ℕ} (s i : ℤ) (h : StripSumsFinite (N+1)) :
    stepCutMass N s (i-1)-stepCutMass N s i=stepArchLeft N s i-stepArchRight N s i := by
  have he (a b : ℕ) : stepCutKernel N s (i-1) (a,b+1)=stepCutKernel N s i (a+1,b) := by
    unfold stepCutKernel
    congr 1 <;> push_cast <;> ring
  have hh := tsum_array_difference (stepCutKernel_summable s (i-1) h)
    (stepCutKernel_summable s i h) he
  have hl : (∑' a,stepCutKernel N s (i-1) (a,0))=stepArchLeft N s i := by
    apply tsum_congr
    intro a
    simp only [stepCutKernel,Nat.cast_zero,add_zero,sub_add_cancel]
    exact stepArchKernel_reverse _ _ _ _
  have hr : (∑' b,stepCutKernel N s i (0,b))=stepArchRight N s i := by
    simp only [stepCutKernel,Nat.cast_zero,sub_zero,stepArchRight]
  rw [hl,hr] at hh
  exact hh



lemma stepSideKernel_summable {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (stepSideKernel N s) := (stepSideWeight_summable s h).prod

 

theorem step_moment_identity {N : ℕ} (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N)
    (hflux : SteppedBoundaryFlux N s) :
    Real.sin (3*lambda)*(moment (N+1)-moment N)=Real.sin lambda*stepSideMass N s := by
  have hfin (L : ℕ) : Real.sin (3*lambda)*
      (stepCutMass N s ((L:ℤ)-1)-stepCutMass N s (-(L:ℤ)-1)) =
      Real.sin lambda * ∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),stepSideKernel N s i := by
    have hi (i : ℤ) : Real.sin lambda*stepSideKernel N s i=
        Real.sin (3*lambda)*(stepCutMass N s i-stepCutMass N s (i-1)) := by
      have hx := hflux i
      rw [←step_cut_divergence s i h] at hx
      linarith
    rw [Finset.mul_sum]
    simp_rw [hi]
    rw [←Finset.mul_sum]
    congr 1
    have hz := Finset.sum_Ico_int_sub L (fun i => stepCutMass N s (i-1))
    have hadd : ∀ i : ℤ,(i+1)-1=i := by intro i; ring
    simp only [hadd] at hz
    have hn : (∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),
        (stepCutMass N s i-stepCutMass N s (i-1)))=
        -(∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),
        (stepCutMass N s (i-1)-stepCutMass N s i)) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hn,hz]
    ring
  have hr : Tendsto (fun L : ℕ=>stepCutMass N s ((L:ℤ)-1)) atTop (𝓝 (moment (N+1))) := by
    have he (L : ℕ) : stepCutMass N s ((L:ℤ)-1)=∑' x,stepCutArchWeight N ((s+1)-(L:ℤ)) x := by
      rw [stepCutMass_eq s _ h]
      congr 3
      ring_nf
    simpa only [he] using step_cut_mass_tall_limit (s+1) h
  have hl : Tendsto (fun L : ℕ=>stepCutMass N s (-(L:ℤ)-1)) atTop (𝓝 (moment N)) := by
    have he (L : ℕ) : stepCutMass N s (-(L:ℤ)-1)=∑' x,stepCutArchWeight N ((s+1)+(L:ℤ)) x := by
      rw [stepCutMass_eq s _ h]
      congr 3
      ring_nf
    simpa only [he] using step_cut_mass_short_limit (s+1) h h₀
  have hz : Tendsto (fun L : ℕ=>∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),stepSideKernel N s i)
      atTop (𝓝 (stepSideMass N s)) :=
    (stepSideKernel_summable s h).hasSum.comp Finset.tendsto_Ico_neg
  exact tendsto_nhds_unique ((hr.sub hl).const_mul _) ((hz.const_mul _).congr (fun L=>(hfin L).symm))

end
 

 

noncomputable section
open scoped BigOperators Classical

lemma step_sines_pos : 0 < Real.sin lambda ∧ 0 < Real.sin (3*lambda) := by
  constructor <;> apply Real.sin_pos_of_pos_of_lt_pi <;>
    dsimp [lambda] <;> linarith [Real.pi_pos]

 

theorem moment_increment_bounds_of_boundary {N : ℕ} (hN : 1≤N) (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N)
    (hflux : SteppedBoundaryFlux N s)
    (hF₀ : c*archMass N+bridgeMass N=1)
    (hF₁ : c*archMass (N+1)+bridgeMass (N+1)=1) :
    ((Real.sin lambda/Real.sin (3*lambda))*rho)*bridgeMass N ≤ moment (N+1)-moment N ∧
    moment (N+1)-moment N ≤ ((Real.sin lambda/Real.sin (3*lambda))/rho)*bridgeMass N := by
  have hs := step_sines_pos
  have he := step_moment_identity s h h₀ hflux
  have hm : moment (N+1)-moment N =
      (Real.sin lambda / Real.sin (3*lambda))*stepSideMass N s := by
    apply (mul_left_cancel₀ hs.2.ne')
    calc
      Real.sin (3*lambda)*(moment (N+1)-moment N)=
        Real.sin lambda*stepSideMass N s := he
      _=Real.sin (3*lambda)*((Real.sin lambda/Real.sin (3*lambda))*stepSideMass N s) := by
        field_simp [hs.2.ne']
  have hmono : bridgeMass (N+1)≤bridgeMass N :=
    bridgeMass_le_of_finite_and_flux (Nat.le_succ N) h hF₀ hF₁
  have hupper : rho*stepSideMass N s≤bridgeMass N := (stepSideMass_le_tall_bridge s h).trans hmono
  have hlower := stepSideMass_ge_base_bridge hN s h h₀
  have hβ : 0≤Real.sin lambda/Real.sin (3*lambda) := (div_pos hs.1 hs.2).le
  constructor
  · rw [hm,mul_assoc]
    exact mul_le_mul_of_nonneg_left hlower hβ
  · have hsu : stepSideMass N s≤bridgeMass N/rho :=
      (le_div_iff₀ rho_pos).mpr (by simpa [mul_comm] using hupper)
    have hu := mul_le_mul_of_nonneg_left hsu hβ
    simpa only [hm,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hu

 

theorem increment_comparable_of_boundary
    (hfinite : ∀ N : ℕ,1≤N → StripSumsFinite N)
    (hstrip : ∀ N : ℕ,1≤N → c*archMass N+bridgeMass N=1)
    (hstep : ∀ N : ℕ,1≤N → ∃ s : ℤ,SteppedBoundaryFlux N s) :
    Comparable (fun N =>moment (N+1)-moment N) bridgeMass := by
  have hs := step_sines_pos
  refine ⟨(Real.sin lambda/Real.sin (3*lambda))*rho,
    (Real.sin lambda/Real.sin (3*lambda))/rho,
    mul_pos (div_pos hs.1 hs.2) rho_pos,div_pos (div_pos hs.1 hs.2) rho_pos,?_⟩
  intro N hN
  obtain ⟨s,h⟩ := hstep N hN
  exact moment_increment_bounds_of_boundary hN s (hfinite (N+1) (by omega))
    (hfinite N hN) h (hstrip N hN) (hstrip (N+1) (by omega))

 

theorem criticalStripMass_of_physical_identities_oai
    (hfinite : ∀ N : ℕ,1≤N → StripSumsFinite N)
    (hstrip : ∀ N : ℕ,1≤N → c*archMass N+bridgeMass N=1)
    (hstep : ∀ N : ℕ,1≤N → ∃ s : ℤ,SteppedBoundaryFlux N s)
    (hArch : ∀ N : ℕ,1≤N → ∃ g : Polynomial ℝ,
      MonicProblem N g ∧ moment N=(N:ℝ)*C-eta*g.coeff (N-1)) :
    CriticalStripMass := by
  apply criticalStripMass_iff_four_estimates.mpr
  refine ⟨hfinite,hstrip,increment_comparable_of_boundary hfinite hstrip hstep,?_⟩
  obtain ⟨lo,hi,hl,hh,hg⟩ := homogeneous_arch_coefficient_growth
  refine ⟨lo,hi,hl,hh,?_⟩
  intro N hN
  obtain ⟨g,hgm,he⟩ := hArch N hN
  simpa only [he] using hg N hN g hgm

end
end CriticalStrip

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.criticalStripMass_of_physical_identities_oai := @OAI.CriticalStrip.criticalStripMass_of_physical_identities_oai
