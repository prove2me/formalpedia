-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:18:42.782222+00:00
-- url     : https://prove2.me/submissions/3b0f6b76-4ec3-4696-87df-69f2be6f09b0

import Mathlib
import Definitions.Def_Q238L012
import Definitions.Def_Q238L031
import Definitions.Def_Q238L052
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialProject_run_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySurplusPostprocess_integral_spec_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_start_certificate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_PhaseSurplusProducer_normal_cost_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_ExtendBudget
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma extendBudget_at {V : Type*} (D : Finset V) (alpha : D → ℝ) (p : D) :
    extendBudget D alpha p.val = alpha p := by simp only [extendBudget,dite_eq_left p.property]

lemma sum_liftSubset {V : Type*} [DecidableEq V] (D C : Finset V) (hCD : C ⊆ D) (f : V → ℝ) :
    (∑ j ∈ Finset.univ.filter (fun j : D => j.val ∈ C), f j.val) = ∑ p ∈ C, f p := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_coe_sort D (fun p => if p ∈ C then f p else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun hp => hp.2,fun hp => ⟨hCD hp,hp⟩⟩

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_ClusterCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma cluster_sum (D I : Finset V) (assign : V → V) (f : V → V → ℝ) :
    (∑ i ∈ I, ∑ p ∈ cluster D assign i, f p i) =
      ∑ p ∈ D.filter (fun p => assign p ∈ I), f p (assign p) := by
  classical
  calc
    _ = ∑ i ∈ I, ∑ p ∈ D.filter (fun p => assign p = i), f p (assign p) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_eq_sum_filter D I assign _

lemma clusterCost_nonneg (D : Finset V) (assign : V → V) (i : V) :
    0 ≤ clusterCost D assign i := Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma total_cluster_cost (D O : Finset V) (hO : O.Nonempty) :
    partCost D O (nearest O hO) = cost D O := by
  classical
  unfold partCost clusterCost
  rw [cluster_sum]
  have hf : D.filter (fun p => nearest O hO p ∈ O) = D :=
    Finset.filter_eq_self.mpr (fun p _ => nearest_mem O hO p)
  rw [hf]
  exact Finset.sum_congr rfl (fun p _ => nearest_distance O hO p)

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ShortPrice
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus

lemma small_price_strict (U P c v A : ℝ) (hP : 0 ≤ P) (hc : 0 < c)
    (hv : 0 < v) (hv1 : v ≤ 1/12) (hvc : v ≤ c/1000)
    (hpay : (1-3*v)*U ≤ A) (hA : A ≤ (2-c/2+c/200)*P) :
    U ≤ (2-c/100)*P := by
  have ht : 0 < 1-3*v := by linarith
  have hvcP := mul_le_mul_of_nonneg_right hvc hP
  have hcv : 0 ≤ c*(v*P) := mul_nonneg hc.le (mul_nonneg hv.le hP)
  have htar : A ≤ (1-3*v)*((2-c/100)*P) := by
    nlinarith only [hA,hvcP,hcv,hP,hc]
  exact (mul_le_mul_iff_right₀ ht).mp (hpay.trans htar)

end MetricKMedianRecovery.Surplus

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

omit [Fintype V] in
lemma aggregate_gain (D O B : Finset V) (hO : O.Nonempty) (hBO : B ⊆ O)
    (alpha : V → ℝ) (lam c : ℝ)
    (hrow : ∀ i ∈ O, (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
      lam+2*clusterCost D (nearest O hO) i)
    (hstrict : ∀ i ∈ B, (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
      lam+(2-c/2)*clusterCost D (nearest O hO) i) :
    (∑ p ∈ D, alpha p) ≤ O.card*lam+2*cost D O-(c/2)*partCost D B (nearest O hO) := by
  classical
  let assign := nearest O hO
  have hpoint (i : V) (hi : i ∈ O) : (∑ p ∈ cluster D assign i, alpha p) ≤
      lam+2*clusterCost D assign i-(if i ∈ B then (c/2)*clusterCost D assign i else 0) := by
    by_cases hb : i ∈ B
    · rw [ite_eq_left hb]
      linarith only [hstrict i hb]
    · rw [ite_eq_right hb,sub_zero]
      exact hrow i hi
  have hsum := Finset.sum_le_sum (s := O) hpoint
  have hleft : (∑ i ∈ O, ∑ p ∈ cluster D assign i, alpha p) = ∑ p ∈ D, alpha p :=
    Finset.sum_fiberwise_of_maps_to (fun p _ => nearest_mem O hO p) alpha
  have hf : O.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun hi => hi.2,fun hi => ⟨hBO hi,hi⟩⟩
  have hcost : (∑ i ∈ O, clusterCost D assign i) = cost D O := total_cluster_cost D O hO
  rw [hleft,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    nsmul_eq_mul,← Finset.mul_sum,hcost,← Finset.sum_filter,hf,← Finset.mul_sum] at hsum
  exact hsum

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGapPos
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring

lemma strictnessGap_pos {T : ℝ} (hT : 0 < T) : 0 < strictnessGap T := by
  unfold strictnessGap
  positivity
lemma strictnessGap_le_one {T : ℝ} (hT : 0 < T) : strictnessGap T ≤ 1 := by
  have hd : 1 ≤ 200*(T+2) := by linarith
  have ht : 0 < 200*(T+2) := by positivity
  have hq : 1/(200*(T+2)) ≤ (1:ℝ) := (div_le_iff₀ ht).mpr (by nlinarith only [hd])
  have hq0 : 0 ≤ 1/(200*(T+2)) := by positivity
  unfold strictnessGap
  nlinarith

variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

omit [Fintype V] [MetricSpace V] [DecidableEq V] in
lemma sum_extended_budget (D : Finset V) (alpha : D → ℝ) :
    (∑ p ∈ D, extendBudget D alpha p) = ∑ j, alpha j := by
  rw [← Finset.sum_coe_sort D (extendBudget D alpha)]
  exact Finset.sum_congr rfl (fun j _ => extendBudget_at D alpha j)

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_IndexedCost
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma strict_on_points (D C F : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty)
    {v lam b : ℝ} {alpha : D → ℝ} (h : Dual (fun j : D => j.val) F v lam alpha)
    (i : V) (hi : i ∈ F) (hb : 0 < b)
    (hP : 0 < ∑ p ∈ C, dist p i) (hprice : lam ≤ b*(∑ p ∈ C, dist p i))
    (hsmall : v^2 ≤ strictnessGap b/(6*(b+2))) :
    (∑ p ∈ C, extendBudget D alpha p) ≤ lam+(2-strictnessGap b/2)*(∑ p ∈ C, dist p i) := by
  classical
  let C' := Finset.univ.filter (fun j : D => j.val ∈ C)
  have hC' : C'.Nonempty := by
    obtain ⟨p,hp⟩ := hC
    exact ⟨⟨p,hCD hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have hd : (∑ j ∈ C', dist i j.val) = ∑ p ∈ C, dist p i := by
    simpa only [dist_comm] using sum_liftSubset D C hCD (fun p => dist p i)
  have ha : (∑ j ∈ C', alpha j) = ∑ p ∈ C, extendBudget D alpha p := by
    calc
      _ = ∑ j ∈ C', extendBudget D alpha j.val :=
        Finset.sum_congr rfl (fun j _ => (extendBudget_at D alpha j).symm)
      _ = _ := sum_liftSubset D C hCD _
  have hh := h.2.2 C' hC' i hi b hb (hd ▸ hP) (hd ▸ hprice) hsmall
  simpa only [ha,hd] using hh

omit [DecidableEq V] in
lemma cluster_ge_one (D C F : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty)
    (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p) (i : V) (hi : i ∈ F) :
    1 ≤ ∑ p ∈ C, dist p i := by
  obtain ⟨p,hp⟩ := hC
  have hh := hfar i hi p (hCD hp)
  rw [dist_comm] at hh
  exact hh.trans (Finset.single_le_sum (fun q _ => (dist_nonneg : 0 ≤ dist q i)) hp)

omit [DecidableEq V] in
lemma comparison_ge_one (F D O : Finset V) (hD : D.Nonempty) (hO : O.Nonempty)
    (hOF : O ⊆ F) (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p) : 1 ≤ cost D O := by
  obtain ⟨p,hp⟩ := hD
  have hh := hfar (nearest O hO p) (hOF (nearest_mem O hO p)) p hp
  rw [dist_comm,nearest_distance] at hh
  exact hh.trans (Finset.single_le_sum (fun p _ => connection_nonneg O p) hp)

lemma countConstant_ge_ten : (10:ℝ) ≤ countConstant (1/100) := by
  unfold countConstant
  have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
  linarith only [hh]

variable [Fintype V]

omit [Fintype V] in

lemma small_cost (F D O S : Finset V) (hO : O.Nonempty) (hD : D.Nonempty) (hOF : O ⊆ F)
    (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p)
    (N : ℕ) (hN : 0 < N) (hcard : O.card ≤ N)
    (alpha : D → ℝ) (Q v : ℝ) (hdual : Dual (fun j : D => j.val) F v (2/(N:ℝ)^2) alpha)
    (hSQ : cost D S ≤ Q) (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ) ≤ strictnessGap (200*countConstant (1/100))/200)
    (hpay : (1-3*v)*Q ≤ ∑ j, alpha j) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  let C := countConstant (1/100)
  let c := strictnessGap (200*C)
  let lam := 2/(N:ℝ)^2
  let P := cost D O
  have hC : 10 ≤ C := countConstant_ge_ten
  have hT : 0 < 200*C := by linarith
  have hc : 0 < c := strictnessGap_pos hT
  have hc1 : c ≤ 1 := strictnessGap_le_one hT
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hNR1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hlam : 0 < lam := by dsimp [lam] <;> positivity
  have hlam2 : lam ≤ 2 := by
    dsimp [lam]
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    nlinarith only [hNR1]
  have hP1 : 1 ≤ P := comparison_ge_one F D O hD hO hOF hfar
  have hstrict (i : V) (hi : i ∈ O) :
      (∑ p ∈ cluster D (nearest O hO) i, extendBudget D alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i := by
    by_cases hne : (cluster D (nearest O hO) i).Nonempty
    · have hp := cluster_ge_one D (cluster D (nearest O hO) i) F (Finset.filter_subset _ _) hne hfar i (hOF hi)
      change 1 ≤ clusterCost D (nearest O hO) i at hp
      have hprice : lam ≤ 200*C*clusterCost D (nearest O hO) i := by
        nlinarith only [hp,hC,hlam2]
      exact strict_on_points D _ F (Finset.filter_subset _ _) hne hdual i (hOF hi) hT
        (show 0 < clusterCost D (nearest O hO) i by linarith only [hp]) hprice hsmall
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [clusterCost,hz,Finset.sum_empty,mul_zero,add_zero]
      exact hlam.le
  have hrow (i : V) (hi : i ∈ O) :
      (∑ p ∈ cluster D (nearest O hO) i, extendBudget D alpha p) ≤
        lam+2*clusterCost D (nearest O hO) i := by
    have hg := hstrict i hi
    have hpos := mul_nonneg hc.le (clusterCost_nonneg D (nearest O hO) i)
    nlinarith only [hg,hpos]
  have hg := aggregate_gain D O O hO (Finset.Subset.refl _) (extendBudget D alpha) lam c hrow hstrict
  rw [total_cluster_cost,sum_extended_budget] at hg
  have hnlam : (N:ℝ)*lam = 2/(N:ℝ) := by dsimp [lam]; field_simp
  have hpayprice : (O.card:ℝ)*lam ≤ (c/200)*P := by
    have hcast : (O.card:ℝ) ≤ N := by exact_mod_cast hcard
    have hh := mul_le_mul_of_nonneg_right hcast hlam.le
    rw [hnlam] at hh
    have hp := mul_le_mul_of_nonneg_left hP1 (by positivity : 0 ≤ c/200)
    exact hh.trans (hsize.trans (by simpa only [mul_one] using hp))
  have hA : (∑ j, alpha j) ≤ (2-c/2+c/200)*P := by
    dsimp [P] at *
    linarith only [hg,hpayprice]
  exact hSQ.trans (small_price_strict Q P c v _ (by linarith only [hP1]) hc hv hv1 hvc hpay hA)

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SortedDual
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
lemma equiv_dual_val (D : Finset V) (i : Fin D.card) : (equiv_dual D i).val=enum D i := rfl
lemma enum_symm (D : Finset V) (j : D) : enum D ((equiv_dual D).symm j)=j.val := by
  rw [←equiv_dual_val,Equiv.apply_symm_apply]
lemma image_enum (D : Finset V) : Finset.univ.image (enum D)=D := by
  ext j
  constructor
  · intro hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact enum_mem D i
  · intro hj
    exact Finset.mem_image.mpr ⟨(equiv_dual D).symm ⟨j,hj⟩,Finset.mem_univ _,enum_symm D ⟨j,hj⟩⟩
lemma sum_enum_dual {M : Type*} [AddCommMonoid M] (D : Finset V) (f : V→M) :
    (∑ j,f (enum D j))=∑ p∈D,f p := by
  rw [←Finset.sum_coe_sort D f]
  exact Equiv.sum_comp (equiv_dual D) (fun j:D=>f j.val)
variable [PseudoMetricSpace V]
lemma sum_cost (D S : Finset V) : (∑ j,nearestDistance (enum D j) S)=LocalSearch.cost D S := by
  exact sum_enum_dual D (fun p=>nearestDistance p S)
lemma dual_on_points (D F : Finset V) (v lam : ℝ) (alpha : Fin D.card→ℝ)
    (h : PhaseOriginalLedger.Dual (enum D) F v lam alpha) :
    PhaseOriginalLedger.Dual (fun j:D=>j.val) F v lam (alpha ∘ (equiv_dual D).symm) := by
  classical
  have hh : PhaseOriginalLedger.Dual (enum D ∘ (equiv_dual D).symm) F v lam
      (alpha ∘ (equiv_dual D).symm) := by
    let indexEquiv := (equiv_dual D).symm
    refine ⟨fun point=>h.1 (indexEquiv point),?_,?_⟩
    · intro facility facility_mem
      have sum_reindex := Equiv.sum_comp indexEquiv
        (fun index=>max (alpha index-2*dist facility (enum D index)) 0)
      simpa only [Function.comp_apply] using sum_reindex.trans_le (h.2.1 facility facility_mem)
    · intro clients clients_nonempty facility facility_mem price price_pos distances_pos price_bound gap_bound
      have distances_eq : (∑ index∈clients.image indexEquiv,dist facility (enum D index))=
          ∑ point∈clients,dist facility ((enum D ∘ indexEquiv) point) := by
        rw [Finset.sum_image]
        · rfl
        · exact fun _ _ _ _ equality=>indexEquiv.injective equality
      have alpha_eq : (∑ index∈clients.image indexEquiv,alpha index)=
          ∑ point∈clients,(alpha ∘ indexEquiv) point := by
        rw [Finset.sum_image]
        · rfl
        · exact fun _ _ _ _ equality=>indexEquiv.injective equality
      simpa only [distances_eq,alpha_eq] using h.2.2 (clients.image indexEquiv)
        (clients_nonempty.image indexEquiv) facility facility_mem price price_pos
        (distances_eq ▸ distances_pos) (distances_eq ▸ price_bound) gap_bound
  have he : enum D ∘ (equiv_dual D).symm = (fun j:D=>j.val) := by
    funext j
    exact enum_symm D j
  rw [he] at hh
  exact hh
omit [PseudoMetricSpace V] in
lemma sum_budget (D : Finset V) (alpha : Fin D.card→ℝ) :
    (∑ j:D,(alpha ∘ (equiv_dual D).symm) j)=∑ j,alpha j := Equiv.sum_comp (equiv_dual D).symm alpha
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
lemma produce_s238r_oai [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m))
    (h L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hh : 2≤h) (hkF : h+L≤F.card)
    (hN : N=D.card+F.card) (hM : 0<M)
    (hδ : ∀ p∈D,∀ i∈F,(δ p i:ℝ)=dist p i)
    (hmetric : ∀ i j,(δ (SortedIndex.enum D j) i:ℝ)=dist i (SortedIndex.enum D j))
    (hfar : ∀ i∈F,∀ p∈D,1≤dist i p)
    (hdiam : ∀ p∈D,∀ i∈F,δ p i≤M)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
    (hvc : (v:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/1000)
    (hsmall : (v:ℝ)^2≤ strictnessGap (200*Anchoring.countConstant (1/100))/(6*(200*Anchoring.countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N≤(v:ℝ))
    (hL : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤L)
    (hC : 2≤(1+v^2)^C) :
    ∃ S : Finset (Fin m),run v C (pack δ F D M h L)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=h+L ∧ LocalSearch.WidthLocalMin F D S 5 ∧
      ∀ O H : Finset (Fin m),∀ xi : ℝ,
        O⊆F→O.card=h→H⊆F→H.Nonempty→H.card+L=h→
        LocalSearch.cost D H≤(1+xi)*LocalSearch.cost D O→xi≤1→
        LocalSearch.cost D S≤(2-strictnessGap (200*Anchoring.countConstant (1/100))/100)*LocalSearch.cost D O := by
  classical
  have hn : 0<D.card := Finset.card_pos.mpr hD
  have hnN : D.card≤N := by omega
  have hhN : h≤N := by omega
  have hN3 : 3≤N := by omega
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  have hfar' (i : Fin m) (hi : i∈F) (j : Fin D.card) : 1≤dist i (SortedIndex.enum D j) :=
    hfar i hi _ (SortedIndex.enum_mem D j)
  have hdiam' (i : Fin m) (hi : i∈F) (j : Fin D.card) : dist i (SortedIndex.enum D j)≤((M:ℚ):ℝ) := by
    rw [←hmetric]
    exact_mod_cast hdiam _ (SortedIndex.enum_mem D j) i hi
  have hNQ : (1:ℚ)≤N := by exact_mod_cast (by omega : 1≤N)
  have hnQ : (1:ℚ)≤D.card := by exact_mod_cast hn
  have hMQ : (1:ℚ)≤M := by exact_mod_cast hM
  have hlo : (0:ℚ)<2/(N:ℚ)^2 := by positivity
  have hlohi : 2/(N:ℚ)^2≤8*(D.card:ℚ)*(M:ℚ) := by
    have htwo : 2/(N:ℚ)^2≤2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℚ)<N))).mpr
      nlinarith only [hNQ]
    have hprod : (1:ℚ)≤(D.card:ℚ)*(M:ℚ) := by
      simpa only [one_mul] using mul_le_mul hnQ hMQ (by norm_num : (0:ℚ)≤1) (by linarith : (0:ℚ)≤D.card)
    linarith only [htwo,hprod]
  let distance : Fin m→Fin D.card→ℚ := fun i j=>(δ (SortedIndex.enum D j) i:ℚ)
  let U := (start (SortedIndex.enum D) distance F v (2/(N:ℚ)^2) M N N
    (HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*M)+1) h).project
  have hdistance (i : Fin m) (j : Fin D.card) : (distance i j:ℝ)=dist i (SortedIndex.enum D j) := by
    simpa only [distance,Rat.cast_natCast] using hmetric i j
  have hrate : 0≤(1:ℝ)/2^N := by positivity
  have hcert := start_certificate_s238r (SortedIndex.enum D) distance hdistance F v (2/(N:ℚ)^2) M
    ((1:ℝ)/2^N) N N h hn hnN hh hF (by exact_mod_cast hM) hN3 hv
    (by linarith only [hv1]) hlo hrate hlohi
    (by simp only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,le_refl]) hfar' hdiam'
  simp only [Rat.cast_natCast] at hcert
  change LowCertificate (SortedIndex.enum D) F U v ((2/(N:ℚ)^2:ℚ):ℝ) h ∨
    NormalCertificate (SortedIndex.enum D) F U v ((2/(N:ℚ)^2:ℚ):ℝ) (8*(D.card:ℝ)*M) ((1:ℝ)/2^N)
      (HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*M)+1) h at hcert
  have hinit : BinaryInitialProject.run v C
      (BinaryInitialAuto.pack distance (SortedIndex.enum D) F (M:ℚ) h)=BinaryFinSet.encode U := by
    simpa only [←hN,U,Rat.cast_natCast] using BinaryInitialProject.run_pack_s238r distance (SortedIndex.enum D) hdistance F v M C h
      (by exact_mod_cast hv) hC hn hh hF (by exact_mod_cast hM) (by omega)
      (by linarith only [hv1]) (by simpa only [←hN] using hlohi) hfar' hdiam'
  have hpost : postInput v C (pack δ F D M h L)=BinarySurplusPostprocess.pack distance F U (h+L) := by
    simp only [postInput,pack,extractPrefix_pairBits,discardPrefix_pairBits]
    change encode [field 0 (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),
      field 1 (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),
      field 2 (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),
      BinaryInitialProject.run v C (BinaryInitialAuto.pack distance (SortedIndex.enum D) F M h),(h+L).bits]=_
    rw [hinit]
    simp only [BinaryInitialAuto.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinarySurplusPostprocess.pack]
  have hUdata : U⊆F ∧ U.Nonempty ∧ U.card≤h+L := by
    rcases hcert with hc|hc
    · exact ⟨hc.1,hc.2.1,hc.2.2.1.trans (by omega)⟩
    · exact ⟨hc.1,hc.2.1,hc.2.2.1.trans (by omega)⟩
  obtain ⟨S,he,hSF,hS,hSc,hSU,hlocal⟩ := BinarySurplusPostprocess.integral_spec_s238r δ (SortedIndex.enum D)
    (SortedIndex.enum_injective D) F U (h+L) hUdata.1 hUdata.2.1 hkF
    (fun j i hi=>hδ _ (SortedIndex.enum_mem D j) i hi)
    (fun j i hi=>hcap _ (SortedIndex.enum_mem D j) i hi)
  rw [SortedIndex.image_enum] at hSU hlocal
  rw [max_eq_left hUdata.2.2] at hSc
  refine ⟨S,?_,hSF,hS,hSc,hlocal,?_⟩
  · rw [run,Function.comp_apply,hpost]
    exact he
  intro O H xi hOF hOh hHF hH hHL hHcost hxi
  have hO : O.Nonempty := Finset.card_pos.mp (by omega)
  rcases hcert with hc|hc
  · obtain ⟨_,_,_,Q,alpha,hQ,hcost,hdual,hpay⟩ := hc
    rw [SortedIndex.sum_cost] at hcost
    have hd := SortedIndex.dual_on_points D F v ((2/(N:ℚ)^2:ℚ):ℝ) alpha hdual
    have hp : (1-3*(v:ℝ))*Q≤∑ j:D,(alpha ∘ (SortedIndex.equiv_dual D).symm) j := by
      rw [SortedIndex.sum_budget]
      exact hpay
    have hd' : PhaseOriginalLedger.Dual (fun j:D=>j.val) F v (2/(N:ℝ)^2)
        (alpha ∘ (SortedIndex.equiv_dual D).symm) := by
      simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast] using hd
    exact PhaseSurplusProducer.small_cost F D O S hO hD hOF hfar N (by omega) (by omega)
      _ Q v hd' (hSU.trans hcost) hv hv1 hvc hsmall hsize hp
  · obtain ⟨_,_,_,lam,Q,alpha,hlo',_,hQ,hcost,hdual,hpay⟩ := hc
    rw [SortedIndex.sum_cost] at hcost
    have hd := SortedIndex.dual_on_points D F v lam alpha hdual
    have hlam : 0<lam := (Rat.cast_pos.mpr hlo).trans_le hlo'
    have hP1 := PhaseSurplusProducer.comparison_ge_one F D O hD hO hOF hfar
    have hOe : (O.card:ℝ)≤N := by exact_mod_cast (by omega : O.card≤N)
    have hne : (D.card:ℝ)≤N := by exact_mod_cast hnN
    have hprod : (O.card:ℝ)*D.card≤(N:ℝ)^2 := by
      simpa only [pow_two] using mul_le_mul hOe hne (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have herr : (O.card:ℝ)*D.card*((1:ℝ)/2^N)≤(v:ℝ)*LocalSearch.cost D O := by
      calc
        _≤(N:ℝ)^2*((1:ℝ)/2^N) := mul_le_mul_of_nonneg_right hprod hrate
        _=(N:ℝ)^2/2^N := by ring
        _≤(v:ℝ) := herror
        _≤(v:ℝ)*LocalSearch.cost D O := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 hv.le
    have hp : (1-3*(v:ℝ))*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*((1:ℝ)/2^N))≤
        ∑ j:D,(alpha ∘ (SortedIndex.equiv_dual D).symm) j := by
      rw [SortedIndex.sum_budget,hOh]
      exact hpay
    exact PhaseSurplusProducer.normal_cost_s238r F D O S H hO hS hH hOF hSF hHF (by omega) L (by omega)
      (by omega) hlocal (by linarith only [hP1]) _ lam Q ((1:ℝ)/2^N) xi v hd hlam hQ
      (hSU.trans hcost) hHcost hxi hv hv1 hvc hsmall herr hp
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r_oai
