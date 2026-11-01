-- Prove2me | solution 2 for GeometryOfGraphs.FlowCut.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T11:50:37.397985+00:00
-- url     : https://prove2.me/submissions/eb66b550-c220-4ca4-a189-d2746b7e88fe

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option autoImplicit false

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

def capacitySet (N : Network V) : Set (Fin N.k → V → V → ℝ) :=
  {f | (∀ μ i j, 0 ≤ f μ i j) ∧ ∀ i j, ∑ μ, (f μ i j + f μ j i) ≤ N.C i j}

omit [Fintype V] [DecidableEq V] in
lemma zero_mem_capacitySet (N : Network V) : 0 ∈ capacitySet N := by
  constructor
  · simp
  · simpa using N.C_nonneg

omit [Fintype V] [DecidableEq V] in
lemma capacity_entry_bound (N : Network V) {f : Fin N.k → V → V → ℝ}
    (hf : f ∈ capacitySet N) (μ : Fin N.k) (i j : V) : f μ i j ≤ N.C i j := by
  have hh := Finset.single_le_sum (fun ν (_ : ν ∈ (Finset.univ : Finset (Fin N.k))) =>
    add_nonneg (hf.1 ν i j) (hf.1 ν j i)) (Finset.mem_univ μ)
  have hn := hf.1 μ j i
  linarith [hf.2 i j]

omit [Fintype V] [DecidableEq V] in
lemma capacitySet_closed (N : Network V) : IsClosed (capacitySet N) := by
  have he : capacitySet N =
      (⋂ μ, ⋂ i, ⋂ j, {f | (0 : ℝ) ≤ f μ i j}) ∩
      (⋂ i, ⋂ j, {f | ∑ μ, (f μ i j + f μ j i) ≤ N.C i j}) := by
    ext f
    simp [capacitySet]
  rw [he]
  apply IsClosed.inter
  · exact isClosed_iInter fun μ => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (by fun_prop)
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by fun_prop) continuous_const

omit [Fintype V] [DecidableEq V] in
lemma capacitySet_compact (N : Network V) : IsCompact (capacitySet N) := by
  apply isCompact_Icc.of_isClosed_subset (capacitySet_closed N)
  intro f hf
  exact ⟨hf.1, fun μ i j => capacity_entry_bound N hf μ i j⟩

omit [Fintype V] [DecidableEq V] in
lemma capacitySet_convex (N : Network V) : Convex ℝ (capacitySet N) := by
  intro f hf g hg a b ha hb hab
  constructor
  · intro μ i j
    exact add_nonneg (mul_nonneg ha (hf.1 μ i j)) (mul_nonneg hb (hg.1 μ i j))
  · intro i j
    change ∑ μ, (a * f μ i j + b * g μ i j + (a * f μ j i + b * g μ j i)) ≤ _
    calc
      _ = a * (∑ μ, (f μ i j + f μ j i)) + b * (∑ μ, (g μ i j + g μ j i)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro μ _
        ring
      _ ≤ a * N.C i j + b * N.C i j := add_le_add
        (mul_le_mul_of_nonneg_left (hf.2 i j) ha) (mul_le_mul_of_nonneg_left (hg.2 i j) hb)
      _ = N.C i j := by rw [← add_mul, hab, one_mul]

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma feasible_mem_capacity (N : Network V) {f : Fin N.k → V → V → ℝ} {lam : ℝ}
    (hf : N.IsFeasibleFlow f lam) : f ∈ capacitySet N := ⟨hf.1, hf.2.2⟩

lemma zero_feasible (N : Network V) : N.IsFeasibleFlow 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · simpa using N.C_nonneg

lemma feasible_value_bound (N : Network V) {μ : Fin N.k}
    (hD : 0 < N.D μ) (hst : N.s μ ≠ N.t μ)
    {lam : ℝ} {f : Fin N.k → V → V → ℝ} (hf : N.IsFeasibleFlow f lam) :
    lam ≤ (∑ j, N.C (N.s μ) j) / N.D μ := by
  have hc := hf.2.1 μ (N.s μ)
  simp only [ite_true, hst, ite_false, sub_zero, mul_one] at hc
  have hi : 0 ≤ ∑ j, f μ j (N.s μ) := Finset.sum_nonneg fun j _ => hf.1 μ j (N.s μ)
  have ho : ∑ j, f μ (N.s μ) j ≤ ∑ j, N.C (N.s μ) j :=
    Finset.sum_le_sum fun j _ => capacity_entry_bound N (feasible_mem_capacity N hf) μ (N.s μ) j
  apply (le_div_iff₀ hD).mpr
  linarith

lemma feasible_values_bddAbove (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) :
    BddAbove {lam : ℝ | 0 ≤ lam ∧ ∃ f, N.IsFeasibleFlow f lam} := by
  obtain ⟨μ,hD,hst⟩ := hpos
  refine ⟨(∑ j, N.C (N.s μ) j) / N.D μ, ?_⟩
  rintro lam ⟨_,f,hf⟩
  exact feasible_value_bound N hD hst hf

lemma maxflow_nonneg (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) : 0 ≤ N.maxflow := by
  exact le_csSup (feasible_values_bddAbove N hpos) ⟨le_rfl, 0, zero_feasible N⟩

lemma feasible_le_maxflow (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) {lam : ℝ}
    (hlam : 0 ≤ lam) {f : Fin N.k → V → V → ℝ} (hf : N.IsFeasibleFlow f lam) :
    lam ≤ N.maxflow := le_csSup (feasible_values_bddAbove N hpos) ⟨hlam,f,hf⟩

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

def divergenceLinear (N : Network V) :
    (Fin N.k → V → V → ℝ) →ₗ[ℝ] (Fin N.k → V → ℝ) where
  toFun f μ v := ∑ j, f μ v j - ∑ j, f μ j v
  map_add' f g := by ext μ v; simp [Finset.sum_add_distrib]; ring
  map_smul' a f := by ext μ v; simp [Finset.mul_sum, mul_sub]

def demandVector (N : Network V) : Fin N.k → V → ℝ :=
  fun μ v => N.D μ * ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))

lemma demand_not_image (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) {lam : ℝ} (hlam : N.maxflow < lam) :
    lam • demandVector N ∉ divergenceLinear N '' capacitySet N := by
  rintro ⟨f,hf,he⟩
  have hln : 0 ≤ lam := (maxflow_nonneg N hpos).trans hlam.le
  have hfeas : N.IsFeasibleFlow f lam := by
    refine ⟨hf.1, ?_, hf.2⟩
    intro μ v
    have hh := congrFun (congrFun he μ) v
    simpa [divergenceLinear, demandVector, mul_assoc] using hh
  exact (not_le_of_gt hlam) (feasible_le_maxflow N hpos hln hfeas)

lemma separating_functional (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) {lam : ℝ} (hlam : N.maxflow < lam) :
    ∃ L : (Fin N.k → V → ℝ) →ₗ[ℝ] ℝ,
      0 < L (demandVector N) ∧
      ∀ f ∈ capacitySet N, L (divergenceLinear N f) < lam * L (demandVector N) := by
  have hc : Continuous (divergenceLinear N) := by
    change Continuous (fun f : Fin N.k → V → V → ℝ => fun μ v => ∑ j, f μ v j - ∑ j, f μ j v)
    fun_prop
  obtain ⟨L,a,hLa,ha⟩ := geometric_hahn_banach_closed_point
    ((capacitySet_convex N).linear_image (divergenceLinear N))
    ((capacitySet_compact N).image hc).isClosed (demand_not_image N hpos hlam)
  have h0 := hLa 0 ⟨0, zero_mem_capacitySet N, map_zero _⟩
  simp only [map_zero] at h0
  have ht : a < lam * L (demandVector N) := by simpa using ha
  refine ⟨L.toLinearMap, ?_, ?_⟩
  · have hl : 0 < lam := lt_of_le_of_lt (maxflow_nonneg N hpos) hlam
    change 0 < L (demandVector N)
    exact (mul_pos_iff_of_pos_left hl).mp (lt_trans h0 ht)
  · intro f hf
    exact (hLa _ ⟨f,hf,rfl⟩).trans ht

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma functional_coefficients {k : ℕ} (L : (Fin k → V → ℝ) →ₗ[ℝ] ℝ) :
    ∃ p : Fin k → V → ℝ, ∀ b, L b = ∑ μ, ∑ v, p μ v * b μ v := by
  let p : Fin k → V → ℝ := fun μ v => L ((fun ν w => if ν = μ ∧ w = v then 1 else 0))
  refine ⟨p, ?_⟩
  intro b
  have he : (∑ μ, ∑ v, b μ v • (fun ν w => if ν = μ ∧ w = v then (1 : ℝ) else 0)) = b := by
    ext μ v
    simp [Finset.sum_apply, ite_and]
  conv_lhs => rw [← he, map_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro v _
  dsimp [p]
  ring

lemma pairing_demand (N : Network V) (p : Fin N.k → V → ℝ) :
    (∑ μ, ∑ v, p μ v * demandVector N μ v) =
      ∑ μ, N.D μ * (p μ (N.s μ) - p μ (N.t μ)) := by
  apply Finset.sum_congr rfl
  intro μ _
  unfold demandVector
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp [mul_comm]

omit [DecidableEq V] in
lemma pairing_divergence (N : Network V) (p : Fin N.k → V → ℝ)
    (f : Fin N.k → V → V → ℝ) :
    (∑ μ, ∑ v, p μ v * divergenceLinear N f μ v) =
      ∑ μ, ∑ i, ∑ j, (p μ i - p μ j) * f μ i j := by
  apply Finset.sum_congr rfl
  intro μ _
  simp only [divergenceLinear, LinearMap.coe_mk, AddHom.coe_mk, mul_sub,
    Finset.mul_sum, Finset.sum_sub_distrib, sub_mul]
  congr 1
  exact Finset.sum_comm

lemma separating_potentials (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) {lam : ℝ} (hlam : N.maxflow < lam) :
    ∃ p : Fin N.k → V → ℝ,
      0 < ∑ μ, N.D μ * (p μ (N.s μ) - p μ (N.t μ)) ∧
      ∀ f ∈ capacitySet N, (∑ μ, ∑ i, ∑ j, (p μ i - p μ j) * f μ i j) <
        lam * ∑ μ, N.D μ * (p μ (N.s μ) - p μ (N.t μ)) := by
  obtain ⟨L,hL,hf⟩ := separating_functional N hpos hlam
  obtain ⟨p,hp⟩ := functional_coefficients L
  refine ⟨p, ?_, ?_⟩
  · simpa only [hp, pairing_demand] using hL
  · intro f hfc
    simpa only [hp, pairing_demand, pairing_divergence] using hf f hfc

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def directedMass (a b x y : ℝ) : ℝ :=
  (if b ≤ a then x else 0) + (if b < a then y else 0)

lemma directedMass_nonneg {a b x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ directedMass a b x y := by unfold directedMass; split_ifs <;> linarith

lemma directedMass_add_reverse (a b x y : ℝ) :
    directedMass a b x y + directedMass b a y x = x+y := by
  unfold directedMass
  split_ifs <;> linarith

lemma directedMass_net (a b x y : ℝ) :
    (a-b) * (directedMass a b x y - directedMass b a y x) = |a-b| * (x+y) := by
  unfold directedMass
  rcases lt_trichotomy a b with h|h|h
  · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_pos h.le, if_pos h,
      abs_of_neg (sub_neg.mpr h)]
    ring
  · subst b
    simp
  · rw [if_pos h.le, if_pos h, if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le),
      abs_of_pos (sub_pos.mpr h)]
    ring

lemma pairing_eq_half_net {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → V → ℝ) (f : ι → V → V → ℝ) :
    (∑ μ, ∑ i, ∑ j, (p μ i-p μ j)*f μ i j) =
      (1/2:ℝ) * ∑ i, ∑ j, ∑ μ, (p μ i-p μ j)*(f μ i j-f μ j i) := by
  have hr : (∑ μ, ∑ i, ∑ j, (p μ i-p μ j)*f μ j i) =
      -(∑ μ, ∑ i, ∑ j, (p μ i-p μ j)*f μ i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : (∑ i, ∑ j, ∑ μ, (p μ i-p μ j)*(f μ i j-f μ j i)) =
      ∑ μ, ∑ i, ∑ j, (p μ i-p μ j)*(f μ i j-f μ j i) := by
    calc
      _ = ∑ i, ∑ μ, ∑ j, (p μ i-p μ j)*(f μ i j-f μ j i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hs]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hr]
  ring

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} {k : ℕ} [Nonempty (Fin k)]

noncomputable def potentialMetric (p : Fin k → V → ℝ) (i j : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun μ => |p μ i - p μ j|)

lemma potentialMetric_attained (p : Fin k → V → ℝ) (i j : V) :
    ∃ μ, potentialMetric p i j = |p μ i - p μ j| := by
  obtain ⟨μ,_,hμ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun μ => |p μ i - p μ j|)
  exact ⟨μ,hμ⟩

lemma abs_sub_le_potentialMetric (p : Fin k → V → ℝ) (μ : Fin k) (i j : V) :
    |p μ i - p μ j| ≤ potentialMetric p i j :=
  Finset.le_sup' (fun ν => |p ν i - p ν j|) (Finset.mem_univ μ)

lemma potentialMetric_nonneg (p : Fin k → V → ℝ) (i j : V) : 0 ≤ potentialMetric p i j := by
  obtain ⟨μ,hμ⟩ := potentialMetric_attained p i j
  rw [hμ]
  exact abs_nonneg _

lemma potentialMetric_self (p : Fin k → V → ℝ) (i : V) : potentialMetric p i i = 0 := by
  obtain ⟨μ,hμ⟩ := potentialMetric_attained p i i
  simpa using hμ

lemma potentialMetric_symm (p : Fin k → V → ℝ) (i j : V) :
    potentialMetric p i j = potentialMetric p j i := by
  unfold potentialMetric
  congr 1
  funext μ
  exact abs_sub_comm _ _

lemma potentialMetric_triangle (p : Fin k → V → ℝ) (i j l : V) :
    potentialMetric p i l ≤ potentialMetric p i j + potentialMetric p j l := by
  obtain ⟨μ,hμ⟩ := potentialMetric_attained p i l
  rw [hμ]
  exact (abs_sub_le (p μ i) (p μ j) (p μ l)).trans
    (add_le_add (abs_sub_le_potentialMetric p μ i j) (abs_sub_le_potentialMetric p μ j l))

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma exists_maximizing_flow (N : Network V) [Nonempty (Fin N.k)] (p : Fin N.k → V → ℝ) :
    ∃ f ∈ capacitySet N,
      (∑ μ, ∑ i, ∑ j, (p μ i-p μ j)*f μ i j) =
        (1/2:ℝ) * ∑ i, ∑ j, N.C i j * potentialMetric p i j := by
  classical
  choose a ha using potentialMetric_attained p
  let h : Fin N.k → V → V → ℝ := fun μ i j => if μ = a i j then N.C i j / 2 else 0
  have hn : ∀ μ i j, 0 ≤ h μ i j := by
    intro μ i j
    dsimp [h]
    split_ifs
    · exact div_nonneg (N.C_nonneg i j) (by norm_num)
    · exact le_rfl
  have hsum : ∀ i j, ∑ μ, h μ i j = N.C i j / 2 := by intro i j; simp [h]
  have hw : ∀ i j, ∑ μ, |p μ i-p μ j| * h μ i j = N.C i j / 2 * potentialMetric p i j := by
    intro i j
    simp only [h, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ha i j]
    ring
  let f : Fin N.k → V → V → ℝ := fun μ i j => directedMass (p μ i) (p μ j) (h μ i j) (h μ j i)
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro μ i j
    exact directedMass_nonneg (hn μ i j) (hn μ j i)
  · intro i j
    change (∑ μ, (directedMass (p μ i) (p μ j) (h μ i j) (h μ j i) +
      directedMass (p μ j) (p μ i) (h μ j i) (h μ i j))) ≤ N.C i j
    simp_rw [directedMass_add_reverse]
    rw [Finset.sum_add_distrib, hsum, hsum, N.C_symm j i]
    linarith
  · rw [pairing_eq_half_net]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (∑ μ, (p μ i-p μ j)*(directedMass (p μ i) (p μ j) (h μ i j) (h μ j i) -
      directedMass (p μ j) (p μ i) (h μ j i) (h μ i j))) = _
    simp_rw [directedMass_net, mul_add]
    rw [Finset.sum_add_distrib, hw]
    have hw' : (∑ μ, |p μ i-p μ j| * h μ j i) = N.C j i/2*potentialMetric p j i := by
      simpa only [abs_sub_comm] using hw j i
    rw [hw', N.C_symm j i, potentialMetric_symm p j i]
    ring

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma approximate_metric_dual (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) {lam : ℝ} (hlam : N.maxflow < lam) :
    ∃ d : V → V → ℝ,
      (∀ i j, 0 ≤ d i j) ∧ (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧
      (∀ i j l, d i l ≤ d i j + d j l) ∧
      0 < (∑ μ, N.D μ * d (N.s μ) (N.t μ)) ∧
      (1/2:ℝ)*(∑ i, ∑ j, N.C i j*d i j) < lam*(∑ μ, N.D μ*d (N.s μ) (N.t μ)) := by
  obtain ⟨μ,hD,hst⟩ := hpos
  let _ : Nonempty (Fin N.k) := ⟨μ⟩
  obtain ⟨p,hp,hf⟩ := separating_potentials N ⟨μ,hD,hst⟩ hlam
  obtain ⟨f,hfc,he⟩ := exists_maximizing_flow N p
  have hB : (∑ ν, N.D ν*(p ν (N.s ν)-p ν (N.t ν))) ≤
      ∑ ν, N.D ν*potentialMetric p (N.s ν) (N.t ν) := by
    apply Finset.sum_le_sum
    intro ν _
    apply mul_le_mul_of_nonneg_left _ (N.D_nonneg ν)
    exact (le_abs_self _).trans (abs_sub_le_potentialMetric p ν _ _)
  refine ⟨potentialMetric p, potentialMetric_nonneg p, potentialMetric_self p,
    potentialMetric_symm p, potentialMetric_triangle p, hp.trans_le hB, ?_⟩
  rw [← he]
  exact (hf f hfc).trans_le (mul_le_mul_of_nonneg_left hB
    ((maxflow_nonneg N ⟨μ,hD,hst⟩).trans hlam.le))

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cap_nonneg (N : Network V) (S : Finset V) : 0 ≤ N.Cap S := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => N.C_nonneg i j

omit [Fintype V] in
lemma dem_nonneg (N : Network V) (S : Finset V) : 0 ≤ N.Dem S := by
  exact Finset.sum_nonneg fun μ _ => N.D_nonneg μ

omit [Fintype V] in
lemma exists_positive_cut (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) : ∃ S : Finset V, 0 < N.Dem S := by
  obtain ⟨μ,hD,hst⟩ := hpos
  refine ⟨{N.s μ}, hD.trans_le ?_⟩
  apply Finset.single_le_sum (fun ν _ => N.D_nonneg ν)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact Or.inl (Ne.symm hst)

lemma exists_minimum_cut (N : Network V)
    (hpos : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) :
    ∃ S : Finset V, 0 < N.Dem S ∧ 0 ≤ N.Cap S / N.Dem S ∧
      ∀ T : Finset V, (N.Cap S/N.Dem S)*N.Dem T ≤ N.Cap T := by
  classical
  let F : Finset (Finset V) := Finset.univ.filter (fun S => 0 < N.Dem S)
  have hF : F.Nonempty := by
    obtain ⟨S,hS⟩ := exists_positive_cut N hpos
    exact ⟨S, by simp [F,hS]⟩
  obtain ⟨S,hS,hmin⟩ := Finset.exists_min_image F (fun S => N.Cap S / N.Dem S) hF
  have hDS : 0 < N.Dem S := (Finset.mem_filter.mp hS).2
  refine ⟨S,hDS,div_nonneg (cap_nonneg N S) hDS.le,?_⟩
  intro T
  by_cases ht : 0 < N.Dem T
  · exact (le_div_iff₀ ht).mp (hmin T (by simp [F,ht]))
  · have he : N.Dem T = 0 := le_antisymm (le_of_not_gt ht) (dem_nonneg N T)
    rw [he, mul_zero]
    exact cap_nonneg N T

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def bernoulliWeight {J : Type*} [Fintype J] (p : ℝ) (a : J → Bool) : ℝ :=
  ∏ i, if a i then p else 1 - p

def avoids {J : Type*} (A : Finset J) (a : J → Bool) : Prop :=
  ∀ i ∈ A, a i = false

lemma bernoulliWeight_nonneg {J : Type*} [Fintype J] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (a : J → Bool) : 0 ≤ bernoulliWeight p a := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

lemma bernoulliWeight_sum {J : Type*} [Fintype J] (p : ℝ) :
    ∑ a : J → Bool, bernoulliWeight p a = 1 := by
  classical
  have h := Fintype.prod_sum (fun (_ : J) (b : Bool) => if b then p else 1 - p)
  simpa [bernoulliWeight] using! h.symm

lemma bernoulli_avoid_factor {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ) (A : Finset J) (a : J → Bool) :
    (if avoids A a then bernoulliWeight p a else 0) =
      ∏ i, if i ∈ A then (if a i then 0 else 1 - p) else (if a i then p else 1 - p) := by
  classical
  by_cases h : avoids A a
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ A
    · simp [hi, h i hi]
    · simp [hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hai⟩ : ∃ i ∈ A, a i ≠ false := by
      by_contra hn
      apply h
      intro i hi
      by_contra hai
      exact hn ⟨i, hi, hai⟩
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases ha : a i <;> simp_all

lemma bernoulli_avoid_mass {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ) (A : Finset J) :
    ∑ a : J → Bool, (if avoids A a then bernoulliWeight p a else 0) = (1 - p) ^ A.card := by
  classical
  simp_rw [bernoulli_avoid_factor]
  have h := Fintype.prod_sum (fun (i : J) (b : Bool) =>
    if i ∈ A then (if b then 0 else 1 - p) else (if b then p else 1 - p))
  simpa [Finset.prod_ite] using! h.symm

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

lemma bernoulli_miss_lower {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * p ≤ (1 - p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1)
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg p]

lemma bernoulli_miss_reciprocal {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp1) _
    have hfac : (1 - p) * (1 + ((n : ℝ) + 1) * p) ≤ 1 + (n : ℝ) * p := by
      nlinarith [sq_nonneg p]
    have hh := mul_le_mul_of_nonneg_left hfac hn
    rw [pow_succ]
    push_cast
    nlinarith

lemma bernoulli_hit_lower {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (n : ℝ) * p / (1 + (n : ℝ) * p) ≤ 1 - (1 - p) ^ n := by
  have hd : 0 < 1 + (n : ℝ) * p := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith [bernoulli_miss_reciprocal hp hp1 n]

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

lemma avoids_union {J : Type*} [DecidableEq J] (A B : Finset J) (a : J → Bool) :
    avoids (A ∪ B) a ↔ avoids A a ∧ avoids B a := by
  simp only [avoids, Finset.mem_union]
  aesop

lemma bernoulli_miss_hit_mass {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ) (A B : Finset J) (hd : Disjoint A B) :
    ∑ a : J → Bool, (if avoids A a ∧ ¬ avoids B a then bernoulliWeight p a else 0) =
      (1 - p) ^ A.card * (1 - (1 - p) ^ B.card) := by
  classical
  have he (a : J → Bool) :
      (if avoids A a ∧ ¬ avoids B a then bernoulliWeight p a else 0) =
        (if avoids A a then bernoulliWeight p a else 0) -
        (if avoids (A ∪ B) a then bernoulliWeight p a else 0) := by
    by_cases ha : avoids A a <;> by_cases hb : avoids B a <;>
      simp [ha, hb, avoids_union]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, bernoulli_avoid_mass, bernoulli_avoid_mass,
    Finset.card_union_of_disjoint hd, pow_add]
  ring

lemma bernoulli_miss_hit_lower {J : Type*} [Fintype J] [DecidableEq J]
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A B : Finset J) (hd : Disjoint A B)
    (ha : (A.card : ℝ) * p ≤ 1 / 4) (hb : 1 / 8 ≤ (B.card : ℝ) * p) :
    (1 / 12 : ℝ) ≤
      ∑ a : J → Bool, (if avoids A a ∧ ¬ avoids B a then bernoulliWeight p a else 0) := by
  rw [bernoulli_miss_hit_mass p A B hd]
  have hmiss : (3 / 4 : ℝ) ≤ (1 - p) ^ A.card := by
    linarith [bernoulli_miss_lower hp hp1 A.card]
  have hpow : 0 ≤ (1 - p) ^ B.card := pow_nonneg (sub_nonneg.mpr hp1) _
  have hh := bernoulli_miss_reciprocal hp hp1 B.card
  have hhit : (1 / 9 : ℝ) ≤ 1 - (1 - p) ^ B.card := by
    nlinarith [mul_nonneg hpow (sub_nonneg.mpr hb)]
  have hm := mul_le_mul hmiss hhit (by norm_num : (0 : ℝ) ≤ 1 / 9)
    (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 4) hmiss)
  norm_num at hm ⊢
  exact hm

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def subsetDistance {V J : Type*} (d : V → V → ℝ) (z : J → V)
    (A : Finset J) (x : V) : ℝ :=
  if h : A.Nonempty then A.inf' h (fun i => d x (z i)) else 0

lemma subsetDistance_le {V J : Type*} (d : V → V → ℝ) (z : J → V)
    {A : Finset J} {i : J} (hi : i ∈ A) (x : V) : subsetDistance d z A x ≤ d x (z i) := by
  rw [subsetDistance, dif_pos ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

lemma le_subsetDistance {V J : Type*} (d : V → V → ℝ) (z : J → V)
    {A : Finset J} (hA : A.Nonempty) (x : V) {r : ℝ}
    (hr : ∀ i ∈ A, r ≤ d x (z i)) : r ≤ subsetDistance d z A x := by
  rw [subsetDistance, dif_pos hA]
  exact Finset.le_inf' hA _ hr

lemma subsetDistance_attained {V J : Type*} (d : V → V → ℝ) (z : J → V)
    {A : Finset J} (hA : A.Nonempty) (x : V) :
    ∃ i ∈ A, subsetDistance d z A x = d x (z i) := by
  rw [subsetDistance, dif_pos hA]
  obtain ⟨i, hi, he⟩ := (Finset.inf'_le_iff hA).mp
    (le_refl (A.inf' hA (fun i => d x (z i))))
  exact ⟨i, hi, le_antisymm (Finset.inf'_le _ hi) he⟩

lemma subsetDistance_abs_sub_le {V J : Type*} (d : V → V → ℝ) (z : J → V)
    (hn : ∀ x y, 0 ≤ d x y) (hs : ∀ x y, d x y = d y x)
    (ht : ∀ x y w, d x w ≤ d x y + d y w) (A : Finset J) (x y : V) :
    |subsetDistance d z A x - subsetDistance d z A y| ≤ d x y := by
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi, hei⟩ := subsetDistance_attained d z hA x
    obtain ⟨j, hj, hej⟩ := subsetDistance_attained d z hA y
    have hx := subsetDistance_le d z hj x
    have hy := subsetDistance_le d z hi y
    have hxy := ht x y (z j)
    have hyx := ht y x (z i)
    rw [hs y x] at hyx
    rw [abs_le]
    constructor <;> linarith
  · simp only [subsetDistance, dif_neg hA, sub_self, abs_zero]
    exact hn x y

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def selected {J : Type*} [Fintype J] (a : J → Bool) : Finset J :=
  Finset.univ.filter fun i => a i = true

lemma exists_selected_of_not_avoids {J : Type*} [Fintype J]
    (a : J → Bool) (B : Finset J) (hb : ¬ avoids B a) :
    ∃ i ∈ B, i ∈ selected a := by
  classical
  obtain ⟨i, hi, hai⟩ : ∃ i ∈ B, a i ≠ false := by
    by_contra hn
    apply hb
    intro i hi
    by_contra hai
    exact hn ⟨i, hi, hai⟩
  refine ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  cases h : a i <;> simp_all

lemma selected_distance_gap {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (a : J → Bool) (x y : V) (r s : ℝ)
    (hm : avoids (Finset.univ.filter (fun i => d x (z i) < r)) a)
    (hh : ¬ avoids (Finset.univ.filter (fun i => d y (z i) ≤ s)) a) :
    r - s ≤ |subsetDistance d z (selected a) x - subsetDistance d z (selected a) y| := by
  obtain ⟨i, hi, hai⟩ := exists_selected_of_not_avoids a _ hh
  have hA : (selected a).Nonempty := ⟨i, hai⟩
  have hy := (subsetDistance_le d z hai y).trans (Finset.mem_filter.mp hi).2
  have hx : r ≤ subsetDistance d z (selected a) x := by
    apply le_subsetDistance d z hA
    intro j hj
    by_contra hn
    have hlt : d x (z j) < r := lt_of_not_ge hn
    have hf := hm j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have ht := (Finset.mem_filter.mp hj).2
    rw [hf] at ht
    contradiction
  have ha := le_abs_self (subsetDistance d z (selected a) x - subsetDistance d z (selected a) y)
  linarith

lemma metric_balls_disjoint {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V)
    (hs : ∀ x y, d x y = d y x) (ht : ∀ x y w, d x w ≤ d x y + d y w)
    (x y : V) (r s : ℝ) (hrs : r + s < d x y) :
    Disjoint (Finset.univ.filter (fun i => d x (z i) < r))
      (Finset.univ.filter (fun i => d y (z i) ≤ s)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hx := (Finset.mem_filter.mp hi).2
  have hy := (Finset.mem_filter.mp hj).2
  have hh := ht x (z i) y
  rw [hs (z i) y] at hh
  linarith

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def scaleDistance {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (p : ℝ) (x y : V) : ℝ :=
  ∑ a : J → Bool, bernoulliWeight p a *
    |subsetDistance d z (selected a) x - subsetDistance d z (selected a) y|

lemma scaleDistance_nonneg {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x y : V) :
    0 ≤ scaleDistance d z p x y := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (bernoulliWeight_nonneg hp hp1 a) (abs_nonneg _)

lemma scaleDistance_symm {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (p : ℝ) (x y : V) :
    scaleDistance d z p x y = scaleDistance d z p y x := by
  simp only [scaleDistance, abs_sub_comm]

lemma scaleDistance_le {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V)
    (hn : ∀ x y, 0 ≤ d x y) (hs : ∀ x y, d x y = d y x)
    (ht : ∀ x y w, d x w ≤ d x y + d y w)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x y : V) :
    scaleDistance d z p x y ≤ d x y := by
  calc
    scaleDistance d z p x y ≤ ∑ a : J → Bool, bernoulliWeight p a * d x y := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (subsetDistance_abs_sub_le d z hn hs ht _ x y)
        (bernoulliWeight_nonneg hp hp1 a)
    _ = d x y := by rw [← Finset.sum_mul, bernoulliWeight_sum, one_mul]

lemma scaleDistance_gap {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V)
    (hs : ∀ x y, d x y = d y x) (ht : ∀ x y w, d x w ≤ d x y + d y w)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x y : V) (r s : ℝ)
    (hgap : 0 ≤ r - s) (hrs : r + s < d x y)
    (ha : ((Finset.univ.filter (fun i => d x (z i) < r)).card : ℝ) * p ≤ 1 / 4)
    (hb : 1 / 8 ≤ ((Finset.univ.filter (fun i => d y (z i) ≤ s)).card : ℝ) * p) :
    (r - s) / 12 ≤ scaleDistance d z p x y := by
  let A := Finset.univ.filter (fun i => d x (z i) < r)
  let B := Finset.univ.filter (fun i => d y (z i) ≤ s)
  have hd : Disjoint A B := metric_balls_disjoint d z hs ht x y r s hrs
  have hm := bernoulli_miss_hit_lower hp hp1 A B hd ha hb
  have he' : (∑ a : J → Bool, if avoids A a ∧ ¬ avoids B a then bernoulliWeight p a else 0) * (r - s)
      ≤ ∑ a : J → Bool, bernoulliWeight p a *
        |subsetDistance d z (selected a) x - subsetDistance d z (selected a) y| := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    by_cases h : avoids A a ∧ ¬ avoids B a
    · rw [if_pos h]
      exact mul_le_mul_of_nonneg_left (selected_distance_gap d z a x y r s h.1 h.2)
        (bernoulliWeight_nonneg hp hp1 a)
    · rw [if_neg h, zero_mul]
      exact mul_nonneg (bernoulliWeight_nonneg hp hp1 a) (abs_nonneg _)
  have he : (∑ a : J → Bool, if avoids A a ∧ ¬ avoids B a then bernoulliWeight p a else 0) * (r - s)
      ≤ scaleDistance d z p x y := by
    simpa only [scaleDistance] using! he'
  have hh := mul_le_mul_of_nonneg_right hm hgap
  linarith

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

lemma exists_finite_quantile {J : Type*} [Fintype J] (f : J → ℝ) (q : ℕ)
    (hq : 0 < q) (hqc : q ≤ Fintype.card J) :
    ∃ r : ℝ, q ≤ (Finset.univ.filter (fun i => f i ≤ r)).card ∧
      (Finset.univ.filter (fun i => f i < r)).card < q := by
  classical
  have hc : 0 < Fintype.card J := lt_of_lt_of_le hq hqc
  let : Nonempty J := Fintype.card_pos_iff.mp hc
  let C : Finset J := Finset.univ.filter fun j =>
    q ≤ (Finset.univ.filter (fun i => f i ≤ f j)).card
  have hC : C.Nonempty := by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    have he : Finset.univ.filter (fun i => f i ≤ f j) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      exact hmax
    simpa only [he, Finset.card_univ] using hqc
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image C f hC
  refine ⟨f j, (Finset.mem_filter.mp hj).2, ?_⟩
  by_contra hn
  have hbig : q ≤ (Finset.univ.filter (fun i => f i < f j)).card := Nat.le_of_not_gt hn
  let A := Finset.univ.filter (fun i => f i < f j)
  have hA : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hq hbig)
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image A f hA
  have hsub : A ⊆ Finset.univ.filter (fun a => f a ≤ f i) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, himax a ha⟩
  have hiC : i ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbig.trans (Finset.card_le_card hsub)⟩
  have hle := hmin i hiC
  have hlt := (Finset.mem_filter.mp hi).2
  exact (not_lt_of_ge hle) hlt

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def finiteQuantile {J : Type*} [Fintype J] (f : J → ℝ) (q : ℕ)
    (hq : 0 < q) (hqc : q ≤ Fintype.card J) : ℝ :=
  Classical.choose (exists_finite_quantile f q hq hqc)

lemma finiteQuantile_closed {J : Type*} [Fintype J] (f : J → ℝ) (q : ℕ)
    (hq : 0 < q) (hqc : q ≤ Fintype.card J) :
    q ≤ (Finset.univ.filter (fun i => f i ≤ finiteQuantile f q hq hqc)).card :=
  (Classical.choose_spec (exists_finite_quantile f q hq hqc)).1

lemma finiteQuantile_open {J : Type*} [Fintype J] (f : J → ℝ) (q : ℕ)
    (hq : 0 < q) (hqc : q ≤ Fintype.card J) :
    (Finset.univ.filter (fun i => f i < finiteQuantile f q hq hqc)).card < q :=
  (Classical.choose_spec (exists_finite_quantile f q hq hqc)).2

noncomputable def pairRadius {J : Type*} [Fintype J] (f g : J → ℝ)
    (q : ℕ) (hq : 0 < q) (cap : ℝ) : ℝ :=
  if hqc : q ≤ Fintype.card J then
    min cap (max (finiteQuantile f q hq hqc) (finiteQuantile g q hq hqc)) else cap

lemma pairRadius_le {J : Type*} [Fintype J] (f g : J → ℝ)
    (q : ℕ) (hq : 0 < q) (cap : ℝ) : pairRadius f g q hq cap ≤ cap := by
  unfold pairRadius
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma pairRadius_closed {J : Type*} [Fintype J] (f g : J → ℝ)
    (q : ℕ) (hq : 0 < q) (cap : ℝ) (hr : pairRadius f g q hq cap < cap) :
    q ≤ (Finset.univ.filter (fun i => f i ≤ pairRadius f g q hq cap)).card ∧
    q ≤ (Finset.univ.filter (fun i => g i ≤ pairRadius f g q hq cap)).card := by
  classical
  by_cases hqc : q ≤ Fintype.card J
  · have hm : max (finiteQuantile f q hq hqc) (finiteQuantile g q hq hqc) < cap := by
      simpa only [pairRadius, dif_pos hqc, min_lt_iff, lt_self_iff_false, false_or] using hr
    have he : pairRadius f g q hq cap =
        max (finiteQuantile f q hq hqc) (finiteQuantile g q hq hqc) := by
      simp only [pairRadius, dif_pos hqc, min_eq_right hm.le]
    rw [he]
    constructor
    · apply (finiteQuantile_closed f q hq hqc).trans
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hi).2.trans (le_max_left _ _)⟩
    · apply (finiteQuantile_closed g q hq hqc).trans
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hi).2.trans (le_max_right _ _)⟩
  · simp only [pairRadius, dif_neg hqc, lt_self_iff_false] at hr

lemma pairRadius_open {J : Type*} [Fintype J] (f g : J → ℝ)
    (q : ℕ) (hq : 0 < q) (cap : ℝ) :
    (Finset.univ.filter (fun i => f i < pairRadius f g q hq cap)).card < q ∨
    (Finset.univ.filter (fun i => g i < pairRadius f g q hq cap)).card < q := by
  classical
  by_cases hqc : q ≤ Fintype.card J
  · by_cases hfg : finiteQuantile f q hq hqc ≤ finiteQuantile g q hq hqc
    · right
      apply lt_of_le_of_lt _ (finiteQuantile_open g q hq hqc)
      apply Finset.card_le_card
      intro i hi
      have hr : pairRadius f g q hq cap ≤ finiteQuantile g q hq hqc := by
        simp only [pairRadius, dif_pos hqc, max_eq_right hfg]
        exact min_le_right _ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le hr⟩
    · left
      apply lt_of_le_of_lt _ (finiteQuantile_open f q hq hqc)
      apply Finset.card_le_card
      intro i hi
      have hr : pairRadius f g q hq cap ≤ finiteQuantile f q hq hqc := by
        simp only [pairRadius, dif_pos hqc, max_eq_left (le_of_not_ge hfg)]
        exact min_le_right _ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le hr⟩
  · left
    exact lt_of_le_of_lt (Finset.card_filter_le _ _) (by simpa only [Finset.card_univ] using Nat.lt_of_not_ge hqc)

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def embeddingRadius {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (x y : V) (t : ℕ) : ℝ :=
  if t = 0 then 0 else pairRadius (fun i => d x (z i)) (fun i => d y (z i))
    (2 ^ t) (pow_pos (by omega) _) (d x y / 4)

lemma embeddingRadius_zero {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (x y : V) : embeddingRadius d z x y 0 = 0 := by
  simp [embeddingRadius]

lemma embeddingRadius_le {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (hn : ∀ x y, 0 ≤ d x y) (x y : V) (t : ℕ) :
    embeddingRadius d z x y t ≤ d x y / 4 := by
  unfold embeddingRadius
  split_ifs
  · exact div_nonneg (hn x y) (by norm_num)
  · exact pairRadius_le _ _ _ _ _

lemma embeddingRadius_closed {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (hself : ∀ x, d x x = 0) (a b : J) (t : ℕ)
    (hr : embeddingRadius d z (z a) (z b) t < d (z a) (z b) / 4) :
    2 ^ t ≤ (Finset.univ.filter (fun i => d (z a) (z i) ≤ embeddingRadius d z (z a) (z b) t)).card ∧
    2 ^ t ≤ (Finset.univ.filter (fun i => d (z b) (z i) ≤ embeddingRadius d z (z a) (z b) t)).card := by
  classical
  by_cases ht : t = 0
  · subst t
    simp only [pow_zero, embeddingRadius_zero]
    constructor
    · apply Finset.one_le_card.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_eq (hself _)⟩⟩
    · apply Finset.one_le_card.mpr
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_eq (hself _)⟩⟩
  · simp only [embeddingRadius, if_neg ht] at hr ⊢
    exact pairRadius_closed _ _ _ _ _ hr

lemma embeddingRadius_open {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (x y : V) (t : ℕ) :
    (Finset.univ.filter (fun i => d x (z i) < embeddingRadius d z x y (t + 1))).card < 2 ^ (t + 1) ∨
    (Finset.univ.filter (fun i => d y (z i) < embeddingRadius d z x y (t + 1))).card < 2 ^ (t + 1) := by
  simp only [embeddingRadius, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
  exact pairRadius_open _ _ _ _ _

lemma embeddingRadius_last {V J : Type*} [Fintype J]
    (d : V → V → ℝ) (z : J → V) (x y : V) (L : ℕ)
    (hL : 0 < L) (hc : Fintype.card J < 2 ^ L) :
    embeddingRadius d z x y L = d x y / 4 := by
  simp only [embeddingRadius, if_neg (Nat.ne_of_gt hL), pairRadius, dif_neg (not_le.mpr hc)]

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def dyadicProbability (t : ℕ) : ℝ := 1 / (4 * (2 : ℝ) ^ (t + 1))

lemma dyadicProbability_nonneg (t : ℕ) : 0 ≤ dyadicProbability t := by
  unfold dyadicProbability
  positivity

lemma dyadicProbability_le_one (t : ℕ) : dyadicProbability t ≤ 1 := by
  unfold dyadicProbability
  have hp : (1 : ℝ) ≤ 2 ^ (t + 1) := one_le_pow₀ (by norm_num)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ (t + 1))).2
  linarith

lemma dyadic_small_card (t a : ℕ) (ha : a < 2 ^ (t + 1)) :
    (a : ℝ) * dyadicProbability t ≤ 1 / 4 := by
  have ha' : (a : ℝ) ≤ (2 : ℝ) ^ (t + 1) := by exact_mod_cast ha.le
  unfold dyadicProbability
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ (t + 1))).2
  linarith

lemma dyadic_large_card (t b : ℕ) (hb : 2 ^ t ≤ b) :
    (1 / 8 : ℝ) ≤ (b : ℝ) * dyadicProbability t := by
  have hb' : (2 : ℝ) ^ t ≤ (b : ℝ) := by exact_mod_cast hb
  unfold dyadicProbability
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ (t + 1))).2
  rw [pow_succ]
  linarith

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

lemma dyadic_scale_lower {V J : Type*} [Fintype J] [DecidableEq J]
    (d : V → V → ℝ) (z : J → V)
    (hn : ∀ x y, 0 ≤ d x y) (hself : ∀ x, d x x = 0)
    (hs : ∀ x y, d x y = d y x) (ht : ∀ x y w, d x w ≤ d x y + d y w)
    (a b : J) (hR : 0 < d (z a) (z b)) (t : ℕ) :
    (embeddingRadius d z (z a) (z b) (t + 1) - embeddingRadius d z (z a) (z b) t) / 12 ≤
      scaleDistance d z (dyadicProbability t) (z a) (z b) := by
  let r := embeddingRadius d z (z a) (z b) (t + 1)
  let s := embeddingRadius d z (z a) (z b) t
  have hp := dyadicProbability_nonneg t
  have hp1 := dyadicProbability_le_one t
  have hr : r ≤ d (z a) (z b) / 4 := embeddingRadius_le d z hn _ _ _
  have hsc : s ≤ d (z a) (z b) / 4 := embeddingRadius_le d z hn _ _ _
  change (r - s) / 12 ≤ _
  by_cases hgap : 0 < r - s
  · have hsl : s < d (z a) (z b) / 4 := by linarith
    have hc := embeddingRadius_closed d z hself a b t hsl
    have ho := embeddingRadius_open d z (z a) (z b) t
    have hsum : r + s < d (z a) (z b) := by linarith
    rcases ho with hox | hoy
    · exact scaleDistance_gap d z hs ht hp hp1 (z a) (z b) r s hgap.le hsum
        (dyadic_small_card t _ hox) (dyadic_large_card t _ hc.2)
    · have hsum' : r + s < d (z b) (z a) := by rw [hs]; exact hsum
      have hh := scaleDistance_gap d z hs ht hp hp1 (z b) (z a) r s hgap.le hsum'
        (dyadic_small_card t _ hoy) (dyadic_large_card t _ hc.1)
      rw [scaleDistance_symm d z _ (z b) (z a)] at hh
      exact hh
  · have hh := scaleDistance_nonneg d z hp hp1 (z a) (z b)
    linarith

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

lemma sum_successive_sub (f : ℕ → ℝ) (L : ℕ) :
    ∑ t ∈ Finset.range L, (f (t + 1) - f t) = f L - f 0 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; ring

lemma terminal_scale_sum_lower {V J : Type*} [Fintype J] [DecidableEq J]
    (d : V → V → ℝ) (z : J → V)
    (hn : ∀ x y, 0 ≤ d x y) (hself : ∀ x, d x x = 0)
    (hs : ∀ x y, d x y = d y x) (ht : ∀ x y w, d x w ≤ d x y + d y w)
    (a b : J) (L : ℕ) (hL : 0 < L) (hc : Fintype.card J < 2 ^ L) :
    d (z a) (z b) / 48 ≤ ∑ t ∈ Finset.range L,
      scaleDistance d z (dyadicProbability t) (z a) (z b) := by
  by_cases hR : 0 < d (z a) (z b)
  · have hh : (∑ t ∈ Finset.range L,
        (embeddingRadius d z (z a) (z b) (t + 1) - embeddingRadius d z (z a) (z b) t) / 12) ≤
        ∑ t ∈ Finset.range L, scaleDistance d z (dyadicProbability t) (z a) (z b) := by
      apply Finset.sum_le_sum
      intro t _
      exact dyadic_scale_lower d z hn hself hs ht a b hR t
    rw [← Finset.sum_div, sum_successive_sub, embeddingRadius_zero,
      embeddingRadius_last d z _ _ L hL hc, sub_zero] at hh
    convert hh using 1
    ring
  · have he : d (z a) (z b) = 0 := le_antisymm (le_of_not_gt hR) (hn _ _)
    rw [he, zero_div]
    apply Finset.sum_nonneg
    intro t _
    exact scaleDistance_nonneg d z (dyadicProbability_nonneg t) (dyadicProbability_le_one t) _ _

end GeometryOfGraphs.FlowCut.Fresh
end

section

open scoped BigOperators Classical
namespace GeometryOfGraphs.FlowCut.Fresh

abbrev EmbeddingIndex (J : Type*) [Fintype J] :=
  Fin (Nat.log 2 (Fintype.card J) + 1) × (J → Bool)

lemma terminal_embedding {V J : Type*} [Fintype J] [DecidableEq J]
    (d : V → V → ℝ) (hn : ∀ x y, 0 ≤ d x y) (hself : ∀ x, d x x = 0)
    (hs : ∀ x y, d x y = d y x) (ht : ∀ x y w, d x w ≤ d x y + d y w)
    (z : J → V) (_hJ : 2 ≤ Fintype.card J) :
    ∃ w : EmbeddingIndex J → ℝ, ∃ f : EmbeddingIndex J → V → ℝ,
      (∀ i, 0 ≤ w i) ∧
      (∀ x y, ∑ i, w i * |f i x - f i y| ≤
        (Nat.log 2 (Fintype.card J) + 1 : ℕ) * d x y) ∧
      (∀ a b, d (z a) (z b) / 48 ≤ ∑ i, w i * |f i (z a) - f i (z b)|) := by
  let L := Nat.log 2 (Fintype.card J) + 1
  let w : EmbeddingIndex J → ℝ := fun i => bernoulliWeight (dyadicProbability i.1.val) i.2
  let f : EmbeddingIndex J → V → ℝ := fun i => subsetDistance d z (selected i.2)
  have he (x y : V) : (∑ i, w i * |f i x - f i y|) =
      ∑ t : Fin L, scaleDistance d z (dyadicProbability t.val) x y := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    unfold scaleDistance
    apply Finset.sum_congr
    · ext a
      simp
    · intro a _
      rfl
  refine ⟨w, f, ?_, ?_, ?_⟩
  · intro i
    exact bernoulliWeight_nonneg (dyadicProbability_nonneg _) (dyadicProbability_le_one _) _
  · intro x y
    rw [he]
    calc
      (∑ t : Fin L, scaleDistance d z (dyadicProbability t.val) x y) ≤ ∑ _t : Fin L, d x y := by
        apply Finset.sum_le_sum
        intro t _
        exact scaleDistance_le d z hn hs ht (dyadicProbability_nonneg _) (dyadicProbability_le_one _) _ _
      _ = (Nat.log 2 (Fintype.card J) + 1 : ℕ) * d x y := by simp [L]
  · intro a b
    rw [he, Fin.sum_univ_eq_sum_range
      (fun t => scaleDistance d z (dyadicProbability t) (z a) (z b)) L]
    apply terminal_scale_sum_lower d z hn hself hs ht a b L (by dsimp [L]; omega)
    exact Nat.lt_pow_succ_log_self (by omega) _

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

noncomputable def lineMetric {V : Type*} (f : V → ℝ) : V → V → ℝ := fun i j => |f i - f j|

noncomputable def cutMetric {V : Type*} [DecidableEq V] (S : Finset V) : V → V → ℝ :=
  lineMetric (fun i => if i ∈ S then 1 else 0)

lemma abs_max_peel (M m x y : ℝ) (hm : m < M)
    (hx : x = M ∨ x ≤ m) (hy : y = M ∨ y ≤ m) :
    |x - y| = |min x m - min y m| +
      (M - m) * |(if x = M then (1 : ℝ) else 0) - (if y = M then 1 else 0)| := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · subst x
    subst y
    simp
  · subst x
    have hyM : y ≠ M := ne_of_lt (lt_of_le_of_lt hy hm)
    rw [if_pos rfl, if_neg hyM, min_eq_right hm.le, min_eq_left hy,
      abs_of_nonneg (by linarith : 0 ≤ M - y), abs_of_nonneg (by linarith : 0 ≤ m - y)]
    norm_num
  · subst y
    have hxM : x ≠ M := ne_of_lt (lt_of_le_of_lt hx hm)
    rw [if_neg hxM, if_pos rfl, min_eq_left hx, min_eq_right hm.le,
      abs_of_nonpos (by linarith : x - M ≤ 0), abs_of_nonpos (by linarith : x - m ≤ 0)]
    norm_num
  · have hxM : x ≠ M := ne_of_lt (lt_of_le_of_lt hx hm)
    have hyM : y ≠ M := ne_of_lt (lt_of_le_of_lt hy hm)
    simp [hxM, hyM, min_eq_left hx, min_eq_left hy]

lemma linear_nonneg_on_lineMetric {V : Type*} [Fintype V] [DecidableEq V]
    (L : (V → V → ℝ) →ₗ[ℝ] ℝ)
    (hcut : ∀ S : Finset V, 0 ≤ L (cutMetric S)) (f : V → ℝ) :
    0 ≤ L (lineMetric f) := by
  classical
  have aux : ∀ S : Finset ℝ, ∀ g : V → ℝ, (∀ i, g i ∈ S) → 0 ≤ L (lineMetric g) := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro g hg
      by_cases hS : S.Nonempty
      · let M := S.max' hS
        have hM : M ∈ S := Finset.max'_mem S hS
        let T := S.erase M
        by_cases hT : T.Nonempty
        · let m := T.max' hT
          have hmT : m ∈ T := Finset.max'_mem T hT
          have hmS : m ∈ S := Finset.mem_of_mem_erase hmT
          have hmne : m ≠ M := Finset.ne_of_mem_erase hmT
          have hmM : m < M := lt_of_le_of_ne (Finset.le_max' S m hmS) hmne
          have hcases : ∀ i, g i = M ∨ g i ≤ m := by
            intro i
            by_cases hi : g i = M
            · exact Or.inl hi
            · exact Or.inr (Finset.le_max' T (g i) (Finset.mem_erase.mpr ⟨hi, hg i⟩))
          have htrunc : ∀ i, min (g i) m ∈ T := by
            intro i
            rcases hcases i with hi | hi
            · rw [hi, min_eq_right hmM.le]
              exact hmT
            · rw [min_eq_left hi]
              exact Finset.mem_erase.mpr ⟨ne_of_lt (lt_of_le_of_lt hi hmM), hg i⟩
          have hind := ih T (Finset.erase_ssubset hM) (fun i => min (g i) m) htrunc
          let A := Finset.univ.filter (fun i => g i = M)
          have he : lineMetric g = lineMetric (fun i => min (g i) m) + (M - m) • cutMetric A := by
            funext i j
            simpa only [lineMetric, cutMetric, A, Finset.mem_filter, Finset.mem_univ,
              true_and, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
              abs_max_peel M m (g i) (g j) hmM (hcases i) (hcases j)
          rw [he, map_add, map_smul]
          exact add_nonneg hind (mul_nonneg (sub_nonneg.mpr hmM.le) (hcut A))
        · have hconst : ∀ i, g i = M := by
            intro i
            by_contra hi
            exact hT ⟨g i, Finset.mem_erase.mpr ⟨hi, hg i⟩⟩
          have he : lineMetric g = 0 := by funext i j; simp [lineMetric, hconst]
          rw [he, map_zero]
      · have he : lineMetric g = 0 := by
          funext i j
          exact False.elim (hS ⟨g i, hg i⟩)
        rw [he, map_zero]
  exact aux (Finset.univ.image f) f (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma cutMetric_formula (S : Finset V) (i j : V) : cutMetric S i j =
    if (i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S) then 1 else 0 := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [cutMetric, lineMetric, hi, hj]

omit [Fintype V] in
lemma demand_cutMetric (N : Network V) (S : Finset V) :
    (∑ μ, N.D μ * cutMetric S (N.s μ) (N.t μ)) = N.Dem S := by
  simp only [Network.Dem, Finset.sum_filter, cutMetric_formula, mul_ite, mul_one, mul_zero]

lemma capacity_cutMetric (N : Network V) (S : Finset V) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, N.C i j * cutMetric S i j) = N.Cap S := by
  classical
  have hrow1 (i : V) (hi : i ∈ S) :
      (∑ j, N.C i j * cutMetric S i j) = ∑ j ∈ Sᶜ, N.C i j := by
    calc
      _ = ∑ j ∈ Sᶜ, N.C i j * cutMetric S i j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hjS : j ∈ S := by simpa using hj
        simp [cutMetric, lineMetric, hi, hjS]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjS : j ∉ S := Finset.mem_compl.mp hj
        simp [cutMetric, lineMetric, hi, hjS]
  have hrow2 (i : V) (hi : i ∈ Sᶜ) :
      (∑ j, N.C i j * cutMetric S i j) = ∑ j ∈ S, N.C i j := by
    have hiS : i ∉ S := Finset.mem_compl.mp hi
    calc
      _ = ∑ j ∈ S, N.C i j * cutMetric S i j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        simp [cutMetric, lineMetric, hiS, hj]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [cutMetric, lineMetric, hiS, hj]
  have hsum : (∑ i, ∑ j, N.C i j * cutMetric S i j) = N.Cap S + N.Cap S := by
    rw [← Finset.sum_add_sum_compl S]
    have ha : (∑ i ∈ S, ∑ j, N.C i j * cutMetric S i j) = N.Cap S := by
      exact Finset.sum_congr rfl (fun i hi => hrow1 i hi)
    have hb : (∑ i ∈ Sᶜ, ∑ j, N.C i j * cutMetric S i j) = N.Cap S := by
      calc
        _ = ∑ i ∈ Sᶜ, ∑ j ∈ S, N.C i j := Finset.sum_congr rfl (fun i hi => hrow2 i hi)
        _ = ∑ j ∈ S, ∑ i ∈ Sᶜ, N.C i j := Finset.sum_comm
        _ = N.Cap S := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          exact N.C_symm i j
    rw [ha, hb]
  rw [hsum]
  ring

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def networkCutFunctional (N : Network V) (σ : ℝ) :
    (V → V → ℝ) →ₗ[ℝ] ℝ where
  toFun d := (1 / 2 : ℝ) * (∑ i, ∑ j, N.C i j * d i j) -
    σ * ∑ μ, N.D μ * d (N.s μ) (N.t μ)
  map_add' d e := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a d := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hC : (∑ i, ∑ j, N.C i j * (a * d i j)) =
        a * (∑ i, ∑ j, N.C i j * d i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hD : (∑ μ, N.D μ * (a * d (N.s μ) (N.t μ))) =
        a * (∑ μ, N.D μ * d (N.s μ) (N.t μ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      ring
    rw [hC, hD]
    ring

lemma network_functional_cut_nonneg (N : Network V) (σ : ℝ)
    (hcut : ∀ S : Finset V, σ * N.Dem S ≤ N.Cap S) (S : Finset V) :
    0 ≤ networkCutFunctional N σ (cutMetric S) := by
  change 0 ≤ (1 / 2 : ℝ) * (∑ i, ∑ j, N.C i j * cutMetric S i j) -
    σ * (∑ μ, N.D μ * cutMetric S (N.s μ) (N.t μ))
  rw [capacity_cutMetric, demand_cutMetric]
  exact sub_nonneg.mpr (hcut S)

lemma network_coarea (N : Network V) (σ : ℝ)
    (hcut : ∀ S : Finset V, σ * N.Dem S ≤ N.Cap S) (f : V → ℝ) :
    σ * (∑ μ, N.D μ * |f (N.s μ) - f (N.t μ)|) ≤
      (1 / 2 : ℝ) * (∑ i, ∑ j, N.C i j * |f i - f j|) := by
  have h := linear_nonneg_on_lineMetric (networkCutFunctional N σ)
    (network_functional_cut_nonneg N σ hcut) f
  exact sub_nonneg.mp h

lemma network_weighted_coarea (N : Network V) (σ : ℝ)
    (hcut : ∀ S : Finset V, σ * N.Dem S ≤ N.Cap S)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ a, 0 ≤ w a) (f : ι → V → ℝ) :
    σ * (∑ μ, N.D μ * (∑ a, w a * |f a (N.s μ) - f a (N.t μ)|)) ≤
      (1 / 2 : ℝ) * (∑ i, ∑ j, N.C i j * (∑ a, w a * |f a i - f a j|)) := by
  have h : 0 ≤ networkCutFunctional N σ (∑ a, w a • lineMetric (f a)) := by
    rw [map_sum]
    apply Finset.sum_nonneg
    intro a _
    rw [map_smul]
    exact mul_nonneg (hw a) (linear_nonneg_on_lineMetric (networkCutFunctional N σ)
      (network_functional_cut_nonneg N σ hcut) (f a))
  apply sub_nonneg.mp
  simpa only [networkCutFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, lineMetric] using h

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma embedding_cut_bound (N : Network V) (hk : 0 < N.k) (sig : ℝ) (hsig : 0 ≤ sig)
    (hcut : ∀ S, sig*N.Dem S ≤ N.Cap S)
    (d : V → V → ℝ) (hn : ∀ i j, 0 ≤ d i j) (hself : ∀ i, d i i = 0)
    (hs : ∀ i j, d i j = d j i) (ht : ∀ i j l, d i l ≤ d i j+d j l)
    (hQ : 0 < ∑ μ, N.D μ*d (N.s μ) (N.t μ)) {lam : ℝ}
    (hdual : (1/2:ℝ)*(∑ i, ∑ j, N.C i j*d i j) < lam*(∑ μ, N.D μ*d (N.s μ) (N.t μ))) :
    sig < 48*(Nat.log 2 (2*N.k)+1 : ℕ)*lam := by
  classical
  let J := Fin N.k × Bool
  let z : J → V := fun a => if a.2 then N.s a.1 else N.t a.1
  have hJ : 2 ≤ Fintype.card J := by simp [J]; omega
  obtain ⟨w,f,hw,hupper,hlower⟩ := terminal_embedding d hn hself hs ht z hJ
  let delta : V → V → ℝ := fun x y => ∑ a, w a*|f a x-f a y|
  let L : ℝ := (Nat.log 2 (Fintype.card J)+1 : ℕ)
  let Q : ℝ := ∑ μ, N.D μ*d (N.s μ) (N.t μ)
  let cost : ℝ := (1/2:ℝ)*(∑ i, ∑ j, N.C i j*d i j)
  have hL : 0 < L := by dsimp [L]; positivity
  have hlow : Q/48 ≤ ∑ μ, N.D μ*delta (N.s μ) (N.t μ) := by
    dsimp [Q]
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro μ _
    have h := hlower (μ,true) (μ,false)
    change d (N.s μ) (N.t μ)/48 ≤ delta (N.s μ) (N.t μ) at h
    convert mul_le_mul_of_nonneg_left h (N.D_nonneg μ) using 1
    ring
  have hhigh : (1/2:ℝ)*(∑ i, ∑ j, N.C i j*delta i j) ≤ L*cost := by
    have hb : (∑ i, ∑ j, N.C i j*delta i j) ≤
        ∑ i, ∑ j, N.C i j*(L*d i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hupper i j) (N.C_nonneg i j)
    have he : (∑ i, ∑ j, N.C i j*(L*d i j)) = L*(∑ i, ∑ j, N.C i j*d i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he] at hb
    dsimp [cost]
    linarith
  have hc := network_weighted_coarea N sig hcut w hw f
  have hmul := mul_le_mul_of_nonneg_left hlow hsig
  have htotal : sig*Q ≤ 48*L*cost := by
    change sig*(∑ μ, N.D μ*delta (N.s μ) (N.t μ)) ≤
      (1/2:ℝ)*(∑ i, ∑ j, N.C i j*delta i j) at hc
    nlinarith
  have hstrict : 48*L*cost < 48*L*(lam*Q) :=
    mul_lt_mul_of_pos_left hdual (by positivity)
  have hres : sig < 48*L*lam := by
    apply (mul_lt_mul_iff_left₀ hQ).mp
    nlinarith [htotal.trans_lt hstrict]
  simpa [L,J,Fintype.card_prod,mul_comm] using hres

end GeometryOfGraphs.FlowCut.Fresh
end

section

namespace GeometryOfGraphs.FlowCut.Fresh

lemma terminal_scale_log_bound (k : ℕ) (hk : 0 < k) :
    ((Nat.log 2 (2 * k) + 1 : ℕ) : ℝ) ≤
      (3 / Real.log 2) * Real.log (max (k : ℝ) 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnat : (2 : ℕ) ^ Nat.log 2 (2 * k) ≤ 2 * k :=
    Nat.pow_log_le_self 2 (by omega)
  have hpow : (2 : ℝ) ^ Nat.log 2 (2 * k) ≤ 2 * (k : ℝ) := by exact_mod_cast hnat
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkR.ne'] at hlog
  have hklog : Real.log (k : ℝ) ≤ Real.log (max (k : ℝ) 2) :=
    Real.log_le_log hkR (le_max_left _ _)
  have htlog : Real.log (2 : ℝ) ≤ Real.log (max (k : ℝ) 2) :=
    Real.log_le_log (by norm_num) (le_max_right _ _)
  have hmain : ((Nat.log 2 (2 * k) + 1 : ℕ) : ℝ) * Real.log 2 ≤
      3 * Real.log (max (k : ℝ) 2) := by
    push_cast
    nlinarith
  calc
    _ ≤ (3 * Real.log (max (k : ℝ) 2)) / Real.log 2 := (le_div_iff₀ htwo).mpr hmain
    _ = _ := by ring

lemma bound_at_limit_from_above (σ F a : ℝ) (ha : 0 < a)
    (h : ∀ lam : ℝ, F < lam → σ ≤ a * lam) : σ ≤ a * F := by
  by_contra hn
  have hgap : 0 < σ - a * F := sub_pos.mpr (lt_of_not_ge hn)
  let lam := F + (σ - a * F) / (2 * a)
  have hlam : F < lam := by
    dsimp [lam]
    exact lt_add_of_pos_right _ (div_pos hgap (by positivity))
  have hb := h lam hlam
  have he : 2 * a * lam = a * F + σ := by
    dsimp [lam]
    field_simp [ha.ne']
    ring
  nlinarith

end GeometryOfGraphs.FlowCut.Fresh
end

section
open Finset
namespace GeometryOfGraphs.FlowCut.Fresh

lemma native_full_root :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (N : Network V),
        (∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) →
        ∃ S : Finset V, 0 < N.Dem S ∧
          N.Cap S ≤ C₀ * Real.log (max (N.k : ℝ) 2) * N.maxflow * N.Dem S := by
  have hlogtwo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨144/Real.log 2, by positivity, ?_⟩
  intro V _ _ N hpos
  obtain ⟨S,hS,hsig,hcut⟩ := exists_minimum_cut N hpos
  have hk : 0 < N.k := by obtain ⟨μ,_,_⟩ := hpos; exact Nat.zero_lt_of_lt μ.isLt
  let a : ℝ := (144/Real.log 2)*Real.log (max (N.k:ℝ) 2)
  have hlog : 0 < Real.log (max (N.k:ℝ) 2) := Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have ha : 0 < a := by dsimp [a]; positivity
  have hbound : N.Cap S/N.Dem S ≤ a*N.maxflow := by
    apply bound_at_limit_from_above _ _ a ha
    intro lam hlam
    obtain ⟨d,hn,hself,hs,ht,hQ,hdual⟩ := approximate_metric_dual N hpos hlam
    have he := embedding_cut_bound N hk (N.Cap S/N.Dem S) hsig hcut d hn hself hs ht hQ hdual
    have hL := terminal_scale_log_bound N.k hk
    have hl : 0 ≤ lam := (maxflow_nonneg N hpos).trans hlam.le
    have hscale : 48*(Nat.log 2 (2*N.k)+1:ℕ)*lam ≤ a*lam := by
      have hm := mul_le_mul_of_nonneg_right hL (mul_nonneg (by norm_num : (0:ℝ) ≤ 48) hl)
      dsimp [a]
      calc
        _ = ((Nat.log 2 (2*N.k)+1:ℕ):ℝ)*(48*lam) := by ring
        _ ≤ ((3/Real.log 2)*Real.log (max (N.k:ℝ) 2))*(48*lam) := hm
        _ = _ := by ring
    exact he.le.trans hscale
  refine ⟨S,hS,?_⟩
  exact (div_le_iff₀ hS).mp hbound

end GeometryOfGraphs.FlowCut.Fresh
end

open GeometryOfGraphs.FlowCut

theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (N : Network V),
        (∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) →
        ∃ S : Finset V, 0 < N.Dem S ∧
          N.Cap S ≤ C₀ * Real.log (max (N.k : ℝ) 2) * N.maxflow * N.Dem S  := by
  exact Fresh.native_full_root
