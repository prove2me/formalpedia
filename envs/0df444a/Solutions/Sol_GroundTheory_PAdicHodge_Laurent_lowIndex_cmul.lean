-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.lowIndex_cmul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:56:55.841167+00:00
-- url     : https://prove2.me/submissions/d616f35e-0f9b-4de6-ae05-905a7690337c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]

private theorem bddAbove_gaussWeights (hρ : 0 < ρ) (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hlt_of_dist {n : ℤ} {ε : ℝ} (hε : dist (f n) 0 < ε) : f n < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at hε
  set s1 : Set ℤ := {x | ¬ dist (f x) 0 < 1}
  have hFin : s1.Finite := Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp h) 1 one_pos)
  by_cases hN : hFin.toFinset.Nonempty
  · refine ⟨1 ⊔ hFin.toFinset.sup' hN f, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n ∈ hFin.toFinset
    · exact le_sup_of_le_right (Finset.le_sup' f hn)
    · have : n ∉ s1 := by
        rw [← hFin.mem_toFinset]
        exact hn
      have : dist (f n) 0 < 1 := by simpa [s1] using this
      exact le_sup_of_le_left (hlt_of_dist this).le
  · refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have : n ∉ s1 := by
      have : hFin.toFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
      rw [← hFin.mem_toFinset, this]
      exact Finset.notMem_empty n
    have : dist (f n) 0 < 1 := by simpa [s1] using this
    exact (hlt_of_dist this).le

private theorem gaussNorm_pos_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    0 < gaussNorm a ρ := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  obtain ⟨n, hn⟩ : ∃ n, a n ≠ 0 := by
    contrapose! ha
    exact funext ha
  have : 0 < f n := mul_pos (norm_pos_iff.mpr hn) (zpow_pos hρ n)
  exact this.trans_le (le_ciSup (bddAbove_gaussWeights hρ h) n)

private theorem domSet_nonempty_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    (domSet a ρ).Nonempty := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hlt_of_dist {n : ℤ} {ε : ℝ} (hε : dist (f n) 0 < ε) : f n < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at hε
  have hbdd := bddAbove_gaussWeights (a := a) hρ h
  set M := ⨆ n, f n
  have hpos : 0 < M := by simpa [M, gaussNorm] using gaussNorm_pos_of (a := a) hρ h ha
  set s : Set ℤ := {n | ¬ dist (f n) 0 < M / 2}
  have hFin : s.Finite :=
    Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp h) (M / 2) (half_pos hpos))
  have hsN : s.Nonempty := by
    by_contra hsempty
    rw [Set.not_nonempty_iff_eq_empty] at hsempty
    have hall : ∀ n, f n < M / 2 := fun n => by
      have : n ∉ s := by rw [hsempty]; exact Set.notMem_empty n
      have : dist (f n) 0 < M / 2 := by simpa [s] using this
      exact hlt_of_dist this
    have : M ≤ M / 2 := ciSup_le fun n => (hall n).le
    exact (not_le.mpr (half_lt_self hpos)) this
  obtain ⟨n, hn, hnmax⟩ :=
    hFin.toFinset.exists_max_image f (hFin.toFinset_nonempty.mpr hsN)
  refine ⟨n, ?_⟩
  change f n = gaussNorm a ρ
  have hn_s : n ∈ s := hFin.mem_toFinset.mp hn
  have hnge : M / 2 ≤ f n := by
    have : ¬ dist (f n) 0 < M / 2 := by simpa [s] using hn_s
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)] at this
    exact not_lt.mp this
  refine le_antisymm (le_ciSup hbdd n) (ciSup_le fun m => ?_)
  by_cases hm : m ∈ s
  · exact hnmax m (hFin.mem_toFinset.mpr hm)
  · have : dist (f m) 0 < M / 2 := by simpa [s] using hm
    exact (hlt_of_dist this).le.trans hnge

private theorem domSet_finite_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    (domSet a ρ).Finite := by
  set f : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n
  have f_nonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  have hpos := gaussNorm_pos_of (a := a) hρ h ha
  set M := ⨆ n, f n
  set s : Set ℤ := {n | ¬ dist (f n) 0 < M / 2}
  have hFin : s.Finite :=
    Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp h) (M / 2) (half_pos hpos))
  refine hFin.subset fun n hn => ?_
  change f n = gaussNorm a ρ at hn
  have hnge : M / 2 ≤ f n := by
    have : M ≤ f n := by simpa [M, gaussNorm] using le_of_eq hn.symm
    exact (half_le_self hpos.le).trans this
  have : ¬ dist (f n) 0 < M / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (f_nonneg n)]
    exact not_lt.mpr hnge
  simpa [s] using this


private theorem lowIndex_mem_of (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) :
    lowIndex a ρ ∈ domSet a ρ :=
  (domSet_nonempty_of (a := a) hρ h ha).csInf_mem (domSet_finite_of (a := a) hρ h ha)

private theorem weight_le_gauss (hρ : 0 < ρ) (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ :=
  le_ciSup (bddAbove_gaussWeights (a := a) hρ h) n

private theorem gaussNorm_nonneg (hρ : 0 < ρ) (h : ConvergesAt a ρ) :
    0 ≤ gaussNorm a ρ :=
  le_trans (mul_nonneg (norm_nonneg (a 0)) (zpow_nonneg hρ.le 0))
    (weight_le_gauss (a := a) hρ h 0)

private theorem weight_mul_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n i : ℤ) :
    (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) ≤ gaussNorm a ρ * gaussNorm b ρ :=
  mul_le_mul (weight_le_gauss (a := a) hρ ha i) (weight_le_gauss (a := b) hρ hb (n - i))
    (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le _))
    (gaussNorm_nonneg (a := a) hρ ha)

private theorem eq_gauss_of_weight_mul_eq (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    {i j : ℤ} (hga : 0 < gaussNorm a ρ) (hgb : 0 < gaussNorm b ρ)
    (heq : (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) = gaussNorm a ρ * gaussNorm b ρ) :
    ‖a i‖ * ρ ^ i = gaussNorm a ρ ∧ ‖b j‖ * ρ ^ j = gaussNorm b ρ := by
  have hx := weight_le_gauss (a := a) hρ ha i
  have hy := weight_le_gauss (a := b) hρ hb j
  have hx0 : 0 ≤ ‖a i‖ * ρ ^ i := mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le _)
  have hy0 : 0 ≤ ‖b j‖ * ρ ^ j := mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le _)
  constructor
  · by_contra hne
    have hlt : ‖a i‖ * ρ ^ i < gaussNorm a ρ := lt_of_le_of_ne hx hne
    have : (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) < gaussNorm a ρ * gaussNorm b ρ :=
      calc
        (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) ≤ (‖a i‖ * ρ ^ i) * gaussNorm b ρ :=
          mul_le_mul_of_nonneg_left hy hx0
        _ < gaussNorm a ρ * gaussNorm b ρ := mul_lt_mul_of_pos_right hlt hgb
    exact this.ne heq
  · by_contra hne
    have hlt : ‖b j‖ * ρ ^ j < gaussNorm b ρ := lt_of_le_of_ne hy hne
    have : (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) < gaussNorm a ρ * gaussNorm b ρ :=
      calc
        (‖a i‖ * ρ ^ i) * (‖b j‖ * ρ ^ j) ≤ gaussNorm a ρ * (‖b j‖ * ρ ^ j) :=
          mul_le_mul_of_nonneg_right hx hy0
        _ < gaussNorm a ρ * gaussNorm b ρ := mul_lt_mul_of_pos_left hlt hga
    exact this.ne heq

private theorem gaussNorm_cmul_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    gaussNorm (cmul a b) ρ ≤ gaussNorm a ρ * gaussNorm b ρ := by
  have hC : 0 ≤ gaussNorm a ρ * gaussNorm b ρ :=
    mul_nonneg (gaussNorm_nonneg (a := a) hρ ha) (gaussNorm_nonneg (a := b) hρ hb)
  refine ciSup_le fun n =>
    norm_cmul_mul_zpow_le (a := a) (b := b) hρ hC fun i =>
      weight_mul_le (a := a) (b := b) hρ ha hb n i

private theorem exists_strict_bound {f : ℤ → ℝ} (hnn : ∀ n, 0 ≤ f n)
    (ht : Tendsto f cofinite (𝓝 0)) {M : ℝ} (hM : 0 < M) (hlt : ∀ n, f n < M) :
    ∃ C, C < M ∧ ∀ n, f n ≤ C := by
  have hFin := Filter.eventually_cofinite.mp ((Metric.tendsto_nhds.mp ht) (M / 2) (half_pos hM))
  set s : Set ℤ := {n | ¬ dist (f n) 0 < M / 2}
  have hsF : s.Finite := hFin
  have hlt_of_dist {n : ℤ} {ε : ℝ} (hε : dist (f n) 0 < ε) : f n < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n)] at hε
  by_cases hN : hsF.toFinset.Nonempty
  · have hsuplt : hsF.toFinset.sup' hN f < M :=
      (Finset.sup'_lt_iff hN).mpr fun i _ => hlt i
    refine ⟨(M / 2) ⊔ hsF.toFinset.sup' hN f, max_lt (half_lt_self hM) hsuplt, fun n => ?_⟩
    by_cases hn : n ∈ hsF.toFinset
    · exact le_sup_of_le_right (Finset.le_sup' f hn)
    · have : n ∉ s := by
        rw [← hsF.mem_toFinset]
        exact hn
      have : dist (f n) 0 < M / 2 := by simpa [s] using this
      exact le_sup_of_le_left (hlt_of_dist this).le
  · refine ⟨M / 2, half_lt_self hM, fun n => ?_⟩
    have : n ∉ s := by
      have : hsF.toFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
      rw [← hsF.mem_toFinset, this]
      exact Finset.notMem_empty n
    have : dist (f n) 0 < M / 2 := by simpa [s] using this
    exact (hlt_of_dist this).le

private theorem tendsto_cmul_term (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Tendsto (fun i : ℤ => ‖a i * b (n - i)‖) cofinite (𝓝 0) := by
  have hw := tendsto_weight_prod (a := a) (b := b) ha hb
  have hinj : Function.Injective (fun i : ℤ => (i, n - i)) := fun i j hij =>
    (Prod.mk.inj hij).1
  have hmap : Tendsto (fun i : ℤ => (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)))
      cofinite (𝓝 0) := hw.comp hinj.tendsto_cofinite
  have : Tendsto (fun i : ℤ =>
      ((‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i))) / ρ ^ n) cofinite (𝓝 0) := by
    convert hmap.div_const (ρ ^ n)
    exact (zero_div _).symm
  convert this using 2 with i
  exact norm_mul_term (a := a) (b := b) hρ.ne' n i

private theorem summable_cmul_term (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Summable fun i : ℤ => a i * b (n - i) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  exact (tendsto_zero_iff_norm_tendsto_zero).2 (tendsto_cmul_term (a := a) (b := b) hρ ha hb n)

private theorem norm_cmul_eq_of_strict_max (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    {n i0 : ℤ} (hdom : ∀ i, i ≠ i0 → ‖a i * b (n - i)‖ < ‖a i0 * b (n - i0)‖)
    (hpos : 0 < ‖a i0 * b (n - i0)‖) :
    ‖cmul a b n‖ = ‖a i0 * b (n - i0)‖ := by
  have hs := summable_cmul_term (a := a) (b := b) hρ ha hb n
  have hsplit := hs.tsum_eq_add_tsum_ite i0
  let f : ℤ → ℝ := fun i => ‖if i = i0 then (0 : K) else a i * b (n - i)‖
  have hnn : ∀ i, 0 ≤ f i := fun _ => norm_nonneg _
  have ht : Tendsto f cofinite (𝓝 0) := by
    have hle : ∀ i, f i ≤ ‖a i * b (n - i)‖ := fun i => by
      by_cases hi : i = i0
      · subst hi; simp only [f, ↓reduceIte, norm_zero]; exact norm_nonneg _
      · simp [f, hi]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_cmul_term (a := a) (b := b) hρ ha hb n) (fun i => hnn i) hle
  have hlt : ∀ i, f i < ‖a i0 * b (n - i0)‖ := by
    intro i
    by_cases hi : i = i0
    · subst hi; simpa [f] using hpos
    · simpa [f, hi] using hdom i hi
  obtain ⟨C, hC, hCbound⟩ := exists_strict_bound (f := f) hnn ht hpos hlt
  have hC0 : 0 ≤ C := (hnn 0).trans (hCbound 0)
  have hrest : ‖∑' i, (if i = i0 then (0 : K) else a i * b (n - i))‖ ≤ C :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 hCbound
  have hne : ‖a i0 * b (n - i0)‖ ≠
      ‖∑' i, (if i = i0 then (0 : K) else a i * b (n - i))‖ :=
    ne_of_gt (hrest.trans_lt hC)
  have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  have : ‖cmul a b n‖ = max ‖a i0 * b (n - i0)‖
      ‖∑' i, (if i = i0 then (0 : K) else a i * b (n - i))‖ := by
    rw [cmul, hsplit]
    exact hmax
  rw [this, max_eq_left (hrest.trans hC.le)]

variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

theorem solution : lowIndex (cmul a b) ρ = lowIndex a ρ + lowIndex b ρ := by
  set la := lowIndex a ρ
  set lb := lowIndex b ρ
  have hla : la ∈ domSet a ρ := lowIndex_mem_of (a := a) hρ ha ha0
  have hlb : lb ∈ domSet b ρ := lowIndex_mem_of (a := b) hρ hb hb0
  have hga : 0 < gaussNorm a ρ := gaussNorm_pos_of (a := a) hρ ha ha0
  have hgb : 0 < gaussNorm b ρ := gaussNorm_pos_of (a := b) hρ hb hb0
  have hprod : 0 < gaussNorm a ρ * gaussNorm b ρ := mul_pos hga hgb
  have hleG : gaussNorm (cmul a b) ρ ≤ gaussNorm a ρ * gaussNorm b ρ :=
    gaussNorm_cmul_le (a := a) (b := b) hρ ha hb
  set n := la + lb
  have hnlb : n - la = lb := by simp [n]
  have hterm : (‖a la‖ * ρ ^ la) * (‖b (n - la)‖ * ρ ^ (n - la)) =
      gaussNorm a ρ * gaussNorm b ρ := by
    rw [hnlb]
    simp only [domSet, Set.mem_setOf] at hla hlb
    rw [hla, hlb]
  have hpos_term : 0 < ‖a la * b (n - la)‖ := by
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    have : 0 < (‖a la‖ * ρ ^ la) * (‖b (n - la)‖ * ρ ^ (n - la)) / ρ ^ n :=
      div_pos (by rwa [hterm]) hρn
    rwa [← norm_mul_term (a := a) (b := b) hρ.ne' n la] at this
  have hstrict : ∀ i, i ≠ la → ‖a i * b (n - i)‖ < ‖a la * b (n - la)‖ := by
    intro i hi
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    rw [norm_mul_term (a := a) (b := b) hρ.ne' n i,
        norm_mul_term (a := a) (b := b) hρ.ne' n la,
        div_lt_div_iff_of_pos_right hρn, hterm]
    refine lt_of_le_of_ne (weight_mul_le (a := a) (b := b) hρ ha hb n i) ?_
    intro heq
    have ⟨hiA, hiB⟩ :=
      eq_gauss_of_weight_mul_eq (a := a) (b := b) hρ ha hb hga hgb (j := n - i) heq
    have hile : la ≤ i :=
      csInf_le (domSet_finite_of (a := a) hρ ha ha0).bddBelow hiA
    have hjle : lb ≤ n - i :=
      csInf_le (domSet_finite_of (a := b) hρ hb hb0).bddBelow hiB
    have : i = la := by linarith
    exact hi this
  have hnorm : ‖cmul a b n‖ = ‖a la * b (n - la)‖ :=
    norm_cmul_eq_of_strict_max (a := a) (b := b) hρ ha hb hstrict hpos_term
  have hweight : ‖cmul a b n‖ * ρ ^ n = gaussNorm a ρ * gaussNorm b ρ := by
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    rw [hnorm, norm_mul_term (a := a) (b := b) hρ.ne' n la, div_mul_cancel₀ _ hρn.ne', hterm]
  have hcmul0 : cmul a b ≠ 0 := by
    intro h0
    have : cmul a b n = 0 := congrFun h0 n
    have : ‖cmul a b n‖ * ρ ^ n = 0 := by simp [this]
    exact hprod.ne (this.symm.trans hweight)
  have hGeq : gaussNorm a ρ * gaussNorm b ρ ≤ gaussNorm (cmul a b) ρ := by
    have hbd := bddAbove_gaussWeights (a := cmul a b) hρ
      (ConvergesAt.cmul (a := a) (b := b) hρ ha hb)
    have := le_ciSup hbd n
    simpa [gaussNorm, hweight] using this
  have hG : gaussNorm (cmul a b) ρ = gaussNorm a ρ * gaussNorm b ρ := le_antisymm hleG hGeq
  have hn_mem : n ∈ domSet (cmul a b) ρ := by
    change ‖cmul a b n‖ * ρ ^ n = gaussNorm (cmul a b) ρ
    rw [hweight, hG]
  have hle : lowIndex (cmul a b) ρ ≤ n :=
    csInf_le (domSet_finite_of (a := cmul a b) hρ
      (ConvergesAt.cmul (a := a) (b := b) hρ ha hb) hcmul0).bddBelow hn_mem
  have hge : n ≤ lowIndex (cmul a b) ρ := by
    refine le_csInf (domSet_nonempty_of (a := cmul a b) hρ
      (ConvergesAt.cmul (a := a) (b := b) hρ ha hb) hcmul0) fun m hm => ?_
    change ‖cmul a b m‖ * ρ ^ m = gaussNorm (cmul a b) ρ at hm
    have hmG : ‖cmul a b m‖ * ρ ^ m = gaussNorm a ρ * gaussNorm b ρ := by rw [hm, hG]
    have hatt : ∃ i, (‖a i‖ * ρ ^ i) * (‖b (m - i)‖ * ρ ^ (m - i)) =
        gaussNorm a ρ * gaussNorm b ρ := by
      by_contra hnone
      push Not at hnone
      have hlt : ∀ i, (‖a i‖ * ρ ^ i) * (‖b (m - i)‖ * ρ ^ (m - i)) <
          gaussNorm a ρ * gaussNorm b ρ := fun i =>
        lt_of_le_of_ne (weight_mul_le (a := a) (b := b) hρ ha hb m i) (hnone i)
      let f : ℤ → ℝ := fun i => (‖a i‖ * ρ ^ i) * (‖b (m - i)‖ * ρ ^ (m - i))
      have hnn : ∀ i, 0 ≤ f i := fun i =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le _))
          (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le _))
      have ht : Tendsto f cofinite (𝓝 0) := by
        have hw := tendsto_weight_prod (a := a) (b := b) ha hb
        have hinj : Function.Injective (fun i : ℤ => (i, m - i)) := fun i j hij =>
          (Prod.mk.inj hij).1
        exact hw.comp hinj.tendsto_cofinite
      obtain ⟨C, hC, hCb⟩ := exists_strict_bound (f := f) hnn ht hprod hlt
      have : ‖cmul a b m‖ * ρ ^ m ≤ C :=
        norm_cmul_mul_zpow_le (a := a) (b := b) hρ ((hnn 0).trans (hCb 0)) hCb
      exact (this.trans_lt hC).ne hmG
    obtain ⟨i, hi⟩ := hatt
    have ⟨hiA, hiB⟩ := eq_gauss_of_weight_mul_eq (a := a) (b := b) hρ ha hb hga hgb hi
    have : la ≤ i := csInf_le (domSet_finite_of (a := a) hρ ha ha0).bddBelow hiA
    have : lb ≤ m - i := csInf_le (domSet_finite_of (a := b) hρ hb hb0).bddBelow hiB
    linarith
  exact le_antisymm hle (by simpa [n] using hge)
