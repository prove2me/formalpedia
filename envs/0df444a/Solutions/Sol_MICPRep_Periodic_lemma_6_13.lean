-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_13
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:20:58.042897+00:00
-- url     : https://prove2.me/submissions/ea2d0ce1-5dbe-4b0b-a55c-f97deab7f43a

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting
import Theorems.Thm_MICPRep_Periodic_lemma_6_11


-- Complete local proof from AsymptoticGeometry.lean.
namespace MICPRep.Periodic.AsymptoticGeometry

open Set Filter
open scoped Topology

variable {n p d : ℕ} {M : Set (Ambient n p d)}

lemma fiber_nonempty {z : Fin d → ℝ} (hz : z ∈ indexSet M) :
    (zProj M z).Nonempty := by
  rcases hz with ⟨⟨x, y, w⟩, h, rfl⟩
  exact ⟨x, y, h⟩

lemma lattice_add_nsmul {z r : Fin d → ℝ} (hz : z ∈ intLattice d)
    (hr : r ∈ intLattice d) (k : ℕ) : z + (k : ℝ) • r ∈ intLattice d := by
  rcases hz with ⟨z, rfl⟩
  rcases hr with ⟨r, rfl⟩
  refine ⟨fun i => z i + (k : ℤ) * r i, ?_⟩
  ext i
  simp

lemma fiber_combo (hM : Convex ℝ M) {z w : Fin d → ℝ} {x y : Pt n}
    (hx : x ∈ zProj M z) (hy : y ∈ zProj M w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ zProj M (a • z + b • w) := by
  rcases hx with ⟨x', hx⟩
  rcases hy with ⟨y', hy⟩
  exact ⟨a • x' + b • y', hM hx hy ha hb hab⟩

lemma fiber_combo_closure_right (hM : Convex ℝ M) {z w : Fin d → ℝ} {x y : Pt n}
    (hx : x ∈ zProj M z) (hy : y ∈ closure (zProj M w))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ closure (zProj M (a • z + b • w)) := by
  have hc : IsClosed {y : Pt n | a • x + b • y ∈
      closure (zProj M (a • z + b • w))} :=
    isClosed_closure.preimage (by fun_prop)
  apply closure_minimal (t := {y : Pt n | a • x + b • y ∈
      closure (zProj M (a • z + b • w))}) ?_ hc hy
  intro y hy
  exact subset_closure (fiber_combo hM hx hy ha hb hab)

lemma integer_fiber_ediam {z : Fin d → ℝ} (hz : z ∈ indexSet M ∩ intLattice d) :
    Metric.ediam (closure (zProj M z)) ≤ micpDiam M := by
  rw [Metric.ediam_closure]
  exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)

lemma drift_unique (hD : micpDiam M < ⊤) {z r : Fin d → ℝ}
    (hz : z ∈ intLattice d ∩ indexSet M) (hrZ : r ∈ intLattice d)
    (hrI : r ∈ recCone (indexSet M)) {u v : Pt n}
    (hu : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M,
      ∀ x ∈ zProj M z, x + t • u ∈ closure (zProj M (z + t • r)))
    (hv : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M,
      ∀ x ∈ zProj M z, x + t • v ∈ closure (zProj M (z + t • r))) : u = v := by
  rcases fiber_nonempty hz.2 with ⟨x, hx⟩
  by_contra huv
  have hpos : 0 < dist u v := dist_pos.mpr huv
  obtain ⟨k, hk⟩ := exists_nat_gt ((micpDiam M).toReal / dist u v + 1)
  have hk0 : 0 < (k : ℝ) := by
    have := ENNReal.toReal_nonneg (a := micpDiam M)
    have := div_nonneg this hpos.le
    linarith
  have hmem : z + (k : ℝ) • r ∈ indexSet M ∩ intLattice d :=
    ⟨hrI z hz.2 k hk0.le, lattice_add_nsmul hz.1 hrZ k⟩
  have hb := (Metric.edist_le_ediam_of_mem (hu k hk0 z hz x hx)
    (hv k hk0 z hz x hx)).trans (integer_fiber_ediam hmem)
  have hd := ENNReal.toReal_mono hD.ne hb
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, dist_add_left, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos hk0] at hd
  have hh : (micpDiam M).toReal / dist u v < (k : ℝ) := by linarith
  have := (div_lt_iff₀ hpos).mp hh
  linarith

lemma ray_union_convex (hM : Convex ℝ M) (z r : Fin d → ℝ) :
    Convex ℝ (⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M w) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_iUnion, mem_ofPred] at hx hy ⊢
  rcases hx with ⟨_, ⟨t, ht, rfl⟩, hx⟩
  rcases hy with ⟨_, ⟨s, hs, rfl⟩, hy⟩
  have heq : a • (z + t • r) + b • (z + s • r) = z + (a*t+b*s) • r := by
    rw [show b = 1-a by linarith]
    module
  exact ⟨_, ⟨a*t+b*s, by positivity, rfl⟩,
    heq ▸ fiber_combo hM hx hy ha hb hab⟩

lemma ray_later_closure (hM : Convex ℝ M) {z r : Fin d → ℝ} {x₀ x : Pt n}
    (hbase : ∀ L : ℝ, 0 < L → x₀ ∈ closure (zProj M (z + L • r)))
    {t k : ℝ} (ht : 0 ≤ t) (htk : t < k) (hx : x ∈ zProj M (z + t • r)) :
    x ∈ closure (zProj M (z + k • r)) := by
  have hc : Tendsto (fun b : ℝ => (1-b) • x + b • x₀) (𝓝[>] 0) (𝓝 x) := by
    have hh : Continuous (fun b : ℝ => (1-b) • x + b • x₀) := by fun_prop
    simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply isClosed_closure.mem_of_tendsto hc
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with b hb
  have hL : 0 < t + (k-t)/b :=
    add_pos_of_nonneg_of_pos ht (div_pos (sub_pos.mpr htk) hb.1)
  have heq : (1-b) • (z+t•r) + b • (z+(t+(k-t)/b)•r) = z+k•r := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hb.1.ne']
    ring
  exact heq ▸ fiber_combo_closure_right hM hx (hbase _ hL)
    (by linarith [hb.2]) hb.1.le (by ring)

lemma ray_zero_conclusions (hM : Convex ℝ M) {r : Fin d → ℝ}
    (hrZ : r ∈ intLattice d) (hrI : r ∈ recCone (indexSet M))
    (hu : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M,
      ∀ x ∈ zProj M z, x ∈ closure (zProj M (z + t • r)))
    (z : Fin d → ℝ) (hz : z ∈ intLattice d ∩ indexSet M) :
    Convex ℝ (⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z+t•r}, zProj M w) ∧
    Metric.ediam (⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z+t•r}, zProj M w) ≤ micpDiam M ∧
    (⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z+t•r} ∩ intLattice d, zProj M w) ⊆
      (⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z+t•r}, zProj M w) ∧
    (⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z+t•r}, zProj M w) ⊆
      ⋃ w ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z+t•r} ∩ intLattice d,
        closure (zProj M w) := by
  rcases fiber_nonempty hz.2 with ⟨x₀, hx₀⟩
  have hbase : ∀ L : ℝ, 0 < L → x₀ ∈ closure (zProj M (z+L•r)) :=
    fun L hL => hu L hL z hz x₀ hx₀
  refine ⟨ray_union_convex hM z r, ?_, ?_, ?_⟩
  · apply Metric.ediam_le
    intro x hx y hy
    simp only [mem_iUnion, mem_ofPred] at hx hy
    rcases hx with ⟨_, ⟨t, ht, rfl⟩, hx⟩
    rcases hy with ⟨_, ⟨s, hs, rfl⟩, hy⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (max t s)
    have htk : t < (k : ℝ) := (le_max_left _ _).trans_lt hk
    have hsk : s < (k : ℝ) := (le_max_right _ _).trans_lt hk
    exact (Metric.edist_le_ediam_of_mem (ray_later_closure hM hbase ht htk hx)
      (ray_later_closure hM hbase hs hsk hy)).trans
      (integer_fiber_ediam ⟨hrI z hz.2 k (by positivity), lattice_add_nsmul hz.1 hrZ k⟩)
  · intro x hx
    simp only [mem_iUnion] at hx ⊢
    rcases hx with ⟨w, hw, hx⟩
    exact ⟨w, hw.1, hx⟩
  · intro x hx
    simp only [mem_iUnion, mem_ofPred] at hx ⊢
    rcases hx with ⟨_, ⟨t, ht, rfl⟩, hx⟩
    obtain ⟨k, hk⟩ := exists_nat_gt t
    exact ⟨z+(k : ℝ)•r, ⟨⟨k, by positivity, rfl⟩, lattice_add_nsmul hz.1 hrZ k⟩,
      ray_later_closure hM hbase ht hk hx⟩

end MICPRep.Periodic.AsymptoticGeometry


-- Complete local proof from RayExistence.lean.
namespace MICPRep.Periodic.AsymptoticGeometry

open Set Filter
open scoped Topology

variable {n p d : ℕ} {M : Set (Ambient n p d)}

lemma ray_drift_exists (hM : Convex ℝ M) (hD : micpDiam M < ⊤)
    {z r : Fin d → ℝ} (hz : z ∈ intLattice d ∩ indexSet M)
    (hrZ : r ∈ intLattice d) (hrI : r ∈ recCone (indexSet M)) :
    ∃ u : Pt n, ∀ t : ℝ, 0 < t → ∀ x ∈ zProj M z,
      x + t • u ∈ closure (zProj M (z + t • r)) := by
  classical
  rcases fiber_nonempty hz.2 with ⟨x₀, hx₀⟩
  have hne (k : ℕ) : (zProj M (z+((k : ℝ)+1)•r)).Nonempty :=
    fiber_nonempty (hrI z hz.2 _ (by positivity))
  choose X hX using hne
  let v : ℕ → Pt n := fun k => (1/((k : ℝ)+1)) • (X k-x₀)
  have hclose (k l : ℕ) (hkl : k ≤ l) :
      dist (v k) (v l) ≤ (micpDiam M).toReal / ((k : ℝ)+1) := by
    let a : ℝ := ((k : ℝ)+1)/((l : ℝ)+1)
    have hk : 0 < (k : ℝ)+1 := by positivity
    have hl : 0 < (l : ℝ)+1 := by positivity
    have ha : 0 ≤ a := (div_pos hk hl).le
    have ha1 : a ≤ 1 := (div_le_one hl).mpr (by exact_mod_cast Nat.add_le_add_right hkl 1)
    have hzid : (1-a) • z + a • (z+((l : ℝ)+1)•r) = z+((k : ℝ)+1)•r := by
      dsimp [a]
      match_scalars <;> field_simp
      all_goals ring
    have hmem := hzid ▸ fiber_combo hM hx₀ (hX l) (sub_nonneg.mpr ha1) ha (by ring)
    have hb := (Metric.edist_le_ediam_of_mem (subset_closure (hX k))
      (subset_closure hmem)).trans (integer_fiber_ediam
        ⟨hrI z hz.2 _ hk.le, by simpa using lattice_add_nsmul hz.1 hrZ (k+1)⟩)
    have hd := ENNReal.toReal_mono hD.ne hb
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hd
    have hid : v k-v l = (1/((k : ℝ)+1)) •
        (X k-((1-a) • x₀+a • X l)) := by
      dsimp [v, a]
      match_scalars <;> field_simp
      all_goals ring
    rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hk)]
    have hn := mul_le_mul_of_nonneg_left hd (one_div_pos.mpr hk).le
    simpa [dist_eq_norm, div_eq_mul_inv, mul_comm] using hn
  have hv : CauchySeq v := cauchySeq_of_le_tendsto_0'
    (fun k => (micpDiam M).toReal / ((k : ℝ)+1)) hclose (by
      simpa [div_eq_mul_inv] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (micpDiam M).toReal)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hv
  refine ⟨u, ?_⟩
  intro t ht x hx
  have hcoef : Tendsto (fun k : ℕ => t/((k : ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
  have hlim : Tendsto (fun k : ℕ => (1-t/((k : ℝ)+1)) • x +
      t • v k + (t/((k : ℝ)+1)) • x₀) atTop (𝓝 (x+t•u)) := by
    simpa using ((((tendsto_const_nhds (x := (1 : ℝ))).sub hcoef).smul_const x).add
      (hu.const_smul t)).add (hcoef.smul_const x₀)
  apply isClosed_closure.mem_of_tendsto hlim
  have hevent : ∀ᶠ k : ℕ in atTop, t ≤ (k : ℝ)+1 := by
    have hh : Tendsto (fun k : ℕ => (k : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact hh.eventually (eventually_ge_atTop t)
  filter_upwards [hevent] with k hk
  have hk0 : 0 < (k : ℝ)+1 := by positivity
  have hc0 : 0 ≤ t/((k : ℝ)+1) := (div_pos ht hk0).le
  have hc1 : t/((k : ℝ)+1) ≤ 1 := (div_le_one hk0).mpr hk
  have hzid : (1-t/((k : ℝ)+1)) • z +
      (t/((k : ℝ)+1)) • (z+((k : ℝ)+1)•r) = z+t•r := by
    match_scalars <;> field_simp
    all_goals ring
  have hid : (1-t/((k : ℝ)+1)) • x + t • v k +
      (t/((k : ℝ)+1)) • x₀ =
      (1-t/((k : ℝ)+1)) • x + (t/((k : ℝ)+1)) • X k := by
    dsimp [v]
    module
  rw [hid]
  exact subset_closure (hzid ▸ fiber_combo hM hx (hX k) (sub_nonneg.mpr hc1)
    hc0 (by ring))

end MICPRep.Periodic.AsymptoticGeometry


-- Complete local proof from CommonDrift.lean.
namespace MICPRep.Periodic.AsymptoticGeometry

open Set

variable {n p d : ℕ} {M : Set (Ambient n p d)}

lemma integer_support_width_bound (hD : micpDiam M < ⊤) (c : Pt n)
    {z : Fin d → ℝ} (hz : z ∈ indexSet M ∩ intLattice d) :
    supportFn (zProj M z) c + supportFn (zProj M z) (-c) ≤
      ((2 * ‖c‖ * (micpDiam M).toReal : ℝ) : EReal) := by
  obtain ⟨x, hx⟩ := fiber_nonempty hz.1
  have hdist (y : Pt n) (hy : y ∈ zProj M z) : dist y x ≤ (micpDiam M).toReal := by
    have h := (Metric.edist_le_ediam_of_mem (subset_closure hy) (subset_closure hx)).trans
      (integer_fiber_ediam hz)
    have h' := ENNReal.toReal_mono hD.ne h
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h'
  have hs (a : Pt n) : supportFn (zProj M z) a ≤
      ((inner ℝ a x + ‖a‖ * (micpDiam M).toReal : ℝ) : EReal) := by
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    apply EReal.coe_le_coe_iff.mpr
    have hinner := (real_inner_le_norm a (y - x)).trans
      (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hdist y hy) (norm_nonneg a))
    rw [inner_sub_right] at hinner
    linarith
  have h := add_le_add (hs c) (hs (-c))
  simpa only [norm_neg, inner_neg_left, ← EReal.coe_add,
    show inner ℝ c x + ‖c‖ * (micpDiam M).toReal +
      (-inner ℝ c x + ‖c‖ * (micpDiam M).toReal) =
      2 * ‖c‖ * (micpDiam M).toReal by ring] using h

lemma closure_pair_support_width {A : Set (Pt n)} (c : Pt n) {x y : Pt n}
    (hx : x ∈ closure A) (hy : y ∈ closure A) :
    ((inner ℝ c (x - y) : ℝ) : EReal) ≤ supportFn A c + supportFn A (-c) := by
  apply closure_minimal (t := {x : Pt n |
    ((inner ℝ c (x - y) : ℝ) : EReal) ≤ supportFn A c + supportFn A (-c)}) ?_ ?_ hx
  · intro x hx
    apply closure_minimal (t := {y : Pt n |
      ((inner ℝ c (x - y) : ℝ) : EReal) ≤ supportFn A c + supportFn A (-c)}) ?_ ?_ hy
    · intro y hy
      have h₁ : ((inner ℝ c x : ℝ) : EReal) ≤ supportFn A c :=
        le_iSup_of_le x (le_iSup_of_le hx le_rfl)
      have h₂ : ((inner ℝ (-c) y : ℝ) : EReal) ≤ supportFn A (-c) :=
        le_iSup_of_le y (le_iSup_of_le hy le_rfl)
      simpa only [Set.mem_ofPred_eq, inner_sub_right, inner_neg_left, ← EReal.coe_add, ← sub_eq_add_neg]
        using add_le_add h₁ h₂
    · exact isClosed_le (continuous_coe_real_ereal.comp (by fun_prop)) continuous_const
  · exact isClosed_le (continuous_coe_real_ereal.comp (by fun_prop)) continuous_const

lemma real_fiber_pair_bound {S : Set (Pt n)} (hM : Induces M S)
    (hD : micpDiam M < ⊤)
    (hint : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty)
    (c : Pt n) : ∃ B : ℝ, ∀ z ∈ IZ (indexSet M), ∀ x ∈ closure (zProj M z),
      ∀ y ∈ closure (zProj M z), inner ℝ c (x - y) ≤ B := by
  have htransfer := (MICPRep.Periodic.lemma_6_11 M S hM).2.2 hint c
  simp only [sub_eq_add_neg, neg_neg] at htransfer
  have hintbound : (⨆ z ∈ IZ (indexSet M) ∩ intLattice d,
      supportFn (zProj M z) c + supportFn (zProj M z) (-c)) < ⊤ := by
    apply lt_of_le_of_lt _ (EReal.coe_lt_top (2 * ‖c‖ * (micpDiam M).toReal))
    exact iSup_le fun z => iSup_le fun hz => integer_support_width_bound hD c ⟨hz.1.1, hz.2⟩
  have hfull := htransfer.mp hintbound
  let B : ℝ := (⨆ z ∈ IZ (indexSet M),
    supportFn (zProj M z) c + supportFn (zProj M z) (-c)).toReal
  refine ⟨B, fun z hz x hx y hy => ?_⟩
  have hs : supportFn (zProj M z) c + supportFn (zProj M z) (-c) ≤
      ⨆ w ∈ IZ (indexSet M), supportFn (zProj M w) c + supportFn (zProj M w) (-c) :=
    le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  have hb : ((inner ℝ c (x - y) : ℝ) : EReal) ≤ (B : EReal) :=
    (closure_pair_support_width c hx hy).trans (hs.trans (EReal.le_coe_toReal hfull.ne))
  exact EReal.coe_le_coe_iff.mp hb

lemma drift_eq {S : Set (Pt n)} (hM : Induces M S) (hD : micpDiam M < ⊤)
    (hint : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty)
    {z z' r : Fin d → ℝ} (hz : z ∈ intLattice d ∩ indexSet M)
    (hz' : z' ∈ intLattice d ∩ indexSet M) (hrZ : r ∈ intLattice d)
    (hrI : r ∈ recCone (indexSet M)) {u v : Pt n}
    (hu : ∀ t : ℝ, 0 < t → ∀ x ∈ zProj M z,
      x + t • u ∈ closure (zProj M (z + t • r)))
    (hv : ∀ t : ℝ, 0 < t → ∀ x ∈ zProj M z',
      x + t • v ∈ closure (zProj M (z' + t • r))) : u = v := by
  obtain ⟨x, hx⟩ := fiber_nonempty hz.2
  obtain ⟨y, hy⟩ := fiber_nonempty hz'.2
  obtain ⟨B, hB⟩ := real_fiber_pair_bound hM hD hint (u - v)
  by_contra huv
  have hpos : 0 < inner ℝ (u - v) (u - v) := real_inner_self_pos.mpr (sub_ne_zero.mpr huv)
  obtain ⟨k, hk⟩ := exists_nat_gt (B / inner ℝ (u - v) (u - v) + 1)
  let l : ℕ := k + 1
  have hl : 0 < (l : ℝ) := by dsimp [l]; positivity
  have hhu := hu (2 * l) (by positivity) x hx
  have hhv := hv (2 * l) (by positivity) y hy
  have hleft := fiber_combo_closure_right hM.2.1 hy hhu
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hright := fiber_combo_closure_right hM.2.1 hx hhv
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hindex : (1 / 2 : ℝ) • z' + (1 / 2 : ℝ) • (z + (2 * (l : ℝ)) • r) =
      (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (z' + (2 * (l : ℝ)) • r) := by module
  rw [hindex] at hleft
  have hI : Convex ℝ (indexSet M) := by
    rintro z₁ ⟨v₁, hv₁, rfl⟩ z₂ ⟨v₂, hv₂, rfl⟩ a b ha hb hab
    exact ⟨a • v₁ + b • v₂, hM.2.1 hv₁ hv₂ ha hb hab, rfl⟩
  have hlateI : z' + (2 * (l : ℝ)) • r ∈ indexSet M := hrI z' hz'.2 _ (by positivity)
  have hlateZ : z' + (2 * (l : ℝ)) • r ∈ intLattice d := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using lattice_add_nsmul hz'.1 hrZ (2 * l)
  have hmid : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (z' + (2 * (l : ℝ)) • r) ∈
      IZ (indexSet M) := by
    exact ⟨hI hz.2 hlateI (by norm_num) (by norm_num) (by norm_num),
      (affZ (indexSet M)).convex (subset_affineSpan ℝ _ ⟨hz.2, hz.1⟩)
        (subset_affineSpan ℝ _ ⟨hlateI, hlateZ⟩)
        (by norm_num) (by norm_num) (by norm_num)⟩
  have hbound := hB _ hmid _ hleft _ hright
  have hdiff : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (x + (2 * (l : ℝ)) • u) -
      ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (y + (2 * (l : ℝ)) • v)) =
      (l : ℝ) • (u - v) := by module
  rw [hdiff, inner_smul_right] at hbound
  have hlarge : B / inner ℝ (u - v) (u - v) < (l : ℝ) := by
    dsimp [l]
    push_cast
    linarith
  have := (div_lt_iff₀ hpos).mp hlarge
  linarith

end MICPRep.Periodic.AsymptoticGeometry


open MICPRep.Periodic MICPRep.Periodic.AsymptoticGeometry
open scoped ENNReal Matrix

theorem solution {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (hD : micpDiam M < ⊤)
    (hint : (intrinsicInterior ℝ (IZ (indexSet M)) ∩ intLattice d).Nonempty)
    (r : Fin d → ℝ) (hrZ : r ∈ intLattice d) (hrI : r ∈ recCone (indexSet M)) (hr0 : r ≠ 0) :
    (∃! u : Pt n, ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M, ∀ x ∈ zProj M z,
        x + t • u ∈ closure (zProj M (z + t • r))) ∧
    ∀ u : Pt n, (∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M, ∀ x ∈ zProj M z,
        x + t • u ∈ closure (zProj M (z + t • r))) → u = 0 →
      ∀ z ∈ intLattice d ∩ indexSet M,
        Convex ℝ (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ∧
        Metric.ediam (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ≤ micpDiam M ∧
        (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r} ∩ intLattice d, zProj M z') ⊆
          (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ∧
        (⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r}, zProj M z') ⊆
          ⋃ z' ∈ {w | ∃ t : ℝ, 0 ≤ t ∧ w = z + t • r} ∩ intLattice d,
            closure (zProj M z') := by
  obtain ⟨z₀, hz₀, hz₀Z⟩ := hint
  have hz₀I : z₀ ∈ indexSet M := (intrinsicInterior_subset hz₀).1
  have hz₀' : z₀ ∈ intLattice d ∩ indexSet M := ⟨hz₀Z, hz₀I⟩
  obtain ⟨u, hu⟩ := ray_drift_exists hM.1.2.1 hD hz₀' hrZ hrI
  have hall : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M,
      ∀ x ∈ zProj M z, x+t•u ∈ closure (zProj M (z+t•r)) := by
    intro t ht z hz x hx
    obtain ⟨v, hv⟩ := ray_drift_exists hM.1.2.1 hD hz hrZ hrI
    have huv : u = v := drift_eq hM.1 hD ⟨z₀, hz₀, hz₀Z⟩ hz₀' hz hrZ hrI hu hv
    simpa only [huv] using hv t ht x hx
  refine ⟨⟨u, hall, ?_⟩, ?_⟩
  · intro v hv
    exact drift_unique hD hz₀' hrZ hrI hv hall
  · intro v hv hv0 z hz
    subst v
    have hzero : ∀ t : ℝ, 0 < t → ∀ z ∈ intLattice d ∩ indexSet M,
        ∀ x ∈ zProj M z, x ∈ closure (zProj M (z+t•r)) := by
      simpa only [smul_zero, add_zero] using hv
    exact ray_zero_conclusions hM.1.2.1 hrZ hrI hzero z hz
