-- Prove2me | solution 1 for MechanismDesign.Screening.monotoneAllocations_compact_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:18:49.135803+00:00
-- url     : https://prove2.me/submissions/035e1b7f-d698-487f-9c75-93b9c457a864

import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

open MeasureTheory Filter Topology

namespace MechanismDesign.Screening

instance typeMeasure_finite' (θlo θhi : ℝ) : IsFiniteMeasure (typeMeasure θlo θhi) :=
  isFiniteMeasure_restrict.2 (by simp)

noncomputable def extF (q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) : ℝ → ℝ :=
  fun x => q (Set.projIcc a b hab x)

lemma extF_eq {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    extF q a b hab x = q x := by
  simp [extF, Set.projIcc_of_mem hab hx]

lemma extF_mono {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hm : MonotoneOn q (Set.Icc a b)) :
    Monotone (extF q a b hab) := by
  intro x y hxy
  exact hm (Set.projIcc a b hab x).2 (Set.projIcc a b hab y).2 (Set.monotone_projIcc hab hxy)

lemma extF_mem {q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h01 : ∀ x ∈ Set.Icc a b, q x ∈ Set.Icc (0:ℝ) 1) (x : ℝ) :
    extF q a b hab x ∈ Set.Icc (0:ℝ) 1 := h01 _ (Set.projIcc a b hab x).2

/-- Helly-type selection: a sequence of monotone functions with values in `[0,1]` has a
subsequence converging at every continuity point of a monotone `[0,1]`-valued limit. -/
lemma helly (h : ℕ → ℝ → ℝ) (hm : ∀ n, Monotone (h n)) (h01 : ∀ n x, h n x ∈ Set.Icc (0:ℝ) 1) :
    ∃ H : ℝ → ℝ, Monotone H ∧ (∀ x, H x ∈ Set.Icc (0:ℝ) 1) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ x, ContinuousAt H x → Tendsto (fun k => h (φ k) x) atTop (𝓝 (H x)) := by
  set K : Set (ℚ → ℝ) := Set.univ.pi (fun _ => Set.Icc (0:ℝ) 1)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨L, hLK, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n (r : ℚ) => h n r)
    (fun n r _ => h01 n r)
  have hlimr : ∀ r : ℚ, Tendsto (fun k => h (φ k) r) atTop (𝓝 (L r)) := by
    intro r
    exact (tendsto_pi_nhds.1 hlim) r
  have hL01 : ∀ r, L r ∈ Set.Icc (0:ℝ) 1 := fun r => hLK r trivial
  have hLm : Monotone L := by
    intro r s hrs
    exact le_of_tendsto_of_tendsto' (hlimr r) (hlimr s)
      (fun k => hm (φ k) (by exact_mod_cast hrs))
  set H : ℝ → ℝ := fun x => ⨆ r : {r : ℚ // (r:ℝ) < x}, L r with hH
  have hne : ∀ x : ℝ, Nonempty {r : ℚ // (r:ℝ) < x} := fun x =>
    ⟨⟨(exists_rat_lt x).choose, (exists_rat_lt x).choose_spec⟩⟩
  have hbdd : ∀ x : ℝ, BddAbove (Set.range (fun r : {r : ℚ // (r:ℝ) < x} => L r)) :=
    fun x => ⟨1, by rintro _ ⟨r, rfl⟩; exact (hL01 r).2⟩
  have hLH : ∀ (r : ℚ) (y : ℝ), (r:ℝ) < y → L r ≤ H y := fun r y hry =>
    le_ciSup (hbdd y) ⟨r, hry⟩
  have hHL : ∀ (x : ℝ) (s : ℚ), x ≤ (s:ℝ) → H x ≤ L s := by
    intro x s hxs
    haveI := hne x
    exact ciSup_le (fun r => hLm (by exact_mod_cast (r.2.trans_le hxs).le))
  have hHm : Monotone H := by
    intro x y hxy
    haveI := hne x
    exact ciSup_le (fun r => hLH r y (lt_of_lt_of_le r.2 hxy))
  have hH01 : ∀ x, H x ∈ Set.Icc (0:ℝ) 1 := by
    intro x
    haveI := hne x
    obtain ⟨r⟩ := hne x
    exact ⟨(hL01 r).1.trans (hLH r x r.2), ciSup_le (fun r => (hL01 r).2)⟩
  refine ⟨H, hHm, hH01, φ, hφ, ?_⟩
  intro x hx
  rw [tendsto_order]; constructor
  · intro a ha
    haveI := hne x
    obtain ⟨⟨r, hr⟩, har⟩ := exists_lt_of_lt_ciSup ha
    filter_upwards [(tendsto_order.1 (hlimr r)).1 a har] with k hk
    exact lt_of_lt_of_le hk (hm (φ k) hr.le)
  · intro b hb
    have hev : {y | H y < b} ∈ 𝓝 x := hx (Iio_mem_nhds hb)
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hev
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hu
    have hy : H ((s + u) / 2) < b := hsub ⟨by linarith, by linarith⟩
    have hLs : L s < b := lt_of_le_of_lt (hLH s _ (by linarith)) hy
    filter_upwards [(tendsto_order.1 (hlimr s)).2 b hLs] with k hk
    exact lt_of_le_of_lt (hm (φ k) hs1.le) hk

theorem monotoneAllocations_compact_convex_core {θlo θhi : ℝ} (hlt : θlo < θhi) :
    IsCompact (monotoneAllocations θlo θhi) ∧ Convex ℝ (monotoneAllocations θlo θhi) := by
  have hab := hlt.le
  set μ := typeMeasure θlo θhi
  have hmemIcc : ∀ᵐ x ∂μ, x ∈ Set.Icc θlo θhi := ae_restrict_mem measurableSet_Icc
  constructor
  · apply IsSeqCompact.isCompact
    intro u hu
    choose q hqm hq01 hqae using hu
    set h : ℕ → ℝ → ℝ := fun n => extF (q n) θlo θhi hab
    have hm : ∀ n, Monotone (h n) := fun n => extF_mono hab (hqm n)
    have h01 : ∀ n x, h n x ∈ Set.Icc (0:ℝ) 1 := fun n x => extF_mem hab (hq01 n) x
    have hae : ∀ n, (u n : ℝ → ℝ) =ᵐ[μ] h n := by
      intro n
      filter_upwards [hqae n, hmemIcc] with x h1 h2
      rw [h1]; exact (extF_eq hab h2).symm
    obtain ⟨H, hHm, hH01, φ, hφ, hconv⟩ := helly h hm h01
    have hmemH : MemLp H 1 μ := by
      refine MemLp.of_bound hHm.measurable.aestronglyMeasurable 1 (Eventually.of_forall ?_)
      intro x; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hH01 x).1, (hH01 x).2]
    set G : L1Space θlo θhi := hmemH.toLp H
    have hGae : (G : ℝ → ℝ) =ᵐ[μ] H := MemLp.coeFn_toLp hmemH
    refine ⟨G, ⟨H, hHm.monotoneOn _, fun x _ => hH01 x, hGae⟩, φ, hφ, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have hdist : ∀ k, dist (u (φ k)) G = ∫ x, |h (φ k) x - H x| ∂μ := by
      intro k
      rw [dist_eq_norm, L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (u (φ k)) G, hae (φ k), hGae] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, Real.norm_eq_abs]
    refine Tendsto.congr (fun k => (hdist k).symm) ?_
    have hcount : ∀ᵐ x ∂(volume : Measure ℝ), ContinuousAt H x := by
      rw [ae_iff]
      exact Set.Countable.measure_zero hHm.countable_not_continuousAt _
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun k x => |h (φ k) x - H x|) (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
      (fun k => (((hm (φ k)).measurable.sub hHm.measurable).abs).aestronglyMeasurable)
      (integrable_const 1)
      (fun k => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        constructor <;> linarith [(h01 (φ k) x).1, (h01 (φ k) x).2, (hH01 x).1, (hH01 x).2]))
      (by
        filter_upwards [ae_restrict_of_ae hcount] with x hx
        have := (hconv x hx).sub_const (H x)
        rw [sub_self] at this
        simpa using this.abs)
    simpa using this
  · rintro g1 ⟨q1, hm1, h1, hae1⟩ g2 ⟨q2, hm2, h2, hae2⟩ a b ha hb hab1
    refine ⟨fun x => a * q1 x + b * q2 x, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      have := hm1 hx hy hxy; have := hm2 hx hy hxy
      dsimp only
      nlinarith [mul_le_mul_of_nonneg_left (hm1 hx hy hxy) ha,
        mul_le_mul_of_nonneg_left (hm2 hx hy hxy) hb]
    · intro x hx
      have e1 := h1 x hx; have e2 := h2 x hx
      constructor
      · nlinarith [mul_nonneg ha e1.1, mul_nonneg hb e2.1]
      · nlinarith [mul_le_mul_of_nonneg_left e1.2 ha, mul_le_mul_of_nonneg_left e2.2 hb]
    · filter_upwards [Lp.coeFn_add (a • g1) (b • g2), Lp.coeFn_smul a g1, Lp.coeFn_smul b g2,
        hae1, hae2] with x e1 e2 e3 e4 e5
      rw [e1, Pi.add_apply, e2, e3, Pi.smul_apply, Pi.smul_apply, e4, e5, smul_eq_mul, smul_eq_mul]

end MechanismDesign.Screening

open MechanismDesign.Screening


theorem solution {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi) :
    IsCompact (monotoneAllocations θlo θhi) ∧ Convex ℝ (monotoneAllocations θlo θhi) := by
  exact monotoneAllocations_compact_convex_core hlt
