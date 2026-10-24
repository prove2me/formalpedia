-- Prove2me | solution 1 for MICPRep.Periodic.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:45:10.385656+00:00
-- url     : https://prove2.me/submissions/80ad50b4-7cc9-4a89-b793-667a4a9177c9

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

/- Complete task-local helper proof bodies from GroupedHull.lean. -/

namespace MICPRep.Periodic.BinaryLift

/-- Group a convex combination by its member of a finite convex family. -/
theorem grouped_hull {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ι → Set E) (hne : ∀ i, (C i).Nonempty) (hc : ∀ i, Convex ℝ (C i))
    {x : E} (hx : x ∈ convexHull ℝ (⋃ i, C i)) :
    ∃ (w : ι → ℝ) (u : ι → E), (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ i, u i ∈ C i) ∧ (∑ i, w i • u i = x) := by
  classical
  choose c hc' using hne
  apply convexHull_min (t := {x | ∃ (w : ι → ℝ) (u : ι → E),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, u i ∈ C i) ∧
      (∑ i, w i • u i = x)}) ?_ ?_ hx
  · intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    refine ⟨Pi.single j 1, Function.update c j y, ?_, by simp, ?_, by simp⟩
    · intro i
      by_cases h : i = j <;> simp [h]
    · intro i
      by_cases h : i = j
      · subst i
        simpa using hj
      · simpa [Function.update_of_ne h] using hc' i
  · rintro x ⟨w, u, hw, hws, hu, hxu⟩ y ⟨w', u', hw', hws', hu', hyu⟩ a b ha hb hab
    let W := fun i => a * w i + b * w' i
    have hW (i) : 0 ≤ W i := add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hw' i))
    let U := fun i => if W i = 0 then c i else (a * w i / W i) • u i + (b * w' i / W i) • u' i
    have hU (i) : U i ∈ C i := by
      by_cases h : W i = 0
      · simpa [U, h] using hc' i
      · have he : a * w i / W i + b * w' i / W i = 1 := by
          rw [← add_div]
          exact div_self h
        exact (show U i = _ from if_neg h) ▸
          hc i (hu i) (hu' i) (div_nonneg (mul_nonneg ha (hw i)) (hW i))
            (div_nonneg (mul_nonneg hb (hw' i)) (hW i)) he
    have hterm (i) : W i • U i = (a * w i) • u i + (b * w' i) • u' i := by
      by_cases h : W i = 0
      · have h0 : a * w i = 0 := by dsimp [W] at h; nlinarith [mul_nonneg ha (hw i), mul_nonneg hb (hw' i)]
        have h1 : b * w' i = 0 := by dsimp [W] at h; nlinarith [mul_nonneg ha (hw i), mul_nonneg hb (hw' i)]
        simp [h, h0, h1]
      · dsimp [U]
        rw [if_neg h, smul_add, smul_smul, smul_smul]
        congr 1 <;> congr 1 <;> field_simp
    refine ⟨W, U, hW, ?_, hU, ?_⟩
    · simp only [W, Finset.sum_add_distrib, ← Finset.mul_sum, hws, hws', mul_one, hab]
    · simp only [hterm, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hxu, hyu]

theorem hull_translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Set E) (d : E) (hs : ∀ x ∈ s, x + d ∈ s)
    {x : E} (hx : x ∈ convexHull ℝ s) : x + d ∈ convexHull ℝ s := by
  have hm : x ∈ ((fun y => y + d) ⁻¹' convexHull ℝ s) :=
    convexHull_min (t := (fun y => y + d) ⁻¹' convexHull ℝ s)
      (fun y hy => subset_convexHull ℝ s (hs y hy))
      ((convex_convexHull ℝ s).translate_preimage_left d) hx
  exact hm

def QuadraticEpigraph {n q : ℕ} (C : Set (Pt n × (Fin q → ℝ))) :
    Set ((Pt n × (Fin q → ℝ)) × ℝ) :=
  {p | p.1 ∈ C ∧ ‖p.1.1‖ ^ 2 + ∑ j, (p.1.2 j) ^ 2 ≤ p.2}

theorem quadraticEpigraph_nonempty {n q : ℕ} (C : Set (Pt n × (Fin q → ℝ)))
    (hC : C.Nonempty) : (QuadraticEpigraph C).Nonempty := by
  obtain ⟨w, hw⟩ := hC
  exact ⟨(w, ‖w.1‖ ^ 2 + ∑ j, (w.2 j) ^ 2), hw, le_rfl⟩

theorem quadraticEpigraph_isClosed {n q : ℕ} (C : Set (Pt n × (Fin q → ℝ)))
    (hC : IsClosed C) : IsClosed (QuadraticEpigraph C) := by
  apply (hC.preimage continuous_fst).inter
  exact isClosed_le
    (show Continuous (fun p : (Pt n × (Fin q → ℝ)) × ℝ => ‖p.1.1‖ ^ 2 + ∑ j, (p.1.2 j) ^ 2) by fun_prop)
    continuous_snd

theorem norm_sq_combo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
  exact ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))).pow
    (fun _ _ => norm_nonneg _) 2).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab

theorem quadraticEpigraph_convex {n q : ℕ} (C : Set (Pt n × (Fin q → ℝ)))
    (hC : Convex ℝ C) : Convex ℝ (QuadraticEpigraph C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
  have hn := norm_sq_combo x.1.1 y.1.1 ha hb hab
  have hi (j : Fin q) : (a * x.1.2 j + b * y.1.2 j) ^ 2 ≤
      a * (x.1.2 j) ^ 2 + b * (y.1.2 j) ^ 2 := by
    simpa only [smul_eq_mul, Real.norm_eq_abs, sq_abs] using
      norm_sq_combo (x.1.2 j) (y.1.2 j) ha hb hab
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hi j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  change ‖a • x.1.1 + b • y.1.1‖ ^ 2 + ∑ j, (a * x.1.2 j + b * y.1.2 j) ^ 2 ≤ a * x.2 + b * y.2
  nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

theorem quadraticEpigraph_norm_sq_le {n q : ℕ} (C : Set (Pt n × (Fin q → ℝ)))
    {p : (Pt n × (Fin q → ℝ)) × ℝ} (hp : p ∈ QuadraticEpigraph C) : ‖p.1‖ ^ 2 ≤ p.2 := by
  have hs : 0 ≤ ∑ j : Fin q, (p.1.2 j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp0 : 0 ≤ p.2 := le_trans (add_nonneg (sq_nonneg _) hs) hp.2
  have hn : ‖p.1‖ ≤ Real.sqrt p.2 := by
    rw [norm_prod_le_iff]
    constructor
    · apply (Real.le_sqrt (norm_nonneg _) hp0).mpr
      linarith [hp.2]
    · apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro j
      apply (Real.le_sqrt (norm_nonneg _) hp0).mpr
      rw [Real.norm_eq_abs, sq_abs]
      have hj := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => sq_nonneg (p.1.2 i)) (Finset.mem_univ j)
      linarith [hp.2, sq_nonneg ‖p.1.1‖]
  nlinarith [Real.sq_sqrt hp0, Real.sqrt_nonneg p.2, norm_nonneg p.1]

theorem quadraticEpigraph_upward {n q : ℕ} (C : Set (Pt n × (Fin q → ℝ)))
    {p : (Pt n × (Fin q → ℝ)) × ℝ} (hp : p ∈ QuadraticEpigraph C)
    {t : ℝ} (ht : 0 ≤ t) : (p.1, p.2 + t) ∈ QuadraticEpigraph C :=
  ⟨hp.1, le_trans hp.2 (le_add_of_nonneg_right ht)⟩

end MICPRep.Periodic.BinaryLift

/- Complete task-local helper proof bodies from ClosedFiber.lean. -/

namespace MICPRep.Periodic.ClosedFiber

/-- Closed component sets with quadratic perspective bounds have a closed finite-sum image. -/
theorem isClosed_sum_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {k : ℕ} (C : Fin k → Set (E × ℝ × ℝ))
    (hclosed : ∀ i, IsClosed (C i))
    (hbound : ∀ i p, p ∈ C i →
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ ‖p.1‖ ^ 2 ≤ p.2.2 * p.2.1) :
    IsClosed ((fun a : Fin k → (E × ℝ × ℝ) =>
      (∑ i, (a i).1, ∑ i, (a i).2.1, fun i => (a i).2.2)) ''
      {a | (∀ i, a i ∈ C i) ∧ ∑ i, (a i).2.2 = 1}) := by
  classical
  let F : (Fin k → (E × ℝ × ℝ)) → E × ℝ × (Fin k → ℝ) :=
    fun a => (∑ i, (a i).1, ∑ i, (a i).2.1, fun i => (a i).2.2)
  let A : Set (Fin k → (E × ℝ × ℝ)) :=
    {a | (∀ i, a i ∈ C i) ∧ ∑ i, (a i).2.2 = 1}
  have hF : Continuous F := by fun_prop
  have hA : IsClosed A := by
    have hc : IsClosed {a : Fin k → (E × ℝ × ℝ) | ∀ i, a i ∈ C i} := by
      simpa only [Set.ofPred_forall, Set.preimage] using
        isClosed_iInter (fun i => (hclosed i).preimage (continuous_apply i))
    exact hc.inter (isClosed_eq (by fun_prop) continuous_const)
  change IsClosed (F '' A)
  apply (CompactlyGeneratedSpace.isClosed_iff_of_t2 _).2
  intro K hK
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.exists_pos_norm_le
  have hb : Bornology.IsBounded (A ∩ F ⁻¹' K) := by
    apply isBounded_iff_forall_norm_le.2
    refine ⟨R + 1, ?_⟩
    intro a ha
    have hsum : ∑ j, (a j).2.1 ≤ R := by
      have hn : ‖(F a).2.1‖ ≤ R :=
        (norm_fst_le (F a).2).trans ((norm_snd_le (F a)).trans (hR (F a) ha.2))
      exact (le_abs_self _).trans hn
    apply (pi_norm_le_iff_of_nonneg (by linarith)).2
    intro i
    obtain ⟨ht0, hl0, hquad⟩ := hbound i (a i) (ha.1.1 i)
    have ht : (a i).2.1 ≤ R :=
      (Finset.single_le_sum (fun j _ => (hbound j (a j) (ha.1.1 j)).1)
        (Finset.mem_univ i)).trans hsum
    have hl : (a i).2.2 ≤ 1 := by
      calc
        (a i).2.2 ≤ ∑ j, (a j).2.2 :=
          Finset.single_le_sum (fun j _ => (hbound j (a j) (ha.1.1 j)).2.1)
            (Finset.mem_univ i)
        _ = 1 := ha.1.2
    have hq : ‖(a i).1‖ ^ 2 ≤ R :=
      hquad.trans ((mul_le_of_le_one_left ht0 hl).trans ht)
    rw [norm_prod_le_iff, norm_prod_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_nonneg (‖(a i).1‖ - 1)]
    · rw [Real.norm_eq_abs, abs_of_nonneg ht0]
      linarith
    · rw [Real.norm_eq_abs, abs_of_nonneg hl0]
      linarith
  have hc : IsCompact (A ∩ F ⁻¹' K) :=
    Metric.isCompact_of_isClosed_isBounded (hA.inter (hK.isClosed.preimage hF)) hb
  simpa only [Set.image_inter_preimage] using (hc.image hF).isClosed

end MICPRep.Periodic.ClosedFiber

/- Complete task-local helper proof bodies from QuadraticClosed.lean. -/

open scoped Topology
open Filter Set

namespace MICPRep.Periodic.QuadraticClosed

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Closed perspective variables: scaled vector, scaled epigraph height, and weight. -/
def Perspective (T : Set (W × ℝ)) : Set (W × ℝ × ℝ) :=
  {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ ‖p.1‖ ^ 2 ≤ p.2.2 * p.2.1 ∧
    (p.2.2 ≠ 0 → (p.2.2⁻¹ • p.1, p.2.2⁻¹ * p.2.1) ∈ T)}

theorem perspective_closed {T : Set (W × ℝ)} (hT : IsClosed T) :
    IsClosed (Perspective T) := by
  apply IsSeqClosed.isClosed
  intro u p hu hp
  have hw : Tendsto (fun j => (u j).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hp
  have hh : Tendsto (fun j => (u j).2.1) atTop (𝓝 p.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto p).comp hp
  have hc : Tendsto (fun j => (u j).2.2) atTop (𝓝 p.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto p).comp hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hh
      (Eventually.of_forall fun j => (hu j).1)
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hc
      (Eventually.of_forall fun j => (hu j).2.1)
  · exact le_of_tendsto_of_tendsto (hw.norm.pow 2) (hc.mul hh)
      (Eventually.of_forall fun j => (hu j).2.2.1)
  · intro hne
    have he : ∀ᶠ j in atTop, (u j).2.2 ≠ 0 :=
      hc.eventually (eventually_ne_nhds hne)
    exact hT.mem_of_tendsto
      (((hc.inv₀ hne).smul hw).prodMk_nhds
        ((hc.inv₀ hne).mul hh))
      (he.mono fun j hj => (hu j).2.2.2 hj)

theorem perspective_scaled {T : Set (W × ℝ)}
    (hbound : ∀ u ∈ T, ‖u.1‖ ^ 2 ≤ u.2)
    {u : W × ℝ} (hu : u ∈ T) {c : ℝ} (hc : 0 ≤ c) :
    (c • u.1, c * u.2, c) ∈ Perspective T := by
  have hh : 0 ≤ u.2 := (sq_nonneg ‖u.1‖).trans (hbound u hu)
  refine ⟨mul_nonneg hc hh, hc, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr (hbound u hu))]
  · intro hne
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul,
      ← mul_assoc, inv_mul_cancel₀ hne, one_mul] using hu

theorem perspective_zero_vector {T : Set (W × ℝ)} {p : W × ℝ × ℝ}
    (hp : p ∈ Perspective T) (hzero : p.2.2 = 0) : p.1 = 0 := by
  have hn : ‖p.1‖ ^ 2 ≤ 0 := by simpa only [hzero, zero_mul] using hp.2.2.1
  have : ‖p.1‖ = 0 := by nlinarith [norm_nonneg p.1]
  exact norm_eq_zero.mp this


variable {k : ℕ}

noncomputable def tag (i : Fin k) (u : W × ℝ) : W × ℝ × (Fin k → ℝ) :=
  (u.1, u.2, Pi.single i 1)

def TaggedHull (T : Fin k → Set (W × ℝ)) : Set (W × ℝ × (Fin k → ℝ)) :=
  convexHull ℝ (⋃ i, tag i '' T i)

def SumPerspectives (T : Fin k → Set (W × ℝ)) : Set (W × ℝ × (Fin k → ℝ)) :=
  (fun p : Fin k → (W × ℝ × ℝ) =>
    (∑ i, (p i).1, ∑ i, (p i).2.1, fun i => (p i).2.2)) ''
    {p | (∀ i, p i ∈ Perspective (T i)) ∧ ∑ i, (p i).2.2 = 1}

theorem tag_convex {T : Set (W × ℝ)} (hT : Convex ℝ T) (i : Fin k) :
    Convex ℝ (tag i '' T) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb hab
  refine ⟨a • u + b • v, hT hu hv ha hb hab, ?_⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  change (Pi.single i 1 : Fin k → ℝ) = a • Pi.single i 1 + b • Pi.single i 1
  rw [← add_smul, hab, one_smul]

theorem sum_tags (c : Fin k → ℝ) (u : Fin k → W × ℝ) :
    ∑ i, c i • tag i (u i) =
      (∑ i, c i • (u i).1, ∑ i, c i * (u i).2, c) := by
  classical
  apply Prod.ext
  · simp [tag, Prod.fst_sum]
  · apply Prod.ext
    · simp [tag, Prod.fst_sum, Prod.snd_sum]
    · ext j
      simp [tag, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, Pi.smul_apply]

theorem tagged_subset_sum (T : Fin k → Set (W × ℝ))
    (hne : ∀ i, (T i).Nonempty) (hc : ∀ i, Convex ℝ (T i))
    (hbound : ∀ i u, u ∈ T i → ‖u.1‖ ^ 2 ≤ u.2) :
    TaggedHull T ⊆ SumPerspectives T := by
  classical
  intro v hv
  obtain ⟨c, u, hc0, hcsum, hu, husum⟩ :=
    BinaryLift.grouped_hull (fun i => tag i '' T i)
      (fun i => (hne i).image (tag i)) (fun i => tag_convex (hc i) i) hv
  choose t ht htag using hu
  have hueq : u = fun i => tag i (t i) := funext fun i => (htag i).symm
  rw [hueq, sum_tags] at husum
  refine ⟨fun i => (c i • (t i).1, c i * (t i).2, c i), ?_, husum⟩
  exact ⟨fun i => perspective_scaled (hbound i) (ht i) (hc0 i), hcsum⟩

theorem tagged_upward (T : Fin k → Set (W × ℝ))
    (hup : ∀ i u, u ∈ T i → ∀ t, 0 ≤ t → (u.1, u.2 + t) ∈ T i)
    {v : W × ℝ × (Fin k → ℝ)} (hv : v ∈ TaggedHull T) {t : ℝ} (ht : 0 ≤ t) :
    v + (0, t, 0) ∈ TaggedHull T := by
  apply BinaryLift.hull_translate (⋃ i, tag i '' T i) (0, t, 0) ?_ hv
  intro p hp
  obtain ⟨i, u, hu, rfl⟩ := Set.mem_iUnion.mp hp
  apply Set.mem_iUnion.mpr
  refine ⟨i, (u.1, u.2 + t), hup i u hu t ht, ?_⟩
  simp [tag]


theorem sum_subset_tagged (T : Fin k → Set (W × ℝ))
    (hne : ∀ i, (T i).Nonempty)
    (hup : ∀ i u, u ∈ T i → ∀ t, 0 ≤ t → (u.1, u.2 + t) ∈ T i) :
    SumPerspectives T ⊆ TaggedHull T := by
  classical
  rintro v ⟨p, ⟨hp, hsum⟩, rfl⟩
  choose u hu using hne
  let c : Fin k → ℝ := fun i => (p i).2.2
  let t : Fin k → W × ℝ := fun i =>
    if c i = 0 then u i else ((c i)⁻¹ • (p i).1, (c i)⁻¹ * (p i).2.1)
  have ht (i : Fin k) : t i ∈ T i := by
    by_cases hi : c i = 0
    · simpa only [t, if_pos hi] using hu i
    · simpa only [t, if_neg hi] using (hp i).2.2.2 hi
  have hvec (i : Fin k) : c i • (t i).1 = (p i).1 := by
    by_cases hi : c i = 0
    · have hv := perspective_zero_vector (hp i) hi
      simp [hi, hv]
    · simp [t, hi, smul_smul]
  let δ : ℝ := ∑ i, if c i = 0 then (p i).2.1 else 0
  have hδ : 0 ≤ δ := Finset.sum_nonneg fun i _ => by
    by_cases hi : c i = 0
    · simpa only [if_pos hi] using (hp i).1
    · simp only [if_neg hi, le_refl]
  have hheight (i : Fin k) :
      c i * (t i).2 + (if c i = 0 then (p i).2.1 else 0) = (p i).2.1 := by
    by_cases hi : c i = 0
    · simp [hi]
    · simp [t, hi]
  have hbase : (∑ i, c i • tag i (t i)) ∈ TaggedHull T := by
    apply mem_convexHull_of_exists_fintype c (fun i => tag i (t i))
      (fun i => (hp i).2.1) hsum
    · intro i
      exact Set.mem_iUnion.mpr ⟨i, t i, ht i, rfl⟩
    · rfl
  have hfinal := tagged_upward T hup hbase hδ
  have heq : (∑ i, c i • tag i (t i)) + (0, δ, 0) =
      (∑ i, (p i).1, ∑ i, (p i).2.1, fun i => (p i).2.2) := by
    rw [sum_tags]
    apply Prod.ext
    · change (∑ i, c i • (t i).1) + 0 = _
      rw [add_zero]
      exact Finset.sum_congr rfl fun i _ => hvec i
    · apply Prod.ext
      · change (∑ i, c i * (t i).2) + δ = _
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hheight i
      · exact add_zero c
  rw [heq] at hfinal
  exact hfinal

theorem tagged_closed [ProperSpace W] (T : Fin k → Set (W × ℝ))
    (hne : ∀ i, (T i).Nonempty) (hc : ∀ i, Convex ℝ (T i))
    (hcl : ∀ i, IsClosed (T i))
    (hbound : ∀ i u, u ∈ T i → ‖u.1‖ ^ 2 ≤ u.2)
    (hup : ∀ i u, u ∈ T i → ∀ t, 0 ≤ t → (u.1, u.2 + t) ∈ T i) :
    IsClosed (TaggedHull T) := by
  have heq : TaggedHull T = SumPerspectives T :=
    Set.Subset.antisymm (tagged_subset_sum T hne hc hbound) (sum_subset_tagged T hne hup)
  rw [heq]
  exact ClosedFiber.isClosed_sum_image (fun i => Perspective (T i))
    (fun i => perspective_closed (hcl i)) (fun i p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)


noncomputable def repack {n q k : ℕ} : Ambient n (q + 1) k ≃ₗ[ℝ]
    ((Pt n × (Fin q → ℝ)) × ℝ × (Fin k → ℝ)) where
  toFun v := ((v.1, Fin.init v.2.1), v.2.1 (Fin.last q), v.2.2)
  invFun v := (v.1.1, Fin.snoc v.1.2 v.2.1, v.2.2)
  left_inv := by intro v; simp only [Fin.snoc_init_self]
  right_inv := by intro v; simp only [Fin.init_snoc, Fin.snoc_last]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem repack_hull {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ))) :
    repack '' liftedHull St = TaggedHull (fun i => BinaryLift.QuadraticEpigraph (St i)) := by
  change (@repack n q k).toLinearMap '' convexHull ℝ _ = convexHull ℝ _
  rw [LinearMap.image_convexHull]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, w, hw, h, hh, rfl⟩ := Set.mem_iUnion.mp hu
    refine Set.mem_iUnion.mpr ⟨i, (w, h), ⟨hw, hh⟩, ?_⟩
    change (w, h, (Pi.single i 1 : Fin k → ℝ)) =
      ((w.1, Fin.init (Fin.snoc w.2 h : Fin (q + 1) → ℝ)),
        (Fin.snoc w.2 h : Fin (q + 1) → ℝ) (Fin.last q), (Pi.single i 1 : Fin k → ℝ))
    simp
  · intro hv
    obtain ⟨i, u, hu, rfl⟩ := Set.mem_iUnion.mp hv
    refine ⟨(u.1.1, Fin.snoc u.1.2 u.2, Pi.single i 1), ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨i, u.1, hu.1, u.2, hu.2, rfl⟩
    · change ((u.1.1, Fin.init (Fin.snoc u.1.2 u.2 : Fin (q + 1) → ℝ)),
          (Fin.snoc u.1.2 u.2 : Fin (q + 1) → ℝ) (Fin.last q),
            (Pi.single i 1 : Fin k → ℝ)) = (u.1, u.2, (Pi.single i 1 : Fin k → ℝ))
      simp

theorem liftedHull_isClosed {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    (hSt : ∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i)) :
    IsClosed (liftedHull St) := by
  have hcl : IsClosed (TaggedHull (fun i => BinaryLift.QuadraticEpigraph (St i))) :=
    tagged_closed (fun i => BinaryLift.QuadraticEpigraph (St i))
      (fun i => BinaryLift.quadraticEpigraph_nonempty (St i) (hSt i).1)
      (fun i => BinaryLift.quadraticEpigraph_convex (St i) (hSt i).2.2)
      (fun i => BinaryLift.quadraticEpigraph_isClosed (St i) (hSt i).2.1)
      (fun i _ hu => BinaryLift.quadraticEpigraph_norm_sq_le (St i) hu)
      (fun i _ hu _ ht => BinaryLift.quadraticEpigraph_upward (St i) hu ht)
  rw [← repack_hull St] at hcl
  have hcont : Continuous (@repack n q k) := by
    change Continuous fun v : Ambient n (q + 1) k =>
      ((v.1, Fin.init v.2.1), v.2.1 (Fin.last q), v.2.2)
    fun_prop
  simpa only [Set.preimage_image_eq _ repack.injective] using hcl.preimage hcont

end MICPRep.Periodic.QuadraticClosed

/- Complete task-local helper proof bodies from BinaryPart.lean. -/

namespace MICPRep.Periodic.BinaryLift

theorem binary_finite {n : ℕ} (S : Set (Pt n)) (hS : IsBinaryMICPR S) :
    ∃ (q k : ℕ) (St : Fin k → Set (Pt n × (Fin q → ℝ))),
      (∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i)) ∧
      S = ⋃ i, Prod.fst '' St i := by
  classical
  obtain ⟨p, d, M, hM, hbin⟩ := hS
  let z : (Fin d → Bool) → Fin d → ℝ := fun b i => if b i then 1 else 0
  let A : (Fin d → Bool) → Set (Pt n × (Fin p → ℝ)) :=
    fun b => {w | (w.1, w.2, z b) ∈ M}
  let J := {b : Fin d → Bool // (A b).Nonempty}
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨p, Fintype.card J, fun i => A (e.symm i).val, ?_, ?_⟩
  · intro i
    refine ⟨(e.symm i).property, hM.1.preimage (by fun_prop), ?_⟩
    intro w hw w' hw' a b ha hb hab
    have hm := hM.2.1 hw hw' ha hb hab
    change (a • w.1 + b • w'.1, a • w.2 + b • w'.2, z (e.symm i).val) ∈ M
    simpa only [Prod.smul_mk, Prod.mk_add_mk,
      ← add_smul, hab, one_smul] using hm
  · ext x
    constructor
    · intro hx
      obtain ⟨y, zz, hzz, hm⟩ := (hM.2.2 x).mp hx
      let b : Fin d → Bool := fun i => decide (zz i = 1)
      have hz : z b = zz := by
        funext i
        have hzi : zz i = 0 ∨ zz i = 1 := hbin (x, y, zz) hm hzz i
        rcases hzi with hi | hi <;> simp [z, b, hi]
      have hb : (A b).Nonempty := ⟨(x, y), by simpa [A, hz] using hm⟩
      refine Set.mem_iUnion.mpr ⟨e ⟨b, hb⟩, ?_⟩
      refine ⟨(x, y), ?_, rfl⟩
      simpa only [Equiv.symm_apply_apply] using (show (x, y) ∈ A b from by simpa [A, hz] using hm)
    · intro hx
      obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.mp hx
      apply (hM.2.2 w.1).mpr
      refine ⟨w.2, z (e.symm i).val, ?_, hw⟩
      refine ⟨fun j => if (e.symm i).val j then (1 : ℤ) else 0, ?_⟩
      funext j
      simp [z]

theorem hull_simplex {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    {v : Ambient n (q + 1) k} (hv : v ∈ liftedHull St) :
    (∀ i, 0 ≤ v.2.2 i ∧ v.2.2 i ≤ 1) ∧ ∑ i, v.2.2 i = 1 := by
  classical
  apply convexHull_min (t := {v : Ambient n (q + 1) k |
      (∀ i, 0 ≤ v.2.2 i ∧ v.2.2 i ≤ 1) ∧ ∑ i, v.2.2 i = 1}) ?_ ?_ hv
  · intro v hv
    obtain ⟨i, w, hw, w₀, hw₀, rfl⟩ := Set.mem_iUnion.mp hv
    constructor
    · intro j
      by_cases hji : j = i <;> simp [hji]
    · simp
  · intro v hv w hw a b ha hb hab
    constructor
    · intro i
      change 0 ≤ a * v.2.2 i + b * w.2.2 i ∧ a * v.2.2 i + b * w.2.2 i ≤ 1
      constructor
      · exact add_nonneg (mul_nonneg ha (hv.1 i).1) (mul_nonneg hb (hw.1 i).1)
      · nlinarith [(mul_le_mul_of_nonneg_left (hv.1 i).2 ha),
          (mul_le_mul_of_nonneg_left (hw.1 i).2 hb)]
    · change ∑ i, (a * v.2.2 i + b * w.2.2 i) = 1
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv.2, hw.2, mul_one, hab]

theorem hull_binary {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    {v : Ambient n (q + 1) k} (hv : v ∈ liftedHull St) (hz : v.2.2 ∈ intLattice k) :
    ∀ i : Fin k, v.2.2 i = 0 ∨ v.2.2 i = 1 := by
  obtain ⟨z, hz⟩ := hz
  intro i
  have hi := (hull_simplex St hv).1 i
  have he : (z i : ℝ) = v.2.2 i := congrFun hz i
  rw [← he] at hi ⊢
  have h0 : 0 ≤ z i := by exact_mod_cast hi.1
  have h1 : z i ≤ 1 := by exact_mod_cast hi.2
  have : z i = 0 ∨ z i = 1 := by omega
  rcases this with h | h <;> simp [h]

theorem hull_slice {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    (hSt : ∀ i, Convex ℝ (St i)) {v : Ambient n (q + 1) k}
    (hv : v ∈ liftedHull St) (i : Fin k) (hi : v.2.2 i = 1) :
    (v.1, fun j : Fin q => v.2.1 j.castSucc) ∈ St i := by
  classical
  have hmem : v ∈ {w : Ambient n (q + 1) k | w.2.2 i ≤ 1 ∧
      (w.2.2 i = 1 → (w.1, fun j : Fin q => w.2.1 j.castSucc) ∈ St i)} := by
    apply convexHull_min ?_ ?_ hv
    · intro w hw
      obtain ⟨j, u, hu, u₀, hu₀, rfl⟩ := Set.mem_iUnion.mp hw
      by_cases hji : j = i
      · subst j
        simpa using hu
      · simp [Ne.symm hji]
    · intro v hv w hw a b ha hb hab
      change a * v.2.2 i + b * w.2.2 i ≤ 1 ∧ _
      have hva := mul_le_mul_of_nonneg_left hv.1 ha
      have hwb := mul_le_mul_of_nonneg_left hw.1 hb
      refine ⟨by nlinarith, ?_⟩
      intro hsum
      change a * v.2.2 i + b * w.2.2 i = 1 at hsum
      by_cases ha0 : a = 0
      · subst a
        have hb1 : b = 1 := by linarith
        simpa [hb1] using hw.2 (by simpa [hb1] using hsum)
      by_cases hb0 : b = 0
      · subst b
        have ha1 : a = 1 := by linarith
        simpa [ha1] using hv.2 (by simpa [ha1] using hsum)
      have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hv1 : v.2.2 i = 1 := by nlinarith
      have hw1 : w.2.2 i = 1 := by nlinarith
      exact hSt i (hv.2 hv1) (hw.2 hw1) ha hb hab
  exact hmem.2 hi

theorem hull_integer_projection {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    (hSt : ∀ i, Convex ℝ (St i)) {v : Ambient n (q + 1) k}
    (hv : v ∈ liftedHull St) (hz : v.2.2 ∈ intLattice k) :
    v.1 ∈ ⋃ i, Prod.fst '' St i := by
  classical
  have hi : ∃ i : Fin k, v.2.2 i = 1 := by
    by_contra! h
    have he : ∀ i, v.2.2 i = 0 := fun i => (hull_binary St hv hz i).resolve_right (h i)
    have hs := (hull_simplex St hv).2
    simp [he] at hs
  obtain ⟨i, hi⟩ := hi
  exact Set.mem_iUnion.mpr ⟨i, _, hull_slice St hSt hv i hi, rfl⟩

theorem lift_point {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    {x : Pt n} (hx : x ∈ ⋃ i, Prod.fst '' St i) :
    ∃ y : Fin (q + 1) → ℝ, ∃ z ∈ intLattice k, (x, y, z) ∈ liftedHull St := by
  classical
  obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.mp hx
  refine ⟨Fin.snoc w.2 (‖w.1‖ ^ 2 + ∑ j, (w.2 j) ^ 2), Pi.single i 1, ?_, ?_⟩
  · refine ⟨Pi.single i 1, ?_⟩
    funext j
    by_cases hji : j = i <;> simp [hji]
  · apply subset_convexHull
    exact Set.mem_iUnion.mpr ⟨i, w, hw, _, le_rfl, rfl⟩

theorem hull_induces {n q k : ℕ} (S : Set (Pt n))
    (St : Fin k → Set (Pt n × (Fin q → ℝ)))
    (hSt : ∀ i, Convex ℝ (St i)) (hclosed : IsClosed (liftedHull St))
    (hS : S = ⋃ i, Prod.fst '' St i) : Induces (liftedHull St) S := by
  refine ⟨hclosed, convex_convexHull ℝ _, ?_⟩
  intro x
  rw [hS]
  constructor
  · exact lift_point St
  · rintro ⟨y, z, hz, hv⟩
    exact hull_integer_projection St hSt hv hz

end MICPRep.Periodic.BinaryLift

open MICPRep.Periodic
open scoped ENNReal Matrix

theorem solution {n : ℕ} (S : Set (Pt n)) :
    (IsBinaryMICPR S ↔
      ∃ (q k : ℕ) (St : Fin k → Set (Pt n × (Fin q → ℝ))),
        (∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i)) ∧
        S = ⋃ i, Prod.fst '' St i) ∧
    ∀ (q k : ℕ) (St : Fin k → Set (Pt n × (Fin q → ℝ))),
      (∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i)) →
      S = ⋃ i, Prod.fst '' St i →
      Induces (liftedHull St) S ∧
        ∀ v ∈ liftedHull St, v.2.2 ∈ intLattice k → ∀ i : Fin k, v.2.2 i = 0 ∨ v.2.2 i = 1 := by
  have hbuild (q k : ℕ) (St : Fin k → Set (Pt n × (Fin q → ℝ)))
      (hSt : ∀ i, (St i).Nonempty ∧ IsClosed (St i) ∧ Convex ℝ (St i))
      (hS : S = ⋃ i, Prod.fst '' St i) :
      Induces (liftedHull St) S ∧
        ∀ v ∈ liftedHull St, v.2.2 ∈ intLattice k → ∀ i : Fin k, v.2.2 i = 0 ∨ v.2.2 i = 1 := by
    exact ⟨BinaryLift.hull_induces S St (fun i => (hSt i).2.2)
      (QuadraticClosed.liftedHull_isClosed St hSt) hS,
      fun v hv hz => BinaryLift.hull_binary St hv hz⟩
  refine ⟨⟨BinaryLift.binary_finite S, ?_⟩, hbuild⟩
  rintro ⟨q, k, St, hSt, hS⟩
  obtain ⟨hi, hb⟩ := hbuild q k St hSt hS
  exact ⟨q + 1, k, liftedHull St, hi, hb⟩
