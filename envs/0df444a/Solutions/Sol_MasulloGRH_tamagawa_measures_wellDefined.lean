-- Prove2me | solution 1 for MasulloGRH.tamagawa_measures_wellDefined
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:32:13.045586+00:00
-- url     : https://prove2.me/submissions/aebe3ece-f48b-4540-90c4-59fad251bd7d

import Definitions.Def_MasulloGRH_ZetaIntegrals
import Theorems.Thm_MasulloGRH_idele_group_topology
import Theorems.Thm_MasulloGRH_idele_class_group_topology
import Theorems.Thm_MasulloGRH_idele_class_group_norm_one_compact

/-!
# Lifting a measure from a quotient by a countable discrete subgroup

`G` is a commutative topological group, `Γ` a countable discrete subgroup, `G ⧸ Γ` is σ-compact.
We build a Borel section of `G → G ⧸ Γ`, the measure `can σ ν` on `G` which gives to every Borel set
on which the projection is injective the `ν`-measure of its image, and prove:

* `can_apply_of_injOn`, `eq_can`: this property characterises the measure;
* `can_isHaarMeasure`: it is a Haar measure if `ν` is;
* `lintegral_can`, `integral_can`: the unfolding formula.

No second countability is used.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace TZMeas

section Abstract

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

/-- a Borel section of the quotient map with Borel range -/
structure Sec where
  s : G ⧸ Γ → G
  mk_s : ∀ x, (QuotientGroup.mk (s x) : G ⧸ Γ) = x
  meas : Measurable s
  meas_range : MeasurableSet (range s)

omit [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] in
/-- a neighbourhood of `1` all of whose translates inject into the quotient -/
lemma exists_inj_nhd [DiscreteTopology Γ] : ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
    ∀ g a b : G, a ∈ W → b ∈ W →
      (QuotientGroup.mk (g * a) : G ⧸ Γ) = QuotientGroup.mk (g * b) → a = b := by
  have h1 : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 h1
  have hO1 : (1 : G) ∈ O := by
    have : (1 : Γ) ∈ (Subtype.val ⁻¹' O : Set Γ) := by rw [hOe]; rfl
    exact this
  have hm : Continuous (fun p : G × G => p.1⁻¹ * p.2) := by fun_prop
  have hpre : IsOpen ((fun p : G × G => p.1⁻¹ * p.2) ⁻¹' O) := hO.preimage hm
  have hmem : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' O := by
    simpa using hO1
  obtain ⟨W₁, W₂, hW₁, hW₂, h1W₁, h1W₂, hsub⟩ := isOpen_prod_iff.1 hpre 1 1 hmem
  refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨h1W₁, h1W₂⟩, fun g a b ha hb hab => ?_⟩
  rw [QuotientGroup.eq] at hab
  have e : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
  rw [e] at hab
  have hO' : a⁻¹ * b ∈ O := hsub (Set.mk_mem_prod ha.1 hb.2)
  have : (⟨a⁻¹ * b, hab⟩ : Γ) ∈ (Subtype.val ⁻¹' O : Set Γ) := hO'
  rw [hOe] at this
  have h2 : a⁻¹ * b = 1 := congrArg Subtype.val this
  exact (inv_mul_eq_one.1 h2)

/-- a Borel section exists -/
theorem exists_sec [DiscreteTopology Γ] [SigmaCompactSpace (G ⧸ Γ)] : Nonempty (Sec Γ) := by
  classical
  obtain ⟨W, hWo, hW1, hWinj⟩ := exists_inj_nhd Γ
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have hπo : IsOpenMap π := QuotientGroup.isOpenMap_coe
  have hπc : Continuous π := continuous_quotient_mk'
  -- the open sets `U g = g W`
  let U : G → Set G := fun g => (fun w => g * w) '' W
  have hUo : ∀ g, IsOpen (U g) := fun g => (Homeomorph.mulLeft g).isOpenMap W hWo
  have hUinj : ∀ g, InjOn π (U g) := by
    rintro g _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hWinj g a b ha hb hab]
  have hUmem : ∀ g, g ∈ U g := fun g => ⟨1, hW1, mul_one g⟩
  obtain ⟨t, htc, htU⟩ := countable_cover_nhds_of_sigmaCompact
    (f := fun x : G ⧸ Γ => π '' U x.out)
    (fun x => (hπo _ (hUo _)).mem_nhds ⟨x.out, hUmem _, QuotientGroup.out_eq' x⟩)
  have htne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at htU
    simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at htU
    exact (Set.empty_ne_univ (α := G ⧸ Γ)) htU
  obtain ⟨e, he⟩ := htc.exists_eq_range htne
  let V : ℕ → Set G := fun i => U (e i).out
  let E : ℕ → Set (G ⧸ Γ) := fun i => π '' V i
  have hEo : ∀ i, IsOpen (E i) := fun i => hπo _ (hUo _)
  have hcov : ∀ x : G ⧸ Γ, ∃ i, x ∈ E i := by
    intro x
    have hx : x ∈ ⋃ y ∈ t, π '' U y.out := by rw [htU]; trivial
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
    rw [he] at hy
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, hxy⟩
  let n : G ⧸ Γ → ℕ := fun x => Nat.find (hcov x)
  have hn : ∀ x, x ∈ E (n x) := fun x => Nat.find_spec (hcov x)
  -- the index sets
  let Cs : ℕ → Set (G ⧸ Γ) := fun i => E i \ ⋃ j ∈ Finset.range i, E j
  have hCs : ∀ i, MeasurableSet (Cs i) := fun i =>
    (hEo i).measurableSet.diff
      (MeasurableSet.biUnion (Finset.countable_toSet _) fun j _ => (hEo j).measurableSet)
  have hnC : ∀ x i, n x = i ↔ x ∈ Cs i := by
    intro x i
    constructor
    · rintro rfl
      refine ⟨hn x, ?_⟩
      simp only [mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and]
      intro j hj
      exact Nat.find_min (hcov x) hj
    · rintro ⟨h1, h2⟩
      simp only [mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and] at h2
      refine le_antisymm (Nat.find_min' (hcov x) h1) ?_
      by_contra hlt
      exact h2 (n x) (not_le.1 hlt) (hn x)
  -- the section
  let s : G ⧸ Γ → G := fun x => (hn x).choose
  have hsV : ∀ x, s x ∈ V (n x) := fun x => (hn x).choose_spec.1
  have hsπ : ∀ x, π (s x) = x := fun x => (hn x).choose_spec.2
  have hkey : ∀ (O : Set G) (i : ℕ) (x : G ⧸ Γ), n x = i → (s x ∈ O ↔ x ∈ π '' (V i ∩ O)) := by
    intro O i x hi
    constructor
    · intro h
      exact ⟨s x, ⟨hi ▸ hsV x, h⟩, hsπ x⟩
    · rintro ⟨u, ⟨huV, huO⟩, hux⟩
      have : s x = u := hUinj _ (hi ▸ hsV x) huV ((hsπ x).trans hux.symm)
      rw [this]; exact huO
  have hmeas : Measurable s := by
    refine measurable_of_isOpen fun O hO => ?_
    have : s ⁻¹' O = ⋃ i, Cs i ∩ π '' (V i ∩ O) := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      constructor
      · intro h
        exact ⟨n x, (hnC x _).1 rfl, (hkey O _ x rfl).1 h⟩
      · rintro ⟨i, hi, hx⟩
        exact (hkey O i x ((hnC x i).2 hi)).2 hx
    rw [this]
    exact MeasurableSet.iUnion fun i =>
      (hCs i).inter (hπo _ ((hUo _).inter hO)).measurableSet
  have hrange : range s = ⋃ i, V i ∩ π ⁻¹' Cs i := by
    ext g
    simp only [mem_range, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨n x, hsV x, ?_⟩
      rw [hsπ x]; exact (hnC x _).1 rfl
    · rintro ⟨i, hgV, hgC⟩
      refine ⟨π g, ?_⟩
      have hi : n (π g) = i := (hnC _ _).2 hgC
      exact hUinj _ (hi ▸ hsV (π g)) hgV (hsπ _)
  refine ⟨⟨s, hsπ, hmeas, ?_⟩⟩
  rw [hrange]
  exact MeasurableSet.iUnion fun i => (hUo _).measurableSet.inter (hπc.measurable (hCs i))

variable {Γ}

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [BorelSpace (G ⧸ Γ)] in
lemma sec_fiber (σ : Sec Γ) (g : G) : ∃ γ : Γ, g = (γ : G) * σ.s (QuotientGroup.mk g) := by
  have h := σ.mk_s (QuotientGroup.mk g)
  rw [QuotientGroup.eq] at h
  exact ⟨⟨_, h⟩, by simp⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [BorelSpace (G ⧸ Γ)] in
lemma mk_mul_sec (σ : Sec Γ) (γ : Γ) (x : G ⧸ Γ) :
    (QuotientGroup.mk ((γ : G) * σ.s x) : G ⧸ Γ) = x := by
  rw [QuotientGroup.mk_mul, σ.mk_s, (QuotientGroup.eq_one_iff _).2 γ.2, one_mul]

/-- the measure on `G` attached to a measure on the quotient -/
noncomputable def can (σ : Sec Γ) (ν : Measure (G ⧸ Γ)) : Measure G :=
  Measure.sum (fun γ : Γ => (ν.map σ.s).map (fun g => (γ : G) * g))

lemma can_apply (σ : Sec Γ) (ν : Measure (G ⧸ Γ)) {A : Set G} (hA : MeasurableSet A) :
    can σ ν A = ∑' γ : Γ, ν {x | (γ : G) * σ.s x ∈ A} := by
  unfold can
  rw [Measure.sum_apply _ hA]
  refine tsum_congr fun γ => ?_
  rw [Measure.map_apply (continuous_const_mul _).measurable hA,
    Measure.map_apply σ.meas ((continuous_const_mul _).measurable hA)]
  rfl

/-- on a Borel set on which the projection is injective, the measure is that of the image -/
theorem can_apply_of_injOn [Countable Γ] (σ : Sec Γ) (ν : Measure (G ⧸ Γ)) {D : Set G}
    (hD : MeasurableSet D) (hinj : InjOn (QuotientGroup.mk : G → G ⧸ Γ) D) :
    MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) '' D) ∧
      can σ ν D = ν ((QuotientGroup.mk : G → G ⧸ Γ) '' D) := by
  have hT : ∀ γ : Γ, MeasurableSet {x | (γ : G) * σ.s x ∈ D} := fun γ =>
    σ.meas ((continuous_const_mul _).measurable hD)
  have hU : (QuotientGroup.mk : G → G ⧸ Γ) '' D = ⋃ γ : Γ, {x | (γ : G) * σ.s x ∈ D} := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨γ, hγ⟩ := sec_fiber σ g
      refine mem_iUnion.2 ⟨γ, ?_⟩
      change (γ : G) * σ.s (QuotientGroup.mk g) ∈ D
      rw [← hγ]; exact hg
    · intro hx
      obtain ⟨γ, hγ⟩ := mem_iUnion.1 hx
      exact ⟨_, hγ, mk_mul_sec σ γ x⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun γ : Γ => {x | (γ : G) * σ.s x ∈ D}) := by
    intro γ δ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    have := hinj hx hx' ((mk_mul_sec σ γ x).trans (mk_mul_sec σ δ x).symm)
    exact Subtype.ext (mul_right_cancel this)
  rw [hU]
  exact ⟨MeasurableSet.iUnion hT, by rw [can_apply σ ν hD, measure_iUnion hdisj hT]⟩

/-- the pieces `A ∩ γ · range s` -/
lemma pieces [Countable Γ] (σ : Sec Γ) {A : Set G} (hA : MeasurableSet A) :
    ∃ P : Γ → Set G, (∀ γ, MeasurableSet (P γ)) ∧
      (∀ γ, InjOn (QuotientGroup.mk : G → G ⧸ Γ) (P γ)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ A = ⋃ γ, P γ := by
  let P : Γ → Set G := fun γ => A ∩ (fun g => (γ : G)⁻¹ * g) ⁻¹' range σ.s
  have hmem : ∀ γ g, g ∈ P γ → ∃ x, g = (γ : G) * σ.s x := by
    rintro γ g ⟨-, x, hx⟩
    exact ⟨x, by rw [hx]; simp⟩
  refine ⟨P, fun γ => hA.inter ((continuous_const_mul _).measurable σ.meas_range), ?_, ?_, ?_⟩
  · intro γ g hg g' hg' h
    obtain ⟨x, rfl⟩ := hmem γ g hg
    obtain ⟨x', rfl⟩ := hmem γ g' hg'
    rw [mk_mul_sec, mk_mul_sec] at h
    rw [h]
  · intro γ δ hne
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    apply hne
    obtain ⟨x, hx⟩ := hmem γ g hg
    obtain ⟨x', hx'⟩ := hmem δ g hg'
    have e : x = x' := by
      have h1 := mk_mul_sec σ γ x
      have h2 := mk_mul_sec σ δ x'
      rw [← hx] at h1
      rw [← hx'] at h2
      exact h1.symm.trans h2
    subst e
    exact Subtype.ext (mul_right_cancel (hx.symm.trans hx'))
  · ext g
    simp only [mem_iUnion]
    constructor
    · intro hg
      obtain ⟨γ, hγ⟩ := sec_fiber σ g
      refine ⟨γ, hg, QuotientGroup.mk g, ?_⟩
      change σ.s _ = (γ : G)⁻¹ * g
      rw [eq_inv_mul_iff_mul_eq]; exact hγ.symm
    · rintro ⟨γ, hg, -⟩
      exact hg

/-- the property characterises the measure -/
theorem eq_can [Countable Γ] (σ : Sec Γ) (ν : Measure (G ⧸ Γ)) (μ : Measure G)
    (h : ∀ D : Set G, MeasurableSet D → InjOn (QuotientGroup.mk : G → G ⧸ Γ) D →
      μ D = ν ((QuotientGroup.mk : G → G ⧸ Γ) '' D)) :
    μ = can σ ν := by
  ext A hA
  obtain ⟨P, hP, hPinj, hPdisj, hPU⟩ := pieces σ hA
  rw [hPU, measure_iUnion hPdisj hP, measure_iUnion hPdisj hP]
  refine tsum_congr fun γ => ?_
  rw [h _ (hP γ) (hPinj γ), (can_apply_of_injOn σ ν (hP γ) (hPinj γ)).2]

omit [MeasurableSpace G] [BorelSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] in
lemma image_preimage_mul (h : G) (D : Set G) :
    (QuotientGroup.mk : G → G ⧸ Γ) '' ((fun g => h * g) ⁻¹' D) =
      (fun x : G ⧸ Γ => (QuotientGroup.mk h : G ⧸ Γ) * x) ⁻¹'
        ((QuotientGroup.mk : G → G ⧸ Γ) '' D) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨h * g, hg, by simp⟩
  · rintro ⟨d, hd, hdx⟩
    refine ⟨h⁻¹ * d, by simpa using hd, ?_⟩
    rw [QuotientGroup.mk_mul, hdx]
    simp

theorem can_isMulLeftInvariant [Countable Γ] (σ : Sec Γ) (ν : Measure (G ⧸ Γ))
    [ν.IsMulLeftInvariant] : (can σ ν).IsMulLeftInvariant := by
  refine ⟨fun h => ?_⟩
  apply eq_can σ ν
  intro D hD hinj
  have hm : Measurable (fun g : G => h * g) := (continuous_const_mul h).measurable
  rw [Measure.map_apply hm hD]
  have hinj' : InjOn (QuotientGroup.mk : G → G ⧸ Γ) ((fun g => h * g) ⁻¹' D) := by
    intro g hg g' hg' hgg
    have : h * g = h * g' := hinj hg hg' (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hgg])
    exact mul_left_cancel this
  rw [(can_apply_of_injOn σ ν (hm hD) hinj').2, image_preimage_mul, measure_preimage_mul]

theorem can_isFiniteMeasureOnCompacts [Countable Γ] [T2Space G] (σ : Sec Γ)
    (ν : Measure (G ⧸ Γ)) [IsFiniteMeasureOnCompacts ν]
    (hloc : ∀ g : G, ∃ V : Set G, IsOpen V ∧ g ∈ V ∧ InjOn (QuotientGroup.mk : G → G ⧸ Γ) V) :
    IsFiniteMeasureOnCompacts (can σ ν) := by
  refine ⟨fun K hK => ?_⟩
  choose V hVo hVm hVinj using hloc
  obtain ⟨t, htK⟩ := hK.elim_finite_subcover V hVo (fun g _ => mem_iUnion.2 ⟨g, hVm g⟩)
  have hsub : K ⊆ ⋃ g ∈ t, K ∩ V g := by
    intro k hk
    obtain ⟨g, hg, hkg⟩ := mem_iUnion₂.1 (htK hk)
    exact mem_iUnion₂.2 ⟨g, hg, hk, hkg⟩
  have hπK : ν ((QuotientGroup.mk : G → G ⧸ Γ) '' K) < ∞ :=
    (hK.image continuous_quotient_mk').measure_lt_top
  calc can σ ν K ≤ can σ ν (⋃ g ∈ t, K ∩ V g) := measure_mono hsub
    _ ≤ ∑ g ∈ t, can σ ν (K ∩ V g) := measure_biUnion_finset_le _ _
    _ ≤ ∑ g ∈ t, ν ((QuotientGroup.mk : G → G ⧸ Γ) '' K) := by
        refine Finset.sum_le_sum fun g _ => ?_
        rw [(can_apply_of_injOn σ ν (hK.measurableSet.inter (hVo g).measurableSet)
          ((hVinj g).mono inter_subset_right)).2]
        exact measure_mono (image_mono inter_subset_left)
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (by simp) hπK

theorem can_isOpenPosMeasure [Countable Γ] (σ : Sec Γ) (ν : Measure (G ⧸ Γ))
    [ν.IsOpenPosMeasure]
    (hloc : ∀ g : G, ∃ V : Set G, IsOpen V ∧ g ∈ V ∧ InjOn (QuotientGroup.mk : G → G ⧸ Γ) V) :
    (can σ ν).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨g, hg⟩ := hne
  obtain ⟨V, hVo, hgV, hVinj⟩ := hloc g
  have h1 : can σ ν (U ∩ V) ≠ 0 := by
    rw [(can_apply_of_injOn σ ν (hU.inter hVo).measurableSet (hVinj.mono inter_subset_right)).2]
    exact (QuotientGroup.isOpenMap_coe _ (hU.inter hVo)).measure_ne_zero ν ⟨_, ⟨g, ⟨hg, hgV⟩, rfl⟩⟩
  exact fun h0 => h1 (measure_mono_null inter_subset_left h0)

theorem can_isHaarMeasure [Countable Γ] [T2Space G] (σ : Sec Γ) (ν : Measure (G ⧸ Γ))
    [ν.IsHaarMeasure]
    (hloc : ∀ g : G, ∃ V : Set G, IsOpen V ∧ g ∈ V ∧ InjOn (QuotientGroup.mk : G → G ⧸ Γ) V) :
    (can σ ν).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := can_isFiniteMeasureOnCompacts σ ν hloc
    toIsMulLeftInvariant := can_isMulLeftInvariant σ ν
    toIsOpenPosMeasure := can_isOpenPosMeasure σ ν hloc }

/-- unfolding, for nonnegative functions -/
theorem lintegral_can [Countable Γ] (σ : Sec Γ) (ν : Measure (G ⧸ Γ)) {φ : G → ℝ≥0∞}
    (hφ : AEMeasurable φ (can σ ν)) :
    ∫⁻ g, φ g ∂(can σ ν) = ∫⁻ x, ∑' γ : Γ, φ ((γ : G) * σ.s x) ∂ν := by
  have hm : ∀ γ : Γ, Measurable (fun g : G => (γ : G) * g) := fun γ =>
    (continuous_const_mul _).measurable
  have hle : ∀ γ : Γ, (ν.map σ.s).map (fun g => (γ : G) * g) ≤ can σ ν := fun γ =>
    Measure.le_sum _ γ
  have h1 : ∀ γ : Γ, AEMeasurable φ ((ν.map σ.s).map (fun g => (γ : G) * g)) := fun γ =>
    hφ.mono_measure (hle γ)
  have h2 : ∀ γ : Γ, AEMeasurable (fun g => φ ((γ : G) * g)) (ν.map σ.s) := fun γ =>
    (h1 γ).comp_measurable (hm γ)
  have h3 : ∀ γ : Γ, AEMeasurable (fun x => φ ((γ : G) * σ.s x)) ν := fun γ =>
    (h2 γ).comp_measurable σ.meas
  rw [lintegral_tsum h3]
  unfold can
  rw [lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  rw [lintegral_map' (h1 γ) (hm γ).aemeasurable, lintegral_map' (h2 γ) σ.meas.aemeasurable]

/-- unfolding, for integrable functions -/
theorem integral_can [Countable Γ] (σ : Sec Γ) (ν : Measure (G ⧸ Γ)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {φ : G → E}
    (hφ : Integrable φ (can σ ν)) :
    ∫ g, φ g ∂(can σ ν) = ∫ x, ∑' γ : Γ, φ ((γ : G) * σ.s x) ∂ν := by
  have hm : ∀ γ : Γ, Measurable (fun g : G => (γ : G) * g) := fun γ =>
    (continuous_const_mul _).measurable
  have hle : ∀ γ : Γ, (ν.map σ.s).map (fun g => (γ : G) * g) ≤ can σ ν := fun γ =>
    Measure.le_sum _ γ
  have h1 : ∀ γ : Γ, AEStronglyMeasurable φ ((ν.map σ.s).map (fun g => (γ : G) * g)) := fun γ =>
    hφ.aestronglyMeasurable.mono_measure (hle γ)
  have h2 : ∀ γ : Γ, AEStronglyMeasurable (fun g => φ ((γ : G) * g)) (ν.map σ.s) := fun γ =>
    (h1 γ).comp_measurable (hm γ)
  have h3 : ∀ γ : Γ, AEStronglyMeasurable (fun x => φ ((γ : G) * σ.s x)) ν := fun γ =>
    (h2 γ).comp_measurable σ.meas
  have hfin : ∑' γ : Γ, ∫⁻ x, ‖φ ((γ : G) * σ.s x)‖ₑ ∂ν ≠ ∞ := by
    have := lintegral_can σ ν (φ := fun g => ‖φ g‖ₑ) hφ.aestronglyMeasurable.enorm
    rw [lintegral_tsum (fun γ => (h3 γ).enorm)] at this
    rw [← this]
    exact hφ.hasFiniteIntegral.ne
  rw [integral_tsum h3 hfin]
  have : ∫ g, φ g ∂(can σ ν) = ∑' γ : Γ, ∫ g, φ g ∂((ν.map σ.s).map (fun g => (γ : G) * g)) := by
    unfold can
    exact integral_sum_measure hφ
  rw [this]
  refine tsum_congr fun γ => ?_
  rw [integral_map (hm γ).aemeasurable (h1 γ), integral_map σ.meas.aemeasurable (h2 γ)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [BorelSpace (G ⧸ Γ)] in
/-- the fibre sum does not depend on the representative -/
lemma tsum_sec_eq (σ : Sec Γ) {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (φ : G → M)
    (g : G) :
    ∑' γ : Γ, φ ((γ : G) * σ.s (QuotientGroup.mk g)) = ∑' γ : Γ, φ ((γ : G) * g) := by
  obtain ⟨δ, hδ⟩ := sec_fiber σ g
  have : ∀ γ : Γ, φ ((γ : G) * g) = φ (((γ * δ : Γ) : G) * σ.s (QuotientGroup.mk g)) := by
    intro γ
    rw [Subgroup.coe_mul, mul_assoc, ← hδ]
  simp_rw [this]
  exact ((Equiv.mulRight δ).tsum_eq (fun γ : Γ => φ ((γ : G) * σ.s (QuotientGroup.mk g)))).symm

end Abstract

section Unique

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SigmaCompactSpace H] [MeasurableSpace H] [BorelSpace H]

/-- uniqueness of Haar measure on a σ-compact group, without regularity assumptions -/
theorem haar_eq_smul (μ' μ : Measure H) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ']
    [μ'.IsMulLeftInvariant] : μ' = Measure.haarScalarFactor μ' μ • μ := by
  ext A hA
  have hmono : Monotone (fun n => A ∩ compactCovering H n) := fun m n hmn =>
    inter_subset_inter_right _ (compactCovering_subset H hmn)
  have hU : A = ⋃ n, A ∩ compactCovering H n := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  have h1 := tendsto_measure_iUnion_atTop (μ := μ') hmono
  have h2 := tendsto_measure_iUnion_atTop (μ := Measure.haarScalarFactor μ' μ • μ) hmono
  have heq : ∀ n, μ' (A ∩ compactCovering H n) =
      (Measure.haarScalarFactor μ' μ • μ) (A ∩ compactCovering H n) := by
    intro n
    have hc : IsCompact (closure (A ∩ compactCovering H n)) :=
      (isCompact_compactCovering H n).closure_of_subset inter_subset_right
    exact Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ hc
  rw [← hU] at h1 h2
  simp only [Function.comp_def, heq] at h1
  exact tendsto_nhds_unique h1 h2

end Unique

end TZMeas

/-!
# The Tamagawa measures on `C_F` and on the ideles exist

Definition A.3.2.1 of the source defines the measures by properties; the formal definitions
`tamagawaIdeleClass`, `tamagawaIdele` pick a measure with these properties when one exists.
Here: they exist, with the unfolding formula, the push-forward under the norm and the invariance
under inversion.
-/


open MasulloGRH NumberField IsDedekindDomain MeasureTheory Set
open scoped ENNReal

namespace TZTam

variable (F : Type*) [Field F] [NumberField F]

instance instT2Idele : T2Space (IdeleGroup F) := (idele_group_topology F).1
instance instLCIdele : LocallyCompactSpace (IdeleGroup F) := (idele_group_topology F).2.1
instance instDiscPrincipal : DiscreteTopology (principalIdeles F) :=
  (idele_class_group_topology F).2.1
instance instT2Class : T2Space (IdeleClassGroup F) := (idele_class_group_topology F).2.2.1
instance instLCClass : LocallyCompactSpace (IdeleClassGroup F) :=
  (idele_class_group_topology F).2.2.2.1

lemma continuous_ideleNorm : Continuous (ideleNorm : IdeleGroup F → ℝ) :=
  (idele_group_topology F).2.2.2.1

variable {F}

lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h :=
  (idele_group_topology F).2.2.2.2.1 g h

lemma ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g :=
  (idele_group_topology F).2.2.2.2.2.1 g

lemma ideleNorm_principal (ξ : Fˣ) : ideleNorm (principalIdele F ξ) = 1 :=
  (idele_class_group_topology F).2.2.2.2.1 ξ

lemma ideleNorm_one : ideleNorm (1 : IdeleGroup F) = 1 := by
  have := ideleNorm_principal (F := F) 1
  rwa [map_one] at this

lemma ideleNorm_inv (g : IdeleGroup F) : ideleNorm g⁻¹ = (ideleNorm g)⁻¹ := by
  have h := ideleNorm_mul g g⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma norm_eq_of_mk_eq {a b : IdeleGroup F}
    (h : (QuotientGroup.mk a : IdeleClassGroup F) = QuotientGroup.mk b) :
    ideleNorm a = ideleNorm b := by
  rw [QuotientGroup.eq] at h
  obtain ⟨ξ, hξ⟩ := h
  have : b = a * principalIdele F ξ := by rw [hξ]; group
  rw [this, ideleNorm_mul, ideleNorm_principal, mul_one]

/-- the norm on idele classes -/
noncomputable def nb (x : IdeleClassGroup F) : ℝ := ideleNorm x.out

lemma nb_mk (g : IdeleGroup F) : nb (QuotientGroup.mk g : IdeleClassGroup F) = ideleNorm g :=
  norm_eq_of_mk_eq (QuotientGroup.out_eq' _)

lemma nb_pos (x : IdeleClassGroup F) : 0 < nb x := ideleNorm_pos _

lemma nb_mul (x y : IdeleClassGroup F) : nb (x * y) = nb x * nb y := by
  induction x using QuotientGroup.induction_on with | _ a => ?_
  induction y using QuotientGroup.induction_on with | _ b => ?_
  rw [← QuotientGroup.mk_mul, nb_mk, nb_mk, nb_mk, ideleNorm_mul]

lemma nb_one : nb (1 : IdeleClassGroup F) = 1 := by
  have : (1 : IdeleClassGroup F) = QuotientGroup.mk (1 : IdeleGroup F) := rfl
  rw [this, nb_mk, ideleNorm_one]

lemma nb_inv (x : IdeleClassGroup F) : nb x⁻¹ = (nb x)⁻¹ := by
  have h := nb_mul x x⁻¹
  rw [mul_inv_cancel, nb_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma continuous_nb : Continuous (nb : IdeleClassGroup F → ℝ) := by
  rw [(QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff]
  have : nb ∘ (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) = ideleNorm := by
    funext g; exact nb_mk g
  rw [this]; exact continuous_ideleNorm F

lemma nb_surj (t : ℝ) (ht : 0 < t) : ∃ x : IdeleClassGroup F, nb x = t := by
  obtain ⟨g, hg⟩ := (idele_class_group_topology F).2.2.2.2.2.1 t ht
  exact ⟨QuotientGroup.mk g, by rw [nb_mk, hg]⟩

lemma image_band (a b : ℝ) :
    (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' {g | a ≤ ideleNorm g ∧ ideleNorm g < b} =
      nb ⁻¹' Ico a b := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change nb (QuotientGroup.mk g) ∈ Ico a b
    rw [nb_mk]; exact hg
  · intro hx
    refine ⟨x.out, hx, QuotientGroup.out_eq' x⟩

/-- the bands `{a ≤ |x| ≤ b}` are compact -/
lemma isCompact_band (a b : ℝ) (ha : 0 < a) : IsCompact (nb (F := F) ⁻¹' Icc a b) := by
  obtain ⟨σ, hσc, hσm, hσn⟩ := (idele_class_group_topology F).2.2.2.2.2.2
  have hC1 := (idele_class_group_norm_one_compact F).1.2
  have hσnb : ∀ t : ℝ, 0 < t → nb (σ t) = t := by
    intro t ht
    obtain ⟨g, hg, hgn⟩ := hσn t ht
    rw [← hg, nb_mk, hgn]
  have hK : IsCompact (σ '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (hσc.mono fun t ht => lt_of_lt_of_le ha ht.1)
  have hprod := hC1.mul hK
  refine hprod.of_isClosed_subset (isClosed_Icc.preimage continuous_nb) ?_
  intro x hx
  have ht : 0 < nb x := nb_pos x
  refine ⟨x * (σ (nb x))⁻¹, ?_, σ (nb x), ⟨nb x, hx, rfl⟩, by simp⟩
  refine ⟨(x * (σ (nb x))⁻¹).out, ?_, QuotientGroup.out_eq' _⟩
  change nb (x * (σ (nb x))⁻¹) = 1
  rw [nb_mul, nb_inv, hσnb _ ht, mul_inv_cancel₀ ht.ne']

instance instSigmaCompactClass : SigmaCompactSpace (IdeleClassGroup F) := by
  refine ⟨⟨fun n : ℕ => nb ⁻¹' Icc (Real.exp (-(n : ℝ))) (Real.exp n), fun n =>
    isCompact_band _ _ (Real.exp_pos _), ?_⟩⟩
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_ge |Real.log (nb x)|
  have hp := nb_pos x
  refine ⟨n, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (Real.exp_pos _) hp, Real.log_exp]
    linarith [neg_abs_le (Real.log (nb x))]
  · rw [← Real.log_le_log_iff hp (Real.exp_pos _), Real.log_exp]
    linarith [le_abs_self (Real.log (nb x))]

instance instCountablePrincipal : Countable (principalIdeles F) := by
  haveI : Countable F := Function.Injective.countable (integralBasis F).equivFun.injective
  haveI : Countable Fˣ := Function.Injective.countable Units.val_injective
  exact (principalIdele F).rangeRestrict_surjective.countable

/-- the unit band `{1 ≤ |x| < e}` -/
lemma band_pos_fin (μ : Measure (IdeleClassGroup F)) [μ.IsHaarMeasure] :
    μ (nb ⁻¹' Ico 1 (Real.exp 1)) ≠ 0 ∧ μ (nb ⁻¹' Ico 1 (Real.exp 1)) ≠ ∞ := by
  constructor
  · have ho : IsOpen (nb (F := F) ⁻¹' Ioo 1 (Real.exp 1)) := isOpen_Ioo.preimage continuous_nb
    have hne : (nb (F := F) ⁻¹' Ioo 1 (Real.exp 1)).Nonempty := by
      obtain ⟨x, hx⟩ := nb_surj (F := F) (Real.exp (1 / 2)) (Real.exp_pos _)
      refine ⟨x, ?_⟩
      change nb x ∈ Ioo 1 (Real.exp 1)
      rw [hx]
      exact ⟨by rw [Real.one_lt_exp_iff]; norm_num, by rw [Real.exp_lt_exp]; norm_num⟩
    have := ho.measure_ne_zero μ hne
    exact fun h0 => this (measure_mono_null (preimage_mono Ioo_subset_Ico_self) h0)
  · have hc := isCompact_band (F := F) 1 (Real.exp 1) one_pos
    exact ((measure_mono (preimage_mono Ico_subset_Icc_self)).trans_lt hc.measure_lt_top).ne

lemma vol_pos : 0 < tamagawaClassVolume F := dedekindZeta_residue_pos F

/-- existence for the measure on `C_F` -/
lemma exists_class_measure : ∃ μ : Measure (IdeleClassGroup F), μ.IsHaarMeasure ∧
    μ ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
      ENNReal.ofReal (tamagawaClassVolume F) := by
  let μ₀ : Measure (IdeleClassGroup F) := Measure.haar
  obtain ⟨h0, htop⟩ := band_pos_fin (F := F) μ₀
  set c : ℝ≥0∞ := ENNReal.ofReal (tamagawaClassVolume F) / μ₀ (nb ⁻¹' Ico 1 (Real.exp 1))
  have hc0 : c ≠ 0 := by
    simp only [c, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨by simpa using vol_pos (F := F), htop⟩
  have hctop : c ≠ ∞ := by
    simp only [c]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top h0
  refine ⟨c • μ₀, Measure.IsHaarMeasure.smul μ₀ hc0 hctop, ?_⟩
  rw [image_band, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.div_mul_cancel h0 htop

lemma class_spec : (tamagawaIdeleClass F).IsHaarMeasure ∧
    tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
      ENNReal.ofReal (tamagawaClassVolume F) := by
  have h := exists_class_measure (F := F)
  have : tamagawaIdeleClass F = h.choose := by
    unfold tamagawaIdeleClass
    exact dif_pos h
  rw [this]
  exact h.choose_spec

instance instHaarClass : (tamagawaIdeleClass F).IsHaarMeasure := class_spec.1

lemma hloc (g : IdeleGroup F) : ∃ V : Set (IdeleGroup F), IsOpen V ∧ g ∈ V ∧
    InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) V := by
  obtain ⟨W, hWo, hW1, hWinj⟩ := TZMeas.exists_inj_nhd (principalIdeles F)
  refine ⟨(fun w => g * w) '' W, (Homeomorph.mulLeft g).isOpenMap W hWo, ⟨1, hW1, mul_one g⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  rw [hWinj g a b ha hb hab]

/-- a fixed Borel section -/
noncomputable def sec : TZMeas.Sec (principalIdeles F) :=
  (TZMeas.exists_sec (principalIdeles F)).some

lemma exists_idele_measure : ∃ μ : Measure (IdeleGroup F), μ.IsHaarMeasure ∧
    ∀ D : Set (IdeleGroup F), MeasurableSet D →
      Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
      μ D = tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D) :=
  ⟨TZMeas.can sec (tamagawaIdeleClass F), TZMeas.can_isHaarMeasure sec _ hloc,
    fun _ hD hinj => (TZMeas.can_apply_of_injOn sec _ hD hinj).2⟩

lemma idele_spec : (tamagawaIdele F).IsHaarMeasure ∧
    ∀ D : Set (IdeleGroup F), MeasurableSet D →
      Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
      tamagawaIdele F D =
        tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D) := by
  have h := exists_idele_measure (F := F)
  have : tamagawaIdele F = h.choose := by
    unfold tamagawaIdele
    exact dif_pos h
  rw [this]
  exact h.choose_spec

lemma idele_eq_can : tamagawaIdele F = TZMeas.can sec (tamagawaIdeleClass F) :=
  TZMeas.eq_can sec _ _ idele_spec.2

lemma nontrivial_adele : Nontrivial (AdeleRing (𝓞 F) F) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  obtain ⟨g, hg⟩ := (idele_class_group_topology F).2.2.2.2.2.1 2 two_pos
  have : g = 1 := Subsingleton.elim _ _
  rw [this, ideleNorm_one] at hg
  norm_num at hg

lemma principalIdele_injective : Function.Injective (principalIdele F) := by
  haveI := nontrivial_adele (F := F)
  intro a b h
  have h2 := congrArg (fun u : IdeleGroup F => (u : AdeleRing (𝓞 F) F)) h
  exact Units.ext ((algebraMap F (AdeleRing (𝓞 F) F)).injective h2)

/-- sums over the principal ideles are sums over `Fˣ` -/
lemma tsum_principal {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (φ : IdeleGroup F → M) (g : IdeleGroup F) :
    ∑' γ : principalIdeles F, φ ((γ : IdeleGroup F) * g) = ∑' ξ : Fˣ, φ (principalIdele F ξ * g) :=
  ((MonoidHom.ofInjective principalIdele_injective).tsum_eq
    (fun γ : principalIdeles F => φ ((γ : IdeleGroup F) * g))).symm

lemma tsum_sec (φ : IdeleGroup F → ℝ≥0∞) (x : IdeleClassGroup F) :
    ∑' γ : principalIdeles F, φ ((γ : IdeleGroup F) * (sec (F := F)).s x) =
      ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out) := by
  have h := TZMeas.tsum_sec_eq (sec (F := F)) φ x.out
  rw [QuotientGroup.out_eq'] at h
  rw [h, tsum_principal]

lemma tsum_sec' (φ : IdeleGroup F → ℂ) (x : IdeleClassGroup F) :
    ∑' γ : principalIdeles F, φ ((γ : IdeleGroup F) * (sec (F := F)).s x) =
      ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out) := by
  have h := TZMeas.tsum_sec_eq (sec (F := F)) φ x.out
  rw [QuotientGroup.out_eq'] at h
  rw [h, tsum_principal]

/-- unfolding for nonnegative functions -/
theorem lintegral_unfold (φ : IdeleGroup F → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(tamagawaIdele F) =
      ∫⁻ x : IdeleClassGroup F, ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out) ∂(tamagawaIdeleClass F) := by
  rw [idele_eq_can, TZMeas.lintegral_can _ _ hφ.aemeasurable]
  exact lintegral_congr fun x => tsum_sec φ x

/-- unfolding for integrable functions -/
theorem integral_unfold (φ : IdeleGroup F → ℂ) (hφ : Integrable φ (tamagawaIdele F)) :
    ∫ g, φ g ∂(tamagawaIdele F) =
      ∫ x : IdeleClassGroup F, ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out) ∂(tamagawaIdeleClass F) := by
  rw [idele_eq_can] at hφ ⊢
  rw [TZMeas.integral_can _ _ hφ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => tsum_sec' φ x)

/-- the logarithm of the norm -/
noncomputable def lg (x : IdeleClassGroup F) : ℝ := Real.log (nb x)

lemma continuous_lg : Continuous (lg : IdeleClassGroup F → ℝ) :=
  continuous_nb.log (fun x => (nb_pos x).ne')

lemma lg_mul (x y : IdeleClassGroup F) : lg (x * y) = lg x + lg y := by
  unfold lg
  rw [nb_mul, Real.log_mul (nb_pos x).ne' (nb_pos y).ne']

lemma lg_surj (a : ℝ) : ∃ y : IdeleClassGroup F, lg y = a := by
  obtain ⟨y, hy⟩ := nb_surj (F := F) (Real.exp a) (Real.exp_pos a)
  exact ⟨y, by unfold lg; rw [hy, Real.log_exp]⟩

lemma lg_preimage_Icc (a b : ℝ) :
    (lg : IdeleClassGroup F → ℝ) ⁻¹' Icc a b = nb ⁻¹' Icc (Real.exp a) (Real.exp b) := by
  ext x
  have hp := nb_pos x
  simp only [mem_preimage, mem_Icc, lg]
  rw [Real.le_log_iff_exp_le hp, Real.log_le_iff_le_exp hp]

lemma lg_preimage_Ico (a b : ℝ) :
    (lg : IdeleClassGroup F → ℝ) ⁻¹' Ico a b = nb ⁻¹' Ico (Real.exp a) (Real.exp b) := by
  ext x
  have hp := nb_pos x
  simp only [mem_preimage, mem_Ico, lg]
  rw [Real.le_log_iff_exp_le hp, Real.log_lt_iff_lt_exp hp]

/-- the push-forward of the Tamagawa measure of `C_F` under `log |x|` is `μ₁(C_F^1) · dx` -/
theorem map_lg : Measure.map (lg : IdeleClassGroup F → ℝ) (tamagawaIdeleClass F) =
    ENNReal.ofReal (tamagawaClassVolume F) • volume := by
  set ν := Measure.map (lg : IdeleClassGroup F → ℝ) (tamagawaIdeleClass F) with hν
  have hm : Measurable (lg : IdeleClassGroup F → ℝ) := continuous_lg.measurable
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun a => ?_⟩
    obtain ⟨y, hy⟩ := lg_surj (F := F) a
    rw [hν, Measure.map_map (measurable_const_add a) hm]
    have : (fun x => a + x) ∘ (lg : IdeleClassGroup F → ℝ) = lg ∘ (fun x => y * x) := by
      funext x
      simp only [Function.comp_apply, lg_mul, hy]
    rw [this, ← Measure.map_map hm (measurable_const_mul y), map_mul_left_eq_self]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    have hsub : K ⊆ Icc (-R) R := fun k hk => by
      have := hR hk
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at this
      exact this
    rw [hν, Measure.map_apply hm hK.measurableSet]
    refine (measure_mono (preimage_mono hsub)).trans_lt ?_
    rw [lg_preimage_Icc]
    exact (isCompact_band _ _ (Real.exp_pos _)).measure_lt_top
  have h1 := Measure.addHaarMeasure_unique ν TopologicalSpace.PositiveCompacts.Icc01
  rw [addHaarMeasure_eq_volume] at h1
  have h2 : ν (Ico 0 1) = ENNReal.ofReal (tamagawaClassVolume F) := by
    rw [hν, Measure.map_apply hm measurableSet_Ico, lg_preimage_Ico, Real.exp_zero, ← image_band]
    exact class_spec.2
  have h3 : ν (Ico 0 1) = ν TopologicalSpace.PositiveCompacts.Icc01 := by
    conv_lhs => rw [h1]
    rw [Measure.smul_apply, Real.volume_Ico, smul_eq_mul]
    simp
  rw [h1, ← h3, h2]

omit [NumberField F] [Field F] in
lemma aux_inv {H : Type*} [CommGroup H] (x y : H) : y * x⁻¹ = (y⁻¹ * x)⁻¹ := by
  rw [mul_inv_rev, inv_inv, mul_comm]

/-- the Tamagawa measure of `C_F` is invariant under inversion -/
theorem map_inv : Measure.map (fun x : IdeleClassGroup F => x⁻¹) (tamagawaIdeleClass F) =
    tamagawaIdeleClass F := by
  have hmi : Measurable (fun x : IdeleClassGroup F => x⁻¹) := continuous_inv.measurable
  set ν := Measure.map (fun x : IdeleClassGroup F => x⁻¹) (tamagawaIdeleClass F) with hν
  have hνapp : ∀ K : Set (IdeleClassGroup F), MeasurableSet K →
      ν K = tamagawaIdeleClass F K⁻¹ := by
    intro K hK
    rw [hν, Measure.map_apply hmi hK]
    rfl
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [hνapp K hK.measurableSet]
    exact hK.inv.measure_lt_top
  haveI : ν.IsMulLeftInvariant := by
    refine ⟨fun y => ?_⟩
    rw [hν, Measure.map_map (measurable_const_mul y) hmi]
    have : (fun x => y * x) ∘ (fun x : IdeleClassGroup F => x⁻¹) =
        (fun x : IdeleClassGroup F => x⁻¹) ∘ (fun x => y⁻¹ * x) := by
      funext x
      exact aux_inv x y
    rw [this, ← Measure.map_map hmi (measurable_const_mul y⁻¹), map_mul_left_eq_self]
  have h1 := TZMeas.haar_eq_smul ν (tamagawaIdeleClass F)
  set S : Set (IdeleClassGroup F) := nb ⁻¹' Icc (Real.exp (-1)) (Real.exp 1) with hS
  have hSc : IsCompact S := isCompact_band _ _ (Real.exp_pos _)
  have hSinv : S⁻¹ = S := by
    ext x
    simp only [hS, Set.mem_inv, mem_preimage, mem_Icc, nb_inv]
    have hp := nb_pos x
    rw [Real.exp_neg]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(inv_le_comm₀ hp (Real.exp_pos 1)).1 h2, (inv_le_inv₀ (Real.exp_pos 1) hp).1 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(inv_le_inv₀ (Real.exp_pos 1) hp).2 h2, (inv_le_comm₀ hp (Real.exp_pos 1)).2 h1⟩
  have hSfin : tamagawaIdeleClass F S ≠ ∞ := hSc.measure_lt_top.ne
  have hSpos : tamagawaIdeleClass F S ≠ 0 := by
    have hsub : nb (F := F) ⁻¹' Ico 1 (Real.exp 1) ⊆ S := by
      intro x hx
      have he : Real.exp (-1) ≤ 1 :=
        (Real.exp_le_exp.2 (by norm_num : (-1 : ℝ) ≤ 0)).trans_eq Real.exp_zero
      exact ⟨he.trans hx.1, hx.2.le⟩
    exact fun h0 => (band_pos_fin (tamagawaIdeleClass F)).1 (measure_mono_null hsub h0)
  have h2 : ν S = tamagawaIdeleClass F S := by rw [hνapp S hSc.measurableSet, hSinv]
  have h3 : ν S = (Measure.haarScalarFactor ν (tamagawaIdeleClass F) : ℝ≥0∞) *
      tamagawaIdeleClass F S := by
    conv_lhs => rw [h1]
    rfl
  have h4 : (Measure.haarScalarFactor ν (tamagawaIdeleClass F) : ℝ≥0∞) = 1 := by
    rw [h2] at h3
    exact (ENNReal.mul_eq_right hSpos hSfin).1 h3.symm
  have h5 : Measure.haarScalarFactor ν (tamagawaIdeleClass F) = 1 := by exact_mod_cast h4
  rw [h1, h5, one_smul]

/-- uniqueness of the measure on `C_F` -/
theorem class_unique (μ' : Measure (IdeleClassGroup F)) [μ'.IsHaarMeasure]
    (h : μ' ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
      ENNReal.ofReal (tamagawaClassVolume F)) :
    μ' = tamagawaIdeleClass F := by
  have h1 := TZMeas.haar_eq_smul μ' (tamagawaIdeleClass F)
  have h2 := (class_spec (F := F)).2
  have h3 : μ' ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
      {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
      (Measure.haarScalarFactor μ' (tamagawaIdeleClass F) : ℝ≥0∞) *
        tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
          {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) := by
    conv_lhs => rw [h1]
    rfl
  rw [h, h2] at h3
  have hV0 : ENNReal.ofReal (tamagawaClassVolume F) ≠ 0 := by simpa using vol_pos (F := F)
  have h4 : (Measure.haarScalarFactor μ' (tamagawaIdeleClass F) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hV0 ENNReal.ofReal_ne_top).1 h3.symm
  have h5 : Measure.haarScalarFactor μ' (tamagawaIdeleClass F) = 1 := by exact_mod_cast h4
  rw [h1, h5, one_smul]

/-- uniqueness of the measure on the ideles -/
theorem idele_unique (μ' : Measure (IdeleGroup F))
    (h : ∀ D : Set (IdeleGroup F), MeasurableSet D →
      Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
      μ' D = tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D)) :
    μ' = tamagawaIdele F := by
  rw [idele_eq_can]
  exact TZMeas.eq_can sec _ _ h

end TZTam

theorem solution (F : Type*) [Field F] [NumberField F] :
    ((tamagawaIdeleClass F).IsHaarMeasure ∧
      tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
          {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
        ENNReal.ofReal (tamagawaClassVolume F) ∧
      ∀ μ' : Measure (IdeleClassGroup F), μ'.IsHaarMeasure →
        μ' ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
          {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
          ENNReal.ofReal (tamagawaClassVolume F) → μ' = tamagawaIdeleClass F) ∧
    ((tamagawaIdele F).IsHaarMeasure ∧
      (∀ D : Set (IdeleGroup F), MeasurableSet D →
        Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
        tamagawaIdele F D =
          tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D)) ∧
      ∀ μ' : Measure (IdeleGroup F),
        (∀ D : Set (IdeleGroup F), MeasurableSet D →
          Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
          μ' D =
            tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D)) →
        μ' = tamagawaIdele F) ∧
    (∀ φ : IdeleGroup F → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂(tamagawaIdele F) =
        ∫⁻ x : IdeleClassGroup F, ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out)
          ∂(tamagawaIdeleClass F)) ∧
    (∀ φ : IdeleGroup F → ℂ, Integrable φ (tamagawaIdele F) →
      ∫ g, φ g ∂(tamagawaIdele F) =
        ∫ x : IdeleClassGroup F, ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out)
          ∂(tamagawaIdeleClass F)) ∧
    Measure.map (fun x : IdeleClassGroup F => Real.log (ideleNorm x.out)) (tamagawaIdeleClass F) =
      ENNReal.ofReal (tamagawaClassVolume F) • (volume : Measure ℝ) ∧
    Measure.map (fun x : IdeleClassGroup F => x⁻¹) (tamagawaIdeleClass F) =
      tamagawaIdeleClass F := by
  refine ⟨⟨TZTam.class_spec.1, TZTam.class_spec.2, fun μ' hμ' h => ?_⟩,
    ⟨TZTam.idele_spec.1, TZTam.idele_spec.2, fun μ' h => TZTam.idele_unique μ' h⟩,
    fun φ hφ => TZTam.lintegral_unfold φ hφ, fun φ hφ => TZTam.integral_unfold φ hφ,
    TZTam.map_lg, TZTam.map_inv⟩
  haveI := hμ'
  exact TZTam.class_unique μ' h
