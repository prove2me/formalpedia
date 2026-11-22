-- Prove2me | solution 1 for MasulloGRH.dPrimeSequence_measure_maximal_compact
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:38:19.661186+00:00
-- url     : https://prove2.me/submissions/3e564713-94e1-48eb-993a-4c9557825c73

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The measure-theoretic maximal theorem along a D′-sequence (Masullo, Theorem A.5.3.5)

The argument follows the proof in the open formalization `mccorvie/riemann-masullo`
(`RiemannMasullo/AppA_AlgebraicNT/Sec5b.lean`, Apache-2.0), adapted to this Mathlib:

* `exists_disjoint_dSequence_translates`: the Vitali-type selection lemma (Theorem A.5.3.1);
* `ae_measure_smul_eq_zero_of_haar_null`: translates of a Haar-null Borel set are `ν`-null for
  Haar-almost every centre (Tonelli);
* `dSequenceMeasureMaximal_weak_null`: the weak type inequality for D-sequences that are only
  Haar-measurable (Theorem A.5.3.4(1));
* `dSequenceMeasureMaximal_weak_compact`: the compact form for D′-sequences (Theorem A.5.3.5).
-/

namespace Sol_MasulloGRH_dPrimeSequence_measure_maximal_compact

open Set
open scoped BigOperators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} {U : ℕ → Set G} {C : ℝ}

/-- Unbundled form of a D-sequence (without the structural constant). -/
def IsDSequence (μ : Measure G) (U : ℕ → Set G) : Prop :=
  (∀ k, 1 ∈ U k ∧ NullMeasurableSet (U k) μ ∧ 0 < μ (U k) ∧ μ (U k) < ∞) ∧
    Antitone U ∧
    ∃ C : ℝ, 0 < C ∧ ∀ k, 0 < μ (U k * (U k)⁻¹) ∧
      μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Theorem A.5.3.1, p. 578. If each point of the nonempty `μ`-measurable set `s` centers an
allowed translate and `μ (s * U 0) < ∞`, one can select finitely many pairwise disjoint allowed
translates centered in `s` whose total mass exceeds the mass of `s` divided by the structural
constant. -/
theorem exists_disjoint_dSequence_translates [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {F : Set (Set G)} (hF : F ⊆ {V | ∃ (x : G) (k : ℕ), V = x • U k})
    {s : Set G} (hs : NullMeasurableSet s μ) (hsne : s.Nonempty) (hsU : μ (s * U 0) < ∞)
    (hcover : ∀ x ∈ s, ∃ k, x • U k ∈ F) :
    ∃ (n : ℕ) (x : Fin n → G) (k : Fin n → ℕ),
      (∀ i, x i ∈ s ∧ x i • U (k i) ∈ F) ∧
      Pairwise (fun i j ↦ Disjoint (x i • U (k i)) (x j • U (k j))) ∧
      μ s / ENNReal.ofReal C < ∑ i, μ (U (k i)) := by
  classical
  let translate (a : G × ℕ) := a.1 • U a.2
  let t : Set (G × ℕ) := {a | a.1 ∈ s ∧ translate a ∈ F}
  -- The geometric spacing forces the selected index to be at most the candidate index.
  let priority (a : G × ℕ) : ℝ := (1 / 2) ^ a.2
  obtain ⟨u, hut, hud, hmatch⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement translate t priority (3 / 2)
      (by norm_num) (fun _ _ ↦ by dsimp [priority]; positivity) 1
      (fun _ _ ↦ pow_le_one₀ (by norm_num) (by norm_num))
      (fun a _ ↦ ⟨a.1, Set.mem_smul_set.mpr ⟨1, (hU.1 a.2).1, mul_one _⟩⟩)
  let enlarged (a : u) := a.val.1 • (U a.val.2 * (U a.val.2)⁻¹)
  have hcenters (x : G) (hx : x ∈ s) : ∃ a : u, x ∈ enlarged a := by
    obtain ⟨k, hk⟩ := hcover x hx
    obtain ⟨a, hau, ⟨z, hz₁, hz₂⟩, hpriority⟩ := hmatch (x, k) ⟨hx, hk⟩
    have ha : a.2 ≤ k := by
      by_contra! h
      have hpow : (1 / 2 : ℝ) ^ a.2 ≤ (1 / 2) ^ k * (1 / 2) := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
      change (1 / 2 : ℝ) ^ k ≤ (3 / 2) * (1 / 2) ^ a.2 at hpriority
      have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
      linarith
    obtain ⟨w, hwU, hw⟩ := Set.mem_smul_set.mp hz₁
    obtain ⟨v, hvU, hv⟩ := Set.mem_smul_set.mp hz₂
    change x * w = z at hw
    change a.1 * v = z at hv
    refine ⟨⟨a, hau⟩, Set.mem_smul_set.mpr ⟨v * w⁻¹, ?_, ?_⟩⟩
    · exact Set.mul_mem_mul hvU (Set.mem_inv.mpr (by simpa using hU.2.1 ha hwU))
    · change a.1 * (v * w⁻¹) = x
      rw [← mul_assoc, hv, ← hw, mul_assoc, mul_inv_cancel, mul_one]
  have hdisjoint : Pairwise (fun i j : u ↦ Disjoint (translate i) (translate j)) :=
    hud.on_injective Subtype.val_injective Subtype.property
  let mass (a : u) := μ (U a.val.2)
  have hmass : (∑' a : u, mass a) < ∞ := by
    calc
      (∑' a : u, mass a) = ∑' a : u, μ (translate a) := by
        simp only [mass, translate, measure_smul]
      _ ≤ μ (⋃ a : u, translate a) :=
        tsum_meas_le_meas_iUnion_of_disjoint₀ μ
          (fun a ↦ (hU.1 a.val.2).2.1.smul a.val.1)
          (fun _ _ hij ↦ (hdisjoint hij).aedisjoint)
      _ ≤ μ (s * U 0) := by
        apply measure_mono (iUnion_subset fun a ↦ ?_)
        rintro y ⟨w, hw, rfl⟩
        exact Set.mul_mem_mul (hut a.property).1 (hU.2.1 (Nat.zero_le _) hw)
      _ < ∞ := hsU
  -- Finite total mass and positive mass for every translate give countability.
  have : Countable u := by
    have hsupp : Function.support mass = univ :=
      Set.eq_univ_of_forall fun a ↦ (hU.1 a.val.2).2.2.1.ne'
    exact countable_univ_iff.mp (hsupp ▸ Summable.countable_support_ennreal hmass.ne)
  have hlt (a : u) : μ (enlarged a) < ENNReal.ofReal C * mass a := by
    simpa only [enlarged, mass, measure_smul] using hbound a.val.2
  have hscaled_fin : (∑' a : u, ENNReal.ofReal C * mass a) < ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass.ne).lt_top
  have hsum_fin : (∑' a : u, μ (enlarged a)) ≠ ∞ :=
    ((ENNReal.tsum_le_tsum fun a ↦ (hlt a).le).trans_lt hscaled_fin).ne
  obtain ⟨x₀, hx₀⟩ := hsne
  obtain ⟨a₀, _⟩ := hcenters x₀ hx₀
  have hstrict : μ s < ENNReal.ofReal C * ∑' a : u, mass a := by
    calc
      μ s ≤ μ (⋃ a : u, enlarged a) := measure_mono fun x hx ↦ mem_iUnion.mpr (hcenters x hx)
      _ ≤ ∑' a : u, μ (enlarged a) := measure_iUnion_le _
      _ < ∑' a : u, ENNReal.ofReal C * mass a :=
        ENNReal.tsum_lt_tsum hsum_fin (fun a ↦ (hlt a).le) (hlt a₀)
      _ = ENNReal.ofReal C * ∑' a : u, mass a := ENNReal.tsum_mul_left
  have hfinite : μ s / ENNReal.ofReal C < ∑' a : u, mass a :=
    (ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hC).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
      (by simpa only [mul_comm] using hstrict)
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hfinite
  obtain ⟨v, hv⟩ := hfinite
  let e := (Fintype.equivFin (↑v : Type _)).symm
  refine ⟨_, fun i ↦ (e i).val.val.1, fun i ↦ (e i).val.val.2,
    fun i ↦ hut (e i).val.property, fun i j hij ↦ ?_, ?_⟩
  · exact hdisjoint (Subtype.val_injective.ne (e.injective.ne hij))
  · change μ s / ENNReal.ofReal C < ∑ i, mass (e i).val
    rw [← Fintype.sum_equiv e.symm (fun a ↦ mass a.val) _ (by simp)]
    rwa [← Finset.sum_attach, Finset.attach_eq_univ] at hv

variable [SecondCountableTopology G]

/-- The limit superior of the masses of the translates under `ν`, normalized by the Haar
masses of the sequence members. -/
noncomputable def dSequenceMeasureMaximal (μ ν : Measure G) (U : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  limsup (fun k ↦ ν (x • U k) / μ (U k)) atTop



set_option linter.unusedSectionVars false in
/-- A tail of a D-sequence is a D-sequence. -/
lemma IsDSequence.tail {U : ℕ → Set G} (hU : IsDSequence μ U) (N : ℕ) :
    IsDSequence μ (fun k ↦ U (k + N)) := by
  refine ⟨fun k ↦ hU.1 (k + N), ?_, ?_⟩
  · intro a b hab
    exact hU.2.1 (by omega)
  · obtain ⟨C, hC, hdoub⟩ := hU.2.2
    exact ⟨C, hC, fun k ↦ hdoub (k + N)⟩

set_option linter.unusedSectionVars false in
/-- Translates of a Haar-null measurable set are `ν`-null for Haar-almost every center. -/
lemma ae_measure_smul_eq_zero_of_haar_null [μ.IsHaarMeasure] {ν : Measure G} [SigmaFinite ν]
    {Z : Set G} (hZ : MeasurableSet Z) (hZ0 : μ Z = 0) :
    ∀ᵐ x ∂μ, ν (x • Z) = 0 := by
  have hmeas : Measurable (fun x : G ↦ ν (x • Z)) := by
    have hmul : Measurable (fun x : G ↦ ν ((fun y ↦ y * x) ⁻¹' Z)) :=
      measurable_measure_mul_right ν hZ
    convert hmul.comp measurable_inv using 1
    ext x
    congr 1
    ext y
    simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_comm]
  have hint : ∫⁻ x, ν (x • Z) ∂μ = 0 := by
    have hfun (x : G) : ν (x • Z) = ∫⁻ y, Z.indicator (1 : G → ℝ≥0∞) (x⁻¹ * y) ∂ν := by
      rw [← lintegral_indicator_one (MeasurableSet.const_smul hZ x)]
      refine lintegral_congr fun y ↦ ?_
      by_cases hy : y ∈ x • Z
      · have hZmem : x⁻¹ * y ∈ Z := by
          rwa [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hy
        rw [Set.indicator_of_mem hZmem, Set.indicator_of_mem hy]
        rfl
      · have hZmem : x⁻¹ * y ∉ Z := fun h ↦ hy <| by
          rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
          exact h
        rw [Set.indicator_of_notMem hZmem, Set.indicator_of_notMem hy]
    simp_rw [hfun]
    have hf : AEMeasurable (Function.uncurry fun x y ↦
        Z.indicator (1 : G → ℝ≥0∞) (x⁻¹ * y)) (μ.prod ν) := by
      have hprod : Measurable (fun p : G × G ↦ Z.indicator (1 : G → ℝ≥0∞) (p.1⁻¹ * p.2)) :=
        (measurable_const.indicator hZ).comp (measurable_fst.inv.mul measurable_snd)
      exact hprod.aemeasurable.congr (Eventually.of_forall fun _ ↦ rfl)
    rw [lintegral_lintegral_swap hf]
    have hinner (y : G) : ∫⁻ x, Z.indicator (1 : G → ℝ≥0∞) (x⁻¹ * y) ∂μ = 0 := by
      have hset : {x | x⁻¹ * y ∈ Z} = y • Z⁻¹ := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, Set.mem_inv, mul_inv_rev, inv_inv]
          exact hx
        · intro hx
          rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, Set.mem_inv, mul_inv_rev, inv_inv] at hx
          exact hx
      have hind :
          (fun x ↦ Z.indicator (1 : G → ℝ≥0∞) (x⁻¹ * y)) = (y • Z⁻¹).indicator 1 := by
        funext x
        by_cases hx : x ∈ y • Z⁻¹
        · have hZmem : x⁻¹ * y ∈ Z := by
            have : x ∈ {x | x⁻¹ * y ∈ Z} := by rwa [hset]
            exact this
          rw [Set.indicator_of_mem hZmem, Set.indicator_of_mem hx]
          rfl
        · have hZmem : x⁻¹ * y ∉ Z := by
            intro hZmem
            apply hx
            have : x ∈ {x | x⁻¹ * y ∈ Z} := hZmem
            rwa [hset] at this
          rw [Set.indicator_of_notMem hZmem, Set.indicator_of_notMem hx]
      rw [hind, lintegral_indicator_one ((MeasurableSet.inv hZ).const_smul y), measure_smul,
        (measure_inv_null μ).2 hZ0]
    simp_rw [hinner, lintegral_zero]
  exact (lintegral_eq_zero_iff hmeas).1 hint

set_option linter.unusedSectionVars false in
/-- Around a compact subset of an open set there is a neighborhood `W` of the identity
with `K * W` still inside the open set. -/
lemma exists_mem_nhds_one_mul_subset {K V : Set G} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) : ∃ W ∈ 𝓝 (1 : G), K * W ⊆ V := by
  refine hK.induction_on ?empty ?mono ?union ?nhds
  · exact ⟨univ, Filter.univ_mem, by simp⟩
  · rintro s t hst ⟨W, hW, hWV⟩
    exact ⟨W, hW, (Set.mul_subset_mul hst Subset.rfl).trans hWV⟩
  · rintro s t ⟨W, hW, hWs⟩ ⟨R, hR, hRt⟩
    refine ⟨W ∩ R, inter_mem hW hR, ?_⟩
    rw [Set.union_mul]
    exact union_subset
      ((Set.mul_subset_mul_left Set.inter_subset_left).trans hWs)
      ((Set.mul_subset_mul_left Set.inter_subset_right).trans hRt)
  · intro x hx
    have hpre : (fun p : G × G ↦ p.1 * p.2) ⁻¹' V ∈ 𝓝 (x, 1) :=
      tendsto_mul (by simpa using hV.mem_nhds (hKV hx))
    rw [nhds_prod_eq, mem_prod_iff] at hpre
    obtain ⟨t, ht, W, hW, hTW⟩ := hpre
    rw [← image_subset_iff, image_mul_prod] at hTW
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, W, hW, hTW⟩

/-- Theorem A.5.3.4(1), p. 579, without a Borel hypothesis on the sequence.
The level set is null-measurable because translates of a Haar null-measurable set
agree almost everywhere with translates of a measurable hull, and the selected
Vitali centers can be taken outside the remaining null set so that `ν` sees them
as null-measurable. -/
theorem dSequenceMeasureMaximal_weak_null [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    {U : ℕ → Set G} (hU : IsDSequence μ U)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {B : Set G} (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ∞)
    {α : ℝ} (hα : 0 < α) :
    μ (B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}) ≤
      ENNReal.ofReal (C / α) *
        ν ((B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}) * U 0) := by
  classical
  set E := B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
  choose Bk hUBk hBkm hBkae using fun k ↦ (hU.1 k).2.1.exists_measurable_superset_ae_eq
  let Z : ℕ → Set G := fun k ↦ toMeasurable μ (Bk k \ U k)
  have hZmeas (k : ℕ) : MeasurableSet (Z k) := measurableSet_toMeasurable _ _
  have hZsub (k : ℕ) : Bk k \ U k ⊆ Z k := subset_toMeasurable _ _
  have hZ0 (k : ℕ) : μ (Z k) = 0 := by
    rw [measure_toMeasurable]
    exact (ae_eq_set.1 (hBkae k)).1
  have hgood : ∀ᵐ x ∂μ, ∀ k, ν (x • Z k) = 0 :=
    ae_all_iff.2 fun k ↦ ae_measure_smul_eq_zero_of_haar_null (hZmeas k) (hZ0 k)
  let good : Set G := {x | ∀ k, ν (x • Z k) = 0}
  have hgood0 : μ goodᶜ = 0 := ae_iff.mp hgood
  have hmeasB (k : ℕ) : Measurable (fun x : G ↦ ν (x • Bk k)) := by
    have hmul : Measurable (fun x : G ↦ ν ((fun y ↦ y * x) ⁻¹' Bk k)) :=
      measurable_measure_mul_right ν (hBkm k)
    convert hmul.comp measurable_inv using 1
    ext x
    congr 1
    ext y
    simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_comm]
  have hae_ratio : ∀ᵐ x ∂μ, ∀ k, ν (x • U k) = ν (x • Bk k) := by
    filter_upwards [hgood] with x hx k
    apply le_antisymm (measure_mono (smul_set_mono (hUBk k)))
    have hincl : x • Bk k ⊆ x • U k ∪ x • Z k := by
      intro y hy
      by_cases hyU : y ∈ x • U k
      · exact Or.inl hyU
      · obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.1 hy
        have hbU : b ∉ U k := by
          intro hbU
          exact hyU (Set.mem_smul_set.2 ⟨b, hbU, rfl⟩)
        exact Or.inr (Set.mem_smul_set.2 ⟨b, hZsub k ⟨hb, hbU⟩, rfl⟩)
    calc
      ν (x • Bk k) ≤ ν (x • U k ∪ x • Z k) := measure_mono hincl
      _ ≤ ν (x • U k) + ν (x • Z k) := measure_union_le _ _
      _ = ν (x • U k) := by simp [hx k]
  let MB : G → ℝ≥0∞ := fun x ↦ limsup (fun k ↦ ν (x • Bk k) / μ (U k)) atTop
  have hMB : Measurable MB := by
    apply Measurable.limsup
    intro k
    exact (hmeasB k).div_const _
  have haeM : (fun x ↦ dSequenceMeasureMaximal μ ν U x) =ᵐ[μ] MB := by
    filter_upwards [hae_ratio] with x hx
    simp only [dSequenceMeasureMaximal, MB]
    exact limsup_congr (Eventually.of_forall fun k ↦ by simp [hx k])
  have hlevel : NullMeasurableSet {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x} μ := by
    have hset :
        {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x} =ᵐ[μ]
          {x | ENNReal.ofReal α < MB x} := by
      filter_upwards [haeM] with x hx
      exact congrArg (fun t => ENNReal.ofReal α < t) hx
    exact ((measurableSet_lt measurable_const hMB).nullMeasurableSet.congr hset.symm)
  have hEm : NullMeasurableSet E μ := hB.inter hlevel
  have hgoodm : NullMeasurableSet good μ :=
    NullMeasurableSet.of_compl (NullMeasurableSet.of_null hgood0)
  let E' := E ∩ good
  have hE'm : NullMeasurableSet E' μ := hEm.inter hgoodm
  have hμE : μ E' = μ E := by
    apply le_antisymm (measure_mono inter_subset_left)
    calc
      μ E ≤ μ (E' ∪ goodᶜ) := by
        refine measure_mono fun x hx ↦ ?_
        by_cases hxg : x ∈ good
        · exact Or.inl ⟨hx, hxg⟩
        · exact Or.inr hxg
      _ ≤ μ E' + μ goodᶜ := measure_union_le _ _
      _ = μ E' := by simp [hgood0]
  obtain hE' | hE' := E'.eq_empty_or_nonempty
  · have : μ E = 0 := by simpa [hE', E'] using hμE.symm
    simp [E, this]
  let F : Set (Set G) :=
    {V | (∃ (x : G) (k : ℕ), V = x • U k) ∧ ENNReal.ofReal α * μ V < ν V}
  have hcover (x : G) (hx : x ∈ E') : ∃ k, x • U k ∈ F := by
    have hlevelx : ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x := hx.1.2
    obtain ⟨k, hk⟩ := (frequently_lt_of_lt_limsup (h := hlevelx)).exists
    refine ⟨k, ⟨⟨x, k, rfl⟩, ?_⟩⟩
    rw [measure_smul]
    exact lt_of_not_ge fun h ↦ hk.not_ge
      ((ENNReal.div_le_iff (hU.1 k).2.2.1.ne' (hU.1 k).2.2.2.ne).mpr
        (by simpa only [mul_comm] using h))
  have hE'sub : E' ⊆ B := fun _ hx ↦ hx.1.1
  obtain ⟨n, x, k, hx, hdisjoint, hmass⟩ :=
    exists_disjoint_dSequence_translates hU hC hbound (F := F) (fun _ hV ↦ hV.1) hE'm hE'
      ((measure_mono (Set.mul_subset_mul hE'sub Subset.rfl)).trans_lt hBU) hcover
  have hunion : (⋃ i, x i • U (k i)) ⊆ E' * U 0 := by
    refine iUnion_subset fun i ↦ ?_
    rintro y ⟨w, hw, rfl⟩
    exact Set.mul_mem_mul (hx i).1 (hU.2.1 (Nat.zero_le _) hw)
  have hnm (i : Fin n) : NullMeasurableSet (x i • U (k i)) ν := by
    have hxg : ∀ j, ν (x i • Z j) = 0 := hx i |>.1.2
    have hBmeas : MeasurableSet (x i • Bk (k i)) := (hBkm (k i)).const_smul (x i)
    have hdiff0 : ν (x i • Bk (k i) \ x i • U (k i)) = 0 := by
      refine measure_mono_null ?_ (hxg (k i))
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.1 hy.1
      have hbU : b ∉ U (k i) := by
        intro hbU
        exact hy.2 (Set.mem_smul_set.2 ⟨b, hbU, rfl⟩)
      exact Set.mem_smul_set.2 ⟨b, hZsub (k i) ⟨hb, hbU⟩, rfl⟩
    have hae : x i • U (k i) =ᵐ[ν] x i • Bk (k i) := by
      rw [ae_eq_set]
      refine ⟨?_, hdiff0⟩
      · have hempty : x i • U (k i) \ x i • Bk (k i) = ∅ := by
          rw [Set.sdiff_eq_empty]
          exact smul_set_mono (hUBk (k i))
        simp [hempty]
    exact hBmeas.nullMeasurableSet.congr hae.symm
  have hsum : ∑ i, ENNReal.ofReal α * μ (U (k i)) ≤ ν (E' * U 0) := by
    calc
      _ ≤ ∑ i, ν (x i • U (k i)) := Finset.sum_le_sum fun i _ ↦ by
        simpa only [measure_smul] using (hx i).2.2.le
      _ = ν (⋃ i, x i • U (k i)) := by
        rw [measure_iUnion₀ (fun i j hij ↦ (hdisjoint hij).aedisjoint) hnm, tsum_fintype]
      _ ≤ ν (E' * U 0) := measure_mono hunion
  have hE'le : μ E' ≤ ENNReal.ofReal (C / α) * ν (E' * U 0) := by
    calc
      μ E' ≤ ENNReal.ofReal C * ∑ i, μ (U (k i)) := by
        rw [mul_comm, ← ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top]
        exact hmass.le
      _ ≤ ENNReal.ofReal C * (ν (E' * U 0) / ENNReal.ofReal α) := by
        refine mul_le_mul' le_rfl ?_
        apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hα).ne')
          (Or.inl ENNReal.ofReal_ne_top)).mpr
        simpa only [mul_comm _ (ENNReal.ofReal α), Finset.mul_sum] using hsum
      _ = ENNReal.ofReal (C / α) * ν (E' * U 0) := by
        rw [ENNReal.ofReal_div_of_pos hα, ENNReal.div_eq_inv_mul, ← mul_assoc, div_eq_mul_inv]
  calc
    μ E = μ E' := hμE.symm
    _ ≤ ENNReal.ofReal (C / α) * ν (E' * U 0) := hE'le
    _ ≤ ENNReal.ofReal (C / α) * ν (E * U 0) :=
      mul_le_mul' le_rfl (measure_mono (Set.mul_subset_mul inter_subset_left Subset.rfl))

/-- Theorem A.5.3.5, p. 580. For a D′-sequence the weak bound on a compact set can use the
`ν`-mass of that compact set itself. -/
theorem dSequenceMeasureMaximal_weak_compact [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U ∧ ∀ W ∈ 𝓝 (1 : G), ∃ k, U k ⊆ W)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {K : Set G} (hK : IsCompact K) {α : ℝ} (hα : 0 < α) :
    μ (K ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}) ≤
      ENNReal.ofReal (C / α) * ν K := by
  classical
  set E := K ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
  let c := ENNReal.ofReal (C / α)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos hC hα)).ne'
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hcb ↦ ?_
  have hKfin : ν K < ∞ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have : c * ν K = ∞ := by simp [htop, ENNReal.mul_top, hc0]
    exact hcb.ne this
  have hηpos : 0 < (ε : ℝ) / (C / α) := div_pos (NNReal.coe_pos.mpr hε) (div_pos hC hα)
  let η : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / (C / α))
  have hη0 : η ≠ 0 := (ENNReal.ofReal_pos.mpr hηpos).ne'
  obtain ⟨V, hKV, hVopen, hVlt⟩ :=
    K.exists_isOpen_lt_of_lt (ν K + η) (ENNReal.lt_add_right hKfin.ne hη0)
  have hEV : μ E ≤ c * ν V := by
    obtain ⟨W, hWmem, hKW⟩ := exists_mem_nhds_one_mul_subset hK hVopen hKV
    obtain ⟨S, hScomp, hSmem⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨N, hN⟩ := hU.2 (W ∩ S) (inter_mem hWmem hSmem)
    have hUNS : U N ⊆ S := hN.trans inter_subset_right
    have hUNW : U N ⊆ W := hN.trans inter_subset_left
    have hfin : μ (K * U (0 + N)) < ∞ := by
      simpa [Nat.zero_add] using
        lt_of_le_of_lt (measure_mono (Set.mul_subset_mul Subset.rfl hUNS))
          (hK.mul hScomp).measure_lt_top
    have htail : IsDSequence μ (fun k ↦ U (k + N)) := hU.1.tail N
    have hM (x : G) :
        dSequenceMeasureMaximal μ ν (fun k ↦ U (k + N)) x =
          dSequenceMeasureMaximal μ ν U x := by
      unfold dSequenceMeasureMaximal
      rw [show (fun k ↦ ν (x • U (k + N)) / μ (U (k + N))) =
          (fun k ↦ ν (x • U k) / μ (U k)) ∘ (fun k ↦ k + N) by ext; rfl,
        limsup, limsup, ← map_map, map_add_atTop_eq_nat]
    have hweak := dSequenceMeasureMaximal_weak_null (ν := ν) (U := fun k ↦ U (k + N)) htail hC
      (fun k ↦ hbound (k + N)) (hK.isClosed.measurableSet.nullMeasurableSet (μ := μ)) hfin hα
    simp only [hM, Nat.zero_add] at hweak
    calc
      μ E ≤ c * ν (E * U N) := hweak
      _ ≤ c * ν (K * U N) :=
        mul_le_mul' le_rfl (measure_mono (Set.mul_subset_mul inter_subset_left Subset.rfl))
      _ ≤ c * ν V :=
        mul_le_mul' le_rfl (measure_mono ((Set.mul_subset_mul Subset.rfl hUNW).trans hKW))
  have hprod : c * η = (ε : ℝ≥0∞) := by
    calc
      c * η = ENNReal.ofReal (C / α) * ENNReal.ofReal ((ε : ℝ) / (C / α)) := rfl
      _ = ENNReal.ofReal ((C / α) * ((ε : ℝ) / (C / α))) :=
        (ENNReal.ofReal_mul (div_pos hC hα).le).symm
      _ = ENNReal.ofReal (ε : ℝ) := by
        congr 1
        rw [mul_comm]
        exact div_mul_cancel₀ (ε : ℝ) (div_pos hC hα).ne'
      _ = ε := ENNReal.ofReal_coe_nnreal
  calc
    μ E ≤ c * ν V := hEV
    _ ≤ c * (ν K + η) := mul_le_mul' le_rfl hVlt.le
    _ = c * ν K + c * η := by rw [mul_add]
    _ = c * ν K + ε := by rw [hprod]

end Sol_MasulloGRH_dPrimeSequence_measure_maximal_compact

open MasulloGRH in
theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (ν : Measure G) [ν.Regular] (K : Set G) (hK : IsCompact K) (α : ℝ) (hα : 0 < α) :
    μ (K ∩ {x | ENNReal.ofReal α < limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop}) ≤
      ENNReal.ofReal (C / α) * ν K := by
  have hD : Sol_MasulloGRH_dPrimeSequence_measure_maximal_compact.IsDSequence μ U :=
    ⟨fun k => ⟨hU.1.one_mem k, hU.1.nullMeasurable k, hU.1.measure_pos k, hU.1.measure_lt_top k⟩,
      antitone_nat_of_succ_le hU.1.antitone,
      ⟨C, hU.1.const_pos, hU.1.doubling⟩⟩
  exact Sol_MasulloGRH_dPrimeSequence_measure_maximal_compact.dSequenceMeasureMaximal_weak_compact
    (ν := ν) ⟨hD, hU.2⟩ hU.1.const_pos (fun k => (hU.1.doubling k).2) hK hα
