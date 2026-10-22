-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.of_local
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T14:23:34.112603+00:00
-- url     : https://prove2.me/submissions/c3f55cac-5f54-4274-98ce-87f15c83a09d

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq



namespace JHolomorphic

open MeasureTheory Filter Topology Set
open scoped ContDiff Manifold

/-- Weak partials on `U` restrict to weak partials on any open subset. -/
theorem HasWeakPartialsOn.mono_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U V : Set ℂ} (hVU : V ⊆ U) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn U u us ut) : HasWeakPartialsOn V u us ut :=
  fun φ hφ hc hφV => h φ hφ hc (hφV.trans hVU)

/-- Functions on a sequence of measurable sets that agree a.e. on overlaps glue to one function. -/
theorem exists_ae_eq_of_agree {E : Type*} [NormedAddCommGroup E] (W : ℕ → Set ℂ)
    (hW : ∀ n, MeasurableSet (W n)) (G : ℕ → ℂ → E)
    (hagree : ∀ m n, ∀ᵐ z ∂(volume.restrict (W m ∩ W n)), G m z = G n z) :
    ∃ g : ℂ → E, ∀ n, ∀ᵐ z ∂(volume.restrict (W n)), g z = G n z := by
  classical
  have hall : ∀ᵐ z ∂(volume : Measure ℂ), ∀ m n, z ∈ W m → z ∈ W n → G m z = G n z := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro n
    have := (ae_restrict_iff' ((hW m).inter (hW n))).1 (hagree m n)
    filter_upwards [this] with z hz hm hn using hz ⟨hm, hn⟩
  refine ⟨fun z => if h : ∃ n, z ∈ W n then G (Nat.find h) z else 0, fun n => ?_⟩
  rw [ae_restrict_iff' (hW n)]
  filter_upwards [hall] with z hz hzn
  have h : ∃ n, z ∈ W n := ⟨n, hzn⟩
  simp only [dif_pos h]
  exact hz _ _ (Nat.find_spec h) hzn

/-- `MemLp` on two sets gives `MemLp` on their union. -/
theorem memLp_restrict_union {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ENNReal} {g : α → E}
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (gA : MemLp g p (μ.restrict A)) (gB : MemLp g p (μ.restrict B)) :
    MemLp g p (μ.restrict (A ∪ B)) := by
  rw [← memLp_indicator_iff_restrict (hA.union hB)]
  have h1 : MemLp (A.indicator g) p μ := (memLp_indicator_iff_restrict hA).2 gA
  have h2 : MemLp ((B \ A).indicator g) p μ :=
    (memLp_indicator_iff_restrict (hB.diff hA)).2 (gB.mono_measure (Measure.restrict_mono
      diff_subset le_rfl))
  convert h1.add h2 using 1
  funext z
  by_cases hzA : z ∈ A
  · simp [hzA]
  · by_cases hzB : z ∈ B <;> simp [hzA, hzB]

/-- `MemLp` on each set of an open cover gives `MemLp` on every compact subset of the union. -/
theorem memLp_restrict_of_isCompact_subset_iUnion {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} {g : ℂ → E} (W : ℕ → Set ℂ) (hWo : ∀ n, IsOpen (W n))
    (hg : ∀ n, MemLp g p (volume.restrict (W n))) {K : Set ℂ} (hK : IsCompact K)
    (hKW : K ⊆ ⋃ n, W n) : MemLp g p (volume.restrict K) := by
  classical
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover W hWo hKW
  have hU : ∀ T : Finset ℕ, MemLp g p (volume.restrict (⋃ i ∈ T, W i)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih =>
      rw [Finset.set_biUnion_insert]
      exact memLp_restrict_union (hWo a).measurableSet
        (Finset.measurableSet_biUnion _ fun i _ => (hWo i).measurableSet) (hg a) ih
  exact (hU S).mono_measure (Measure.restrict_mono hS le_rfl)

/-- The weak-derivative identity in a direction `v` glues along an open cover. -/
theorem integral_fderiv_smul_of_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (W : ℕ → Set ℂ) (hWo : ∀ n, IsOpen (W n))
    (hWU : ∀ n, W n ⊆ U) (hcov : U ⊆ ⋃ n, W n) {f g : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K) (hg : ∀ K ⊆ U, IsCompact K → IntegrableOn g K)
    (v : ℂ)
    (hloc : ∀ n, ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W n →
      ∫ z, fderiv ℝ ψ z v • f z = -∫ z, ψ z • g z)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∫ z, fderiv ℝ φ z v • f z = -∫ z, φ z • g z := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) (isClosed_tsupport φ)
    W hWo (hφU.trans hcov)
  set F := (ρ.locallyFinite.finite_nonempty_inter_compact hφc).toFinset with hF
  set ψ : ℕ → ℂ → ℝ := fun i z => ρ i z * φ z with hψ
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  have hψs : ∀ i, ContDiff ℝ ∞ (ψ i) := fun i => (hρs i).mul hφ
  have hψc : ∀ i, HasCompactSupport (ψ i) := fun i => hφc.mul_left
  have hψW : ∀ i, tsupport (ψ i) ⊆ W i := fun i => (tsupport_mul_subset_left).trans (hρ i)
  have hψU : ∀ i, tsupport (ψ i) ⊆ U := fun i => (hψW i).trans (hWU i)
  have hsum : φ = fun z => ∑ i ∈ F, ψ i z := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · have h1 : ∑ᶠ i, ρ i z = 1 := ρ.sum_eq_one hz
      have hsub : (Function.support fun i => ρ i z) ⊆ ↑F := by
        intro i hi
        simp only [hF, Finite.coe_toFinset, mem_setOf_eq]
        exact ⟨z, hi, hz⟩
      rw [finsum_eq_sum_of_support_subset _ hsub] at h1
      simp only [hψ, ← Finset.sum_mul, h1, one_mul]
    · have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hψ, h0]
  have hfd : ∀ z, fderiv ℝ φ z v = ∑ i ∈ F, fderiv ℝ (ψ i) z v := by
    intro z
    rw [hsum, fderiv_fun_sum fun i _ => ((hψs i).differentiable (by simp)).differentiableAt,
      ContinuousLinearMap.sum_apply]
  have hint1 : ∀ i, Integrable (fun z => fderiv ℝ (ψ i) z v • f z) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := fderiv_apply_isTestFunction (hψs i) (hψc i) (hψU i) v
    exact integrable_smul_of_integrableOn_compact hf h1.continuous.continuousOn h2 h3
  have hint2 : ∀ i, Integrable (fun z => ψ i z • g z) := fun i =>
    integrable_smul_of_integrableOn_compact hg (hψs i).continuous.continuousOn (hψc i) (hψU i)
  calc ∫ z, fderiv ℝ φ z v • f z
      = ∫ z, ∑ i ∈ F, fderiv ℝ (ψ i) z v • f z := by
        congr 1; funext z; rw [hfd, Finset.sum_smul]
    _ = ∑ i ∈ F, ∫ z, fderiv ℝ (ψ i) z v • f z := integral_finset_sum _ fun i _ => hint1 i
    _ = ∑ i ∈ F, -∫ z, ψ i z • g z := by
        refine Finset.sum_congr rfl fun i _ => hloc i (ψ i) (hψs i) (hψc i) (hψW i)
    _ = -∫ z, ∑ i ∈ F, ψ i z • g z := by
        rw [integral_finset_sum _ fun i _ => hint2 i, Finset.sum_neg_distrib]
    _ = -∫ z, φ z • g z := by
        congr 2; funext z; rw [← Finset.sum_smul]; exact congrFun hsum.symm z ▸ rfl

/-- Local weak partial derivatives in `L^p` glue to weak partial derivatives on `U` that lie in
`L^p(K)` for every compact `K ⊆ U`. -/
theorem HasWeakPartialsOn.of_local_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {p : ENNReal} (hp : 1 ≤ p) {f : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    (hloc : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ ∃ gs gt : ℂ → E,
      HasWeakPartialsOn V f gs gt ∧ MemLp gs p (volume.restrict V) ∧
        MemLp gt p (volume.restrict V)) :
    ∃ gs gt : ℂ → E, HasWeakPartialsOn U f gs gt ∧
      ∀ K ⊆ U, IsCompact K → MemLp gs p (volume.restrict K) ∧ MemLp gt p (volume.restrict K) := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, 0, fun φ _ _ hφ => ?_, fun K hK _ => ?_⟩
    · have : φ = 0 := by
        funext z; exact image_eq_zero_of_notMem_tsupport fun hz => hφ hz
      subst this; simp
    · rw [subset_empty_iff.1 hK]; simp
  choose! V hVo hzV hVU gs gt hW hgs hgt using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun z : U => V z) (fun z => hVo z z.2)
  have hcovU : U ⊆ ⋃ z : U, V z := fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzV z hz⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    have : z ∈ ⋃ i ∈ T, V (i : ℂ) := hTU ▸ hcovU hz
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 this
    exact ⟨i, hi⟩
  obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
  set W : ℕ → Set ℂ := fun n => V (e n) with hWdef
  have hWo : ∀ n, IsOpen (W n) := fun n => hVo _ (e n).2
  have hWU : ∀ n, W n ⊆ U := fun n => hVU _ (e n).2
  have hcov : U ⊆ ⋃ n, W n := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V (i : ℂ) := hTU ▸ hcovU hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 this
    rw [he] at hi
    obtain ⟨n, rfl⟩ := hi
    exact mem_iUnion.2 ⟨n, hzi⟩
  have hWw : ∀ n, HasWeakPartialsOn (W n) f (gs (e n)) (gt (e n)) := fun n => hW _ (e n).2
  have hWs : ∀ n, MemLp (gs (e n)) p (volume.restrict (W n)) := fun n => hgs _ (e n).2
  have hWt : ∀ n, MemLp (gt (e n)) p (volume.restrict (W n)) := fun n => hgt _ (e n).2
  have hintK : ∀ {h : ℂ → E} {A : Set ℂ}, MemLp h p (volume.restrict A) → ∀ K ⊆ A,
      IsCompact K → IntegrableOn h K := by
    intro h A hA K hKA hK
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact (hA.mono_measure (Measure.restrict_mono hKA le_rfl)).integrable hp
  -- agreement on overlaps
  have hagree : ∀ m n, ∀ᵐ z ∂(volume.restrict (W m ∩ W n)),
      gs (e m) z = gs (e n) z ∧ gt (e m) z = gt (e n) z := by
    intro m n
    have hmn : W m ∩ W n ⊆ W m := inter_subset_left
    have hnm : W m ∩ W n ⊆ W n := inter_subset_right
    exact HasWeakPartialsOn.ae_eq ((hWo m).inter (hWo n)) ((hWw m).mono_set hmn)
      ((hWw n).mono_set hnm) fun K hK hKc =>
        ⟨hintK (hWs m) K (hK.trans hmn) hKc, hintK (hWt m) K (hK.trans hmn) hKc,
          hintK (hWs n) K (hK.trans hnm) hKc, hintK (hWt n) K (hK.trans hnm) hKc⟩
  obtain ⟨Gs, hGs⟩ := exists_ae_eq_of_agree W (fun n => (hWo n).measurableSet)
    (fun n => gs (e n)) fun m n => (hagree m n).mono fun _ h => h.1
  obtain ⟨Gt, hGt⟩ := exists_ae_eq_of_agree W (fun n => (hWo n).measurableSet)
    (fun n => gt (e n)) fun m n => (hagree m n).mono fun _ h => h.2
  have hGsL : ∀ n, MemLp Gs p (volume.restrict (W n)) := fun n =>
    (hWs n).ae_eq ((hGs n).mono fun _ h => h.symm)
  have hGtL : ∀ n, MemLp Gt p (volume.restrict (W n)) := fun n =>
    (hWt n).ae_eq ((hGt n).mono fun _ h => h.symm)
  have hLK : ∀ K ⊆ U, IsCompact K → MemLp Gs p (volume.restrict K) ∧
      MemLp Gt p (volume.restrict K) := fun K hKU hK =>
    ⟨memLp_restrict_of_isCompact_subset_iUnion W hWo hGsL hK (hKU.trans hcov),
      memLp_restrict_of_isCompact_subset_iUnion W hWo hGtL hK (hKU.trans hcov)⟩
  have hIs : ∀ K ⊆ U, IsCompact K → IntegrableOn Gs K := fun K hKU hK =>
    hintK (hLK K hKU hK).1 K subset_rfl hK
  have hIt : ∀ K ⊆ U, IsCompact K → IntegrableOn Gt K := fun K hKU hK =>
    hintK (hLK K hKU hK).2 K subset_rfl hK
  -- replacing the local partials by the glued ones inside `W n`
  have hrepl : ∀ n (G H : ℂ → E), (∀ᵐ z ∂(volume.restrict (W n)), H z = G z) →
      ∀ ψ : ℂ → ℝ, tsupport ψ ⊆ W n → ∫ z, ψ z • G z = ∫ z, ψ z • H z := by
    intro n G H hHG ψ hψ
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' (hWo n).measurableSet).1 hHG] with z hz
    by_cases hzW : z ∈ W n
    · rw [hz hzW]
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzW (hψ h)
      simp [this]
  refine ⟨Gs, Gt, fun φ hφ hφc hφU => ⟨?_, ?_⟩, hLK⟩
  · refine integral_fderiv_smul_of_cover W hWo hWU hcov hf hIs 1 (fun n ψ hψ hψc hψW => ?_)
      φ hφ hφc hφU
    rw [(hWw n ψ hψ hψc hψW).1, hrepl n (gs (e n)) Gs (hGs n) ψ hψW]
  · refine integral_fderiv_smul_of_cover W hWo hWU hcov hf hIt Complex.I
      (fun n ψ hψ hψc hψW => ?_) φ hφ hφc hφU
    rw [(hWw n ψ hψ hψc hψW).2, hrepl n (gt (e n)) Gt (hGt n) ψ hψW]

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {p : ENNReal} (hp : 1 ≤ p) {f : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    (hloc : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ ∃ gs gt : ℂ → E,
      HasWeakPartialsOn V f gs gt ∧ MemLp gs p (volume.restrict V) ∧
        MemLp gt p (volume.restrict V)) :
    ∃ gs gt : ℂ → E, HasWeakPartialsOn U f gs gt ∧
      ∀ K ⊆ U, IsCompact K → MemLp gs p (volume.restrict K) ∧ MemLp gt p (volume.restrict K) :=
  HasWeakPartialsOn.of_local_aux hU hp hf hloc
