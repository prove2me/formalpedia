-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:18.285848+00:00
-- url     : https://prove2.me/submissions/75c23ef6-8d70-4874-8ba5-6ed6bb18f59f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticGermFiniteProjection
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticGermSlice_isAnalyticNear_zeros_inter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
namespace GlobalTheory.CompanionTheory.AnalyticGermSlice
private theorem exists_eventually_eq_zero_of_prod_analyticAt {n : ℕ} (a : ℂ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) a) (hP : ∀ᶠ t in 𝓝 a, ∏ i, f i t = 0) :
    ∃ i, ∀ᶠ t in 𝓝 a, f i t = 0 := by
  by_contra hcon
  have hcon' : ∀ i, ¬ ∀ᶠ t in 𝓝 a, f i t = 0 := fun i hi => hcon ⟨i, hi⟩
  have hne : ∀ i, ∀ᶠ t in 𝓝[≠] a, f i t ≠ 0 := fun i =>
    ((hf i).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hcon' i)
  have hall : ∀ᶠ t in 𝓝[≠] a, ∀ i, f i t ≠ 0 := Filter.eventually_all.2 hne
  have hP' : ∀ᶠ t in 𝓝[≠] a, ∏ i, f i t = 0 := nhdsWithin_le_nhds hP
  obtain ⟨t, ht1, ht2⟩ := (hall.and hP').exists
  exact (Finset.prod_ne_zero_iff.2 fun i _ => ht1 i) ht2
end GlobalTheory.CompanionTheory.AnalyticGermSlice
end

set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticGermSlice
namespace GlobalTheory.CompanionTheory.AnalyticGermSlice
theorem _root_.solution :
    FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  intro hFG hGF hAC σ _ X w hX hirr hacc
  obtain ⟨d, A, ⟨W0, hW0, hfib⟩, hdom⟩ := hGF σ X w hX hirr
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨y, ⟨hyW, hyX⟩, hyw⟩ := (accPt_iff_nhds.1 hacc) W0 hW0
      exact absurd (hfib y ⟨hyX, hyW⟩ (Subsingleton.elim _ _)) hyw
    · exact h0
  let i0 : Fin d := ⟨0, hd⟩
  let g : Fin d → (σ → ℂ) → ℂ := fun j z => if j = i0 then 0 else A z j - A w j
  have hgan : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ := by
    intro j
    by_cases hj : j = i0
    · simp only [g, hj, if_true]
      exact analyticOnNhd_const
    · simp only [g, hj, if_false]
      exact (((ContinuousLinearMap.proj j).comp A).analyticOnNhd _).sub analyticOnNhd_const
  let S : Set (σ → ℂ) := {z | z ∈ X ∧ ∀ j, g j z = 0}
  have hSan : IsAnalyticNear S w := isAnalyticNear_zeros_inter hX g hgan
  have hwS : w ∈ S := ⟨hirr.1, fun j => by by_cases hj : j = i0 <;> simp [g, hj]⟩
  obtain ⟨n, Y, hYi, W1, hW1, hYeq⟩ := hAC σ S w hSan hwS
  let A1 : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.proj i0).comp A
  have hA1 : ∀ z k, A1 z k = A z i0 := fun z k => rfl
  have hfibS : ∀ x ∈ S ∩ W0, A1 x = A1 w → x = w := by
    rintro x ⟨⟨hxX, hxg⟩, hxW⟩ hx
    refine hfib x ⟨hxX, hxW⟩ (funext fun j => ?_)
    by_cases hj : j = i0
    · subst hj
      have := congrFun hx 0
      simpa [hA1] using this
    · have := hxg j
      simp only [g, hj, if_false, sub_eq_zero] at this
      exact this
  have himg : ∀ V ∈ 𝓝 w, A1 '' (S ∩ V) ∈ 𝓝 (A1 w) := by
    intro V hV
    have hbig := hFG σ X w d A hX ⟨W0, hW0, hfib⟩ hdom V hV
    let ψ : (Fin 1 → ℂ) → (Fin d → ℂ) := fun y j => if j = i0 then y 0 else A w j
    have hψc : Continuous ψ := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = i0
      · simp only [ψ, hj, if_true]
        exact continuous_apply 0
      · simp only [ψ, hj, if_false]
        exact continuous_const
    have hψw : ψ (A1 w) = A w := by
      funext j
      by_cases hj : j = i0
      · subst hj
        simp [ψ, hA1]
      · simp [ψ, hj]
    have hpre : ψ ⁻¹' (A '' (X ∩ V)) ∈ 𝓝 (A1 w) := by
      apply hψc.continuousAt.preimage_mem_nhds
      rw [hψw]
      exact hbig
    refine Filter.mem_of_superset hpre ?_
    rintro y ⟨x, ⟨hxX, hxV⟩, hxy⟩
    refine ⟨x, ⟨⟨hxX, fun j => ?_⟩, hxV⟩, ?_⟩
    · by_cases hj : j = i0
      · simp [g, hj]
      · have := congrFun hxy j
        simp only [ψ, hj, if_false] at this
        simp [g, hj, this]
    · funext k
      have := congrFun hxy i0
      simp only [ψ, if_true] at this
      rw [hA1, this, Subsingleton.elim k 0]
  have hdomi : ∃ i, ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) →
      (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) → ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
    by_contra hcon
    have hcon' : ∀ i, ∃ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A1 w) ∧
        (∀ᶠ z in 𝓝 w, z ∈ Y i → h (A1 z) = 0) ∧ ¬ ∀ᶠ y in 𝓝 (A1 w), h y = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, fun h ha hz => by
        by_contra hy
        exact hi ⟨h, ha, hz, hy⟩⟩
    choose h hha hhz hhnz using hcon'
    let c : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
    let a : ℂ := A w i0
    have hca : c a = A1 w := by
      funext k
      rfl
    have hback : ∀ φ : (Fin 1 → ℂ) → ℂ, (∀ᶠ t in 𝓝 a, φ (c t) = 0) → ∀ᶠ y in 𝓝 (A1 w), φ y = 0 := by
      intro φ hφ
      have hev : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 (A1 w)) (𝓝 a) :=
        (continuous_apply 0).tendsto' _ _ rfl
      filter_upwards [hev.eventually hφ] with y hy
      have hyc : c (y 0) = y := by
        funext k
        rw [Subsingleton.elim k 0]
        rfl
      rwa [hyc] at hy
    have hfan : ∀ i, AnalyticAt ℂ (fun t => h i (c t)) a := by
      intro i
      have h1 : AnalyticAt ℂ (h i) (c a) := by
        rw [hca]
        exact hha i
      exact h1.comp (c.analyticAt a)
    have hPz : ∀ᶠ t in 𝓝 a, ∏ i, h i (c t) = 0 := by
      have hV : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y i → h i (A1 z) = 0 := Filter.eventually_all.2 hhz
      have hV' : {z | ∀ i, z ∈ Y i → h i (A1 z) = 0} ∩ W1 ∈ 𝓝 w := Filter.inter_mem hV hW1
      have hI := himg _ hV'
      have hy : ∀ᶠ y in 𝓝 (A1 w), ∏ i, h i y = 0 := by
        filter_upwards [hI] with y hy
        obtain ⟨x, ⟨hxS, hxV, hxW⟩, rfl⟩ := hy
        have hxU : x ∈ (⋃ i, Y i) ∩ W1 := by
          rw [← hYeq]
          exact ⟨hxS, hxW⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU.1
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hxV i hi)
      have hev : Tendsto c (𝓝 a) (𝓝 (A1 w)) := by
        rw [← hca]
        exact c.continuous.tendsto a
      exact hev.eventually hy
    obtain ⟨i, hi⟩ := exists_eventually_eq_zero_of_prod_analyticAt a (fun i t => h i (c t)) hfan hPz
    exact hhnz i (hback (h i) hi)
  obtain ⟨i, hi⟩ := hdomi
  refine ⟨Y i, W1, A1, hW1, ?_, (hYi i).1, (hYi i).2, ⟨W1 ∩ W0, Filter.inter_mem hW1 hW0, ?_⟩, hi⟩
  · rintro z ⟨hzY, hzW⟩
    have hzU : z ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hzY⟩, hzW⟩
    rw [← hYeq] at hzU
    exact hzU.1.1
  · rintro x ⟨hxY, hxW1, hxW0⟩ hx
    have hxU : x ∈ (⋃ j, Y j) ∩ W1 := ⟨Set.mem_iUnion.2 ⟨i, hxY⟩, hxW1⟩
    rw [← hYeq] at hxU
    exact hfibS x ⟨hxU.1, hxW0⟩ hx
end GlobalTheory.CompanionTheory.AnalyticGermSlice
