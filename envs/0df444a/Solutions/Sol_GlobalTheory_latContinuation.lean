-- Prove2me | solution 1 for GlobalTheory.latContinuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:51.519792+00:00
-- url     : https://prove2.me/submissions/b3a3d194-d5f4-4d4d-8452-6aec1c521ba2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LatContMapContinuous
import Theorems.Thm_GlobalTheory_latCont_discrete
import Theorems.Thm_GlobalTheory_latContMap_apply
import Theorems.Thm_GlobalTheory_latContMap_repr
import Theorems.Thm_GlobalTheory_latCont_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range := by
  intro La _ _ _ g m B b₀ K P r hB hb₀ hr hdisc hclosed hcont hle heq hinj hspan
  obtain ⟨J, _, ⟨e⟩⟩ : ∃ (J : Type) (_ : Fintype J), Nonempty (Module.Basis J ℤ La) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ La⟩⟩
  have hrepr : ∀ b (k : J → ℤ), P b (e.equivFun.symm k) = ∑ j, ((k j : ℤ) : ℝ) • P b (e j) := by
    intro b k
    rw [← latContMap_repr e (P b) k, latContMap_apply]
  have hcoord : ∀ b x, P b x = ∑ j, ((e.equivFun x j : ℤ) : ℝ) • P b (e j) := by
    intro b x
    rw [← hrepr]
    simp
  have hdiscR : ∀ b ∈ B, DiscreteTopology (P b).range := fun b hb =>
    latCont_discrete _ r hr (fun z hz hzr => hdisc b hb z (hle b hb hz) hzr)
  have hcard : Fintype.card J = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← Module.finrank_fintype_fun_eq_card ℝ]
    exact latCont_card e (P b₀) (hdiscR b₀ hb₀) hinj hspan
  have hspan0 : ⊤ ≤ Submodule.span ℝ (Set.range (fun j => P b₀ (e j))) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [hcoord]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hli0 : LinearIndependent ℝ (fun j => P b₀ (e j)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan0 hcard
  have hvc : ContinuousAt (fun b => fun j => P b (e j)) b₀ :=
    continuousAt_pi.mpr (fun j => hcont (e j))
  have hev_li : ∀ᶠ b in nhds b₀, LinearIndependent ℝ (fun j => P b (e j)) :=
    hvc.tendsto.eventually hli0.eventually
  have hev_B : ∀ᶠ b in nhds b₀, b ∈ B := hB.mem_nhds hb₀
  have hspanv : ∀ b, LinearIndependent ℝ (fun j => P b (e j)) →
      Submodule.span ℝ (Set.range (fun j => P b (e j))) = ⊤ :=
    fun b hb => hb.span_eq_top_of_card_eq_finrank' hcard
  have hsurj : ∀ b, LinearIndependent ℝ (fun j => P b (e j)) →
      ∀ z, ∃ c : J → ℝ, ∑ j, c j • P b (e j) = z := by
    intro b hb z
    have hz : z ∈ Submodule.span ℝ (Set.range (fun j => P b (e j))) := by
      rw [hspanv b hb]
      trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
  have hev_eq : ∀ᶠ b in nhds b₀, ∀ z ∈ K b, z ∈ (P b).range := by
    by_contra hne
    rw [Filter.not_eventually] at hne
    have hfr : ∃ᶠ b in nhds b₀, b ∈ B ∧ LinearIndependent ℝ (fun j => P b (e j)) ∧
        ∃ z ∈ K b, z ∉ (P b).range := by
      refine (hne.and_eventually (hev_B.and hev_li)).mono ?_
      rintro b ⟨h1, h2, h3⟩
      push Not at h1
      exact ⟨h2, h3, h1⟩
    obtain ⟨bs, hbs, hprop⟩ := Filter.exists_seq_forall_of_frequently hfr
    choose hbsB hbsli z hzK hzR using hprop
    choose c hc using fun i => hsurj (bs i) (hbsli i) (z i)
    have hshift : ∀ i (k : J → ℤ),
        (∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)) ∈ K (bs i) ∧
        (∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)) ∉ (P (bs i)).range := by
      intro i k
      have e1 : ∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)
          = z i - P (bs i) (e.equivFun.symm (fun j => ⌊c i j⌋ + k j)) := by
        rw [hrepr, ← hc i, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← sub_smul]
        congr 1
        push_cast
        rw [← Int.self_sub_floor]
        ring
      rw [e1]
      have hmem : P (bs i) (e.equivFun.symm (fun j => ⌊c i j⌋ + k j)) ∈ (P (bs i)).range :=
        ⟨_, rfl⟩
      refine ⟨sub_mem (hzK i) (hle _ (hbsB i) hmem), fun h => hzR i ?_⟩
      have := add_mem h hmem
      rwa [sub_add_cancel] at this
    have hIcc : ∀ i, (fun j => Int.fract (c i j)) ∈ Set.Icc (0 : J → ℝ) 1 := fun i =>
      ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩
    obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_Icc (a := (0 : J → ℝ)) (b := 1)).tendsto_subseq hIcc
    have hbφ : Filter.Tendsto (bs ∘ φ) Filter.atTop (nhds b₀) := hbs.comp hφ.tendsto_atTop
    have hvφ : ∀ j, Filter.Tendsto (fun i => P (bs (φ i)) (e j)) Filter.atTop
        (nhds (P b₀ (e j))) := fun j => (hcont (e j)).tendsto.comp hbφ
    have haj : ∀ j, Filter.Tendsto (fun i => Int.fract (c (φ i) j)) Filter.atTop (nhds (a j)) :=
      fun j => ((continuous_apply j).tendsto a).comp ha
    have hlim : ∀ k : J → ℤ, Filter.Tendsto
        (fun i => ∑ j, (Int.fract (c (φ i) j) - (k j : ℝ)) • P (bs (φ i)) (e j)) Filter.atTop
        (nhds (∑ j, (a j - (k j : ℝ)) • P b₀ (e j))) := fun k =>
      tendsto_finsetSum _ (fun j _ => ((haj j).sub_const _).smul (hvφ j))
    have hz0 : (∑ j, (a j - ((0 : J → ℤ) j : ℝ)) • P b₀ (e j)) ∈ K b₀ :=
      hclosed (bs ∘ φ) _ _ hbφ (hlim 0) (fun i => (hshift (φ i) 0).1)
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hz0
    rw [← heq] at hz0
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hz0
    have hzero : ∑ j, (a j - ((e.equivFun x j : ℤ) : ℝ)) • P b₀ (e j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hcoord b₀ x, ← hx, sub_self]
    have hlim0 := hlim (e.equivFun x)
    rw [hzero] at hlim0
    obtain ⟨i, hi⟩ := (hlim0.eventually (Metric.ball_mem_nhds (0 : Fin g → ℂ) hr)).exists
    rw [dist_zero_right] at hi
    obtain ⟨hK', hR'⟩ := hshift (φ i) (e.equivFun x)
    exact hR' (by rw [hdisc _ (hbsB (φ i)) _ hK' hi]; exact zero_mem _)
  filter_upwards [hev_B, hev_li, hev_eq] with b hb hli hrange
  refine ⟨le_antisymm (hle b hb) (fun z hz => hrange z hz), ?_, ?_, hdiscR b hb⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hcoord] at hx
    have h0 := (Fintype.linearIndependent_iff.mp hli) _ hx
    have h1 : e.equivFun x = 0 := funext fun j => by simpa using h0 j
    simpa using congrArg e.equivFun.symm h1
  · rw [eq_top_iff, ← hspanv b hli]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨e j, rfl⟩
end GlobalTheory
