-- Prove2me | solution 2 for MasulloGRH.strictLF_nhds_zero_of_absConvex_traces
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:11:54.988091+00:00
-- url     : https://prove2.me/submissions/401aff59-c61e-4cb6-91f8-f59ff8709c5b

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps

set_option autoImplicit false

open MasulloGRH Topology

theorem sqrl_aux_cont {E : Type*} [AddCommGroup E] [Module ℂ E] (fam : SeminormFamily ℂ E PUnit)
    (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (f : F →ₗ[ℂ] E) (h : Continuous ((fam PUnit.unit).comp f)) :
    @Continuous F E _ fam.moduleFilterBasis.topology f := by
  letI : TopologicalSpace E := fam.moduleFilterBasis.topology
  have hw : WithSeminorms fam := ⟨rfl⟩
  exact hw.continuous_of_continuous_comp f (fun _ => h)

theorem sqrl_aux_lc {E : Type*} [AddCommGroup E] [Module ℂ E] (fam : SeminormFamily ℂ E PUnit) :
    @WithSeminorms ℂ E PUnit _ _ _ fam fam.moduleFilterBasis.topology := by
  letI : TopologicalSpace E := fam.moduleFilterBasis.topology
  exact ⟨rfl⟩

theorem sqrl_aux_ball {E : Type*} [AddCommGroup E] [Module ℂ E] (fam : SeminormFamily ℂ E PUnit) :
    {x | fam PUnit.unit x < 1} ∈ @nhds E fam.moduleFilterBasis.topology 0 := by
  letI : TopologicalSpace E := fam.moduleFilterBasis.topology
  have hw : WithSeminorms fam := ⟨rfl⟩
  have hc := hw.continuous_seminorm PUnit.unit
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (Ω : Set E) (hconv : Convex ℝ Ω) (hbal : Balanced ℂ Ω)
    (htr : ∀ n, ((↑) : X n → E) ⁻¹' Ω ∈ nhds (0 : X n)) :
    Ω ∈ nhds (0 : E) := by
  obtain ⟨⟨hlc, -⟩, -⟩ := strictLF_hlcs_and_closed_steps E X hmono hexh hX htop
  obtain ⟨ι, _, p, hp⟩ := hlc
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have h0 : (0 : E) ∈ Ω := by
    have := mem_of_mem_nhds (htr 0)
    simpa using this
  have habs : Absorbent ℝ Ω := by
    intro x
    obtain ⟨n, hn⟩ := hexh x
    have : ContinuousSMul ℝ (X n) :=
      ⟨(Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd⟩
    have hA : Absorbent ℝ (((↑) : X n → E) ⁻¹' Ω) := absorbent_nhds_zero (htr n)
    have h1 := hA ⟨x, hn⟩
    unfold Absorbs at h1 ⊢
    filter_upwards [h1] with a ha
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨z, hz, hz'⟩ := ha (Set.mem_singleton _)
    refine ⟨(z : E), hz, ?_⟩
    have := congrArg (fun w : X n => (w : E)) hz'
    simpa using this
  let q : Seminorm ℂ E := gaugeSeminorm hbal hconv habs
  let fam : SeminormFamily ℂ E PUnit := fun _ => q
  have hcont : ∀ n, Continuous (q.comp (X n).subtype) := by
    intro n
    apply Seminorm.continuous (r := 2)
    rw [Seminorm.ball_comp]
    apply Filter.mem_of_superset (htr n)
    intro z hz
    simp only [Set.mem_preimage, Seminorm.mem_ball, map_zero, sub_zero] at hz ⊢
    have : gauge Ω (z : E) ≤ 1 := gauge_le_one_of_mem hz
    show gauge Ω (z : E) < 2
    linarith
  have hmem : fam.moduleFilterBasis.topology ∈ {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val} := by
    refine ⟨⟨PUnit, inferInstance, fam, sqrl_aux_lc fam⟩, fun n => ?_⟩
    have : IsTopologicalAddGroup (X n) := inferInstance
    exact sqrl_aux_cont fam (X n) (X n).subtype (hcont n)
  have hle : ‹TopologicalSpace E› ≤ fam.moduleFilterBasis.topology := by rw [htop]; exact sInf_le hmem
  have hball : {x | gauge Ω x < 1} ∈ @nhds E fam.moduleFilterBasis.topology 0 := sqrl_aux_ball fam
  have : {x | gauge Ω x < 1} ∈ nhds (0 : E) := nhds_mono hle hball
  exact Filter.mem_of_superset this (setOfPred_gauge_lt_one_subset_self hconv h0 habs)
