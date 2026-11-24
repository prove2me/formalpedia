-- Prove2me | solution 1 for GlobalTheory.JR.descFn_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:50.792108+00:00
-- url     : https://prove2.me/submissions/10759d56-6c2b-4fb4-9602-56b1f3eb7b57

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportDescendedFunction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  intro F E _ _ _ _ _ A r M Ax j lam α hαl hαc f hf

  have hstar : Continuous (star : E → E) := by
    have : Isometry (starAddEquiv : E ≃+ E) :=
      (AddMonoidHomClass.isometry_iff_norm (starAddEquiv : E ≃+ E)).2 (fun x => Unram.norm_star F x)
    exact this.continuous
  haveI : ContinuousStar E := ⟨hstar⟩
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjs : Continuous j.symm :=
    LinearMap.continuous_of_finiteDimensional ((j.symm : (Fin r → E) →ₗ[E] A.L).restrictScalars F)

  have hact : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (actU p.2 (Ax, j p.1, lam) : Hn r F E)) := by
    have hg : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (p.2 : Matrix (Fin r) (Fin r) E)) :=
      continuous_subtype_val.comp continuous_snd
    have c1 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) * Ax.1 * star (p.2 : Matrix (Fin r) (Fin r) E)) :=
      (hg.mul continuous_const).mul hg.star
    have c2 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) *ᵥ j p.1) :=
      Continuous.matrix_mulVec hg (hj.comp continuous_fst)
    exact Continuous.prodMk (Continuous.subtype_mk c1 _) (Continuous.prodMk c2 continuous_const)
  set Φ : A.L × Matrix.unitaryGroup (Fin r) E → ℂ := fun p => f (actU p.2 (Ax, j p.1, lam)) * (α p.2 : ℂ) with hΦ
  have hΦl : IsLocallyConstant Φ := by
    refine IsLocallyConstant.mul (hf.1.comp_continuous hact) ?_
    exact (hαl.comp_continuous continuous_snd).comp (fun x : ℝ => (x : ℂ))
  have hdesc : ∀ y, A.descFn M Ax j lam α f y = (letI := M.mU; ∫ g, Φ (y, g) ∂M.μU) := fun y => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y0
    have key : ∀ᶠ y in 𝓝 y0, ∀ g ∈ tsupport α, Φ (y, g) = Φ (y0, g) := by
      refine hαc.isCompact.eventually_forall_of_forall_eventually ?_
      intro g _
      have h1 := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦl (y0, g)
      have h2 : ∀ᶠ z : A.L × Matrix.unitaryGroup (Fin r) E in 𝓝 (y0, g), Φ (y0, z.2) = Φ (y0, g) := by
        have h3 : Tendsto (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) (𝓝 (y0, g)) (𝓝 (y0, g)) := by
          have : Continuous (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) :=
            continuous_const.prodMk continuous_snd
          simpa using this.tendsto (y0, g)
        exact h3.eventually h1
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    rw [hdesc, hdesc]
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hy g hg
    · have : α g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [hΦ, this]
  · let S : Set (Fin r → E) := Prod.fst '' (Prod.snd '' tsupport f)
    let Kset : Set A.L := (fun p : Matrix.unitaryGroup (Fin r) E × (Fin r → E) => j.symm (star (p.1 : Matrix (Fin r) (Fin r) E) *ᵥ p.2)) '' (tsupport α ×ˢ S)
    have hS : IsCompact S :=
      (hf.2.isCompact.image continuous_snd).image continuous_fst
    have hK : IsCompact Kset := by
      refine (hαc.isCompact.prod hS).image ?_
      refine hjs.comp ?_
      exact Continuous.matrix_mulVec ((continuous_subtype_val.comp continuous_fst).star) continuous_snd
    have hKc : IsClosed Kset := by
      have h1 : IsClosed (j '' Kset) := (hK.image hj).isClosed
      have h2 : Kset = j ⁻¹' (j '' Kset) := (Set.preimage_image_eq _ j.injective).symm
      rw [h2]
      exact h1.preimage hj
    refine HasCompactSupport.intro' hK hKc ?_
    intro y hy
    by_contra hne
    rw [hdesc] at hne
    have : ∃ g, Φ (y, g) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      have : (fun g => Φ (y, g)) = fun _ => 0 := funext hall
      rw [this]
      simp
    obtain ⟨g, hg⟩ := this
    have hfg : f (actU g (Ax, j y, lam)) ≠ 0 := left_ne_zero_of_mul hg
    have hαg : (α g : ℂ) ≠ 0 := right_ne_zero_of_mul hg
    have hαg' : α g ≠ 0 := by exact_mod_cast hαg
    apply hy
    refine ⟨(g, g.1 *ᵥ j y), ⟨subset_tsupport _ hαg', ?_⟩, ?_⟩
    · exact ⟨(actU g (Ax, j y, lam)).2, ⟨actU g (Ax, j y, lam), subset_tsupport _ hfg, rfl⟩, rfl⟩
    · simp only [Matrix.mulVec_mulVec]
      have hu : star (g.1 : Matrix (Fin r) (Fin r) E) * g.1 = 1 := Matrix.UnitaryGroup.star_mul_self g
      rw [hu, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
end GlobalTheory.JR
