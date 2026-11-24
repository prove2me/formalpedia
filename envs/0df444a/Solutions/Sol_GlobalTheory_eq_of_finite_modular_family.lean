-- Prove2me | solution 1 for GlobalTheory.eq_of_finite_modular_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:08.707537+00:00
-- url     : https://prove2.me/submissions/3b31a996-83be-43f9-bf60-92616e861336

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F : Set (ℍ → ℂ)} (hF : F.Finite)
    (hol : ∀ f ∈ F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (bdd : ∀ f ∈ F, UpperHalfPlane.IsBoundedAtImInfty f)
    (hS : ∀ f ∈ F, (fun z => f (ModularGroup.S • z)) ∈ F)
    (hT : ∀ f ∈ F, (fun z => f (ModularGroup.T • z)) ∈ F)
    {f : ℍ → ℂ} (hf : f ∈ F) (z w : ℍ) : f z = f w := by
  have key : ∀ X : ℂ, ∃ c, (∏ f ∈ hF.toFinset, (fun z => X - f z) : ℍ → ℂ) =
      Function.const _ c := by
    intro X
    set P : ℍ → ℂ := ∏ f ∈ hF.toFinset, (fun z => X - f z) with hP
    have hγ : ∀ γ : SL(2, ℤ), (∀ f ∈ F, (fun z => f (γ • z)) ∈ F) → P ∣[(0 : ℤ)] γ = P := by
      intro γ hγ
      have hinj : Function.Injective fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z) := by
        intro f f' h
        funext z
        simpa using congrFun h (γ⁻¹ • z)
      have hb : Set.BijOn (fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z)) F F :=
        (hF.injOn_iff_bijOn_of_mapsTo hγ).1 hinj.injOn
      ext z
      rw [ModularForm.SL_slash_apply]
      simp only [neg_zero, zpow_zero, mul_one, hP, Finset.prod_apply]
      exact Finset.prod_nbij (fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z))
        (fun f hf => by simpa using hγ f (by simpa using hf)) hinj.injOn
        (by simpa using hb.surjOn) (fun f _ => rfl)
    have hs := SlashInvariantForm.slash_action_generators_SL2Z (hγ _ hS) (hγ _ hT)
    have hb : UpperHalfPlane.IsBoundedAtImInfty P := by
      refine Filter.BoundedAtFilter.prod _ fun f hf => ?_
      exact Asymptotics.IsBigO.sub (Filter.const_boundedAtFilter _ X) (bdd f (by simpa using hf))
    let M : ModularForm 𝒮ℒ 0 :=
      { toFun := P
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
        holo' := by
          refine Finset.prod_induction _ (fun f : ℍ → ℂ => MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
            (fun a b ha hb => ha.mul hb) mdifferentiable_const fun f hf => ?_
          exact mdifferentiable_const.sub (hol f (by simpa using hf))
        bdd_at_cusps' := fun {c} hc ↦ by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hs γ]
          exact hb }
    exact ModularFormClass.levelOne_weight_zero_const M
  have hfin : ((fun f : ℍ → ℂ => f UpperHalfPlane.I) '' F).Finite := hF.image _
  refine isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete
    (hol f hf).continuous.continuousOn (fun t _ => ?_) (Set.mem_univ z) (Set.mem_univ w)
  obtain ⟨c, hc⟩ := key (f t)
  have h1 := congrFun hc t
  have h2 := congrFun hc UpperHalfPlane.I
  simp only [Finset.prod_apply, Function.const_apply] at h1 h2
  rw [Finset.prod_eq_zero (f := fun c : ℍ → ℂ => f t - c t) (hF.mem_toFinset.2 hf) (sub_self _)]
    at h1
  obtain ⟨f', hf', h⟩ := Finset.prod_eq_zero_iff.1 (h2.trans h1.symm)
  exact ⟨f', hF.mem_toFinset.1 hf', (sub_eq_zero.1 h).symm⟩
end GlobalTheory
