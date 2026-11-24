-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.closed_on_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:24.714262+00:00
-- url     : https://prove2.me/submissions/66021d48-a12c-437b-a827-2f05a8f4ec72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_restrict_of_dense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {S W P X : Scheme.{0}} (f : W ⟶ S) (s : P ⟶ S) [IsSeparated f]
    (U O : W.Opens) (hUO : U ≤ O) (φ : U.toScheme ⟶ P) (ι : X ⟶ pullback f s)
    [IsClosedImmersion ι] (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ ι ≫ pullback.fst f s = U.ι) (h₂ : j ≫ ι ≫ pullback.snd f s = φ)
    {σ : Type} (g : σ → Γ(O.toScheme, ⊤))
    [IsClosedImmersion (AffineSpace.homOfVector (O.ι ≫ f) g)]
    (D : P.Opens) (r : σ → Γ(D.toScheme, ⊤))
    (hr : ∀ (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D), a ≫ φ = b ≫ D.ι →
      ∀ i, b.appTop (r i) = a.appTop ((W.homOfLE hUO).appTop (g i))) :
    IsClosedImmersion ((ι ≫ pullback.snd f s) ∣_ D) := by
  let c := AffineSpace.homOfVector (O.ι ≫ f) g
  let h := AffineSpace.homOfVector (D.ι ≫ s) r
  have hc : c ≫ 𝔸(σ; S) ↘ S = O.ι ≫ f := AffineSpace.homOfVector_over _ _
  have hh : h ≫ 𝔸(σ; S) ↘ S = D.ι ≫ s := AffineSpace.homOfVector_over _ _
  have hφ : φ ≫ s = U.ι ≫ f := by
    rw [← h₁, ← h₂]; simp [pullback.condition]
  refine closed_restrict_of_dense (pullback.snd f s) ι j D (pullback.snd c h)
    (pullback.lift (pullback.fst c h ≫ O.ι) (pullback.snd c h ≫ D.ι) (by
      rw [Category.assoc, Category.assoc, ← hc, ← hh, pullback.condition_assoc]))
    (pullback.lift_snd _ _ _) ?_
  intro Z a b hab
  rw [h₂] at hab
  refine ⟨pullback.lift (a ≫ W.homOfLE hUO) b ?_, ?_⟩
  · apply AffineSpace.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, hc, hh, Scheme.homOfLE_ι_assoc,
        ← reassoc_of% hab, hφ]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, c, h,
        AffineSpace.homOfVector_appTop_coord]
      exact (hr Z a b hab i).symm
  · apply pullback.hom_ext
    · simp [h₁, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [h₂, hab, pullback.lift_snd, pullback.lift_snd_assoc]
end GlobalTheory.DenseClosedAffineSubsets
