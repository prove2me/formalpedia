-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.landing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:00.244816+00:00
-- url     : https://prove2.me/submissions/04f1ae4e-ed44-46a7-b030-bba37d95dd2d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution {X : Scheme.{0}} {A Q R' : Type} [CommRing A] [CommRing Q] [CommRing R']
    (j : Sp A ⟶ X) [IsOpenImmersion j] (ε : A →+* R') (q : Q →+* R')
    (hq : Function.Surjective q) (hnil : ∀ x, q x = 0 → IsNilpotent x)
    (y : Sp Q ⟶ X) (hy : spMap q ≫ y = spMap ε ≫ j) :
    ∃ ψ : A →+* Q, y = spMap ψ ≫ j := by
  have hsurj : ∀ p : Sp Q, ∃ p' : Sp R', spMap q p' = p := by
    intro p
    have : (p : PrimeSpectrum Q) ∈ Set.range (PrimeSpectrum.comap q) := by
      rw [range_comap_of_surjective _ q hq]
      intro x hx
      obtain ⟨n, hn⟩ := hnil x hx
      exact p.2.mem_of_pow_mem n (hn ▸ zero_mem _)
    obtain ⟨p', hp'⟩ := this
    exact ⟨p', hp'⟩
  have hr : Set.range y ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p', rfl⟩ := hsurj p
    have h1 : y (spMap q p') = (spMap q ≫ y) p' := by simp
    rw [h1, hy]
    exact ⟨spMap ε p', by simp⟩
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j y hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift j y hr)).hom = IsOpenImmersion.lift j y hr := by
    simp [spMap]
  rw [this, IsOpenImmersion.lift_fac]
end GlobalTheory.CompanionTheory.CotLoc
