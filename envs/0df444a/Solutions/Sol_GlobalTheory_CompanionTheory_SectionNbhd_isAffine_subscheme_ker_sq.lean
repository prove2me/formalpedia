-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:13.664363+00:00
-- url     : https://prove2.me/submissions/c56eaa13-1702-4446-aa77-244a8eb5c588

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffine
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SectionNbhd
namespace GlobalTheory.CompanionTheory.SectionNbhd
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U)
      [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  intro R _ U t e _ het
  have hte : ∀ q : Sp R, t (e q) = q := fun q => by
    have := congr($(het) q)
    simpa using this
  set c := (e.ker ^ 2).subschemeι with hc
  have hrange : ∀ x, ∃ q : Sp R, c x = e q := by
    intro x
    have h1 : c x ∈ Set.range c := ⟨x, rfl⟩
    rw [hc, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_pow _ _ two_ne_zero, Scheme.Hom.support_ker,
      e.isClosedEmbedding.isClosed_range.closure_eq] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq.symm⟩
  have haff : IsAffineHom (c ≫ t) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := e y) (U := ⊤) trivial
    obtain ⟨f, hfle, hyf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le
      (V := e ⁻¹ᵁ V₀) ⟨y, hyV₀⟩ trivial
    refine ⟨(Sp R).basicOpen f, hyf, (isAffineOpen_top (Sp R)).basicOpen f, ?_⟩
    have hV : IsAffineOpen (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      rw [Scheme.preimage_basicOpen]
      have h := Scheme.basicOpen_res U (V := V₀) (t.app ⊤ f) (homOfLE le_top).op
      rw [← h]
      exact hV₀.basicOpen _
    have heq : (c ≫ t) ⁻¹ᵁ (Sp R).basicOpen f = c ⁻¹ᵁ (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      ext x
      constructor
      · intro hx
        have hx' : t (c x) ∈ (Sp R).basicOpen f := hx
        refine ⟨?_, hx'⟩
        obtain ⟨q, hq⟩ := hrange x
        rw [hq, hte] at hx'
        have : e q ∈ V₀ := hfle hx'
        simpa [hq] using this
      · intro hx
        exact hx.2
    rw [heq]
    exact hV.preimage c
  exact isAffine_of_isAffineHom (c ≫ t)
end GlobalTheory.CompanionTheory.SectionNbhd
