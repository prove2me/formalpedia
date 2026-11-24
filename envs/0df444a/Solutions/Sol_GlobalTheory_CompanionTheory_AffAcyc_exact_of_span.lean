-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.exact_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:28.548541+00:00
-- url     : https://prove2.me/submissions/99300f7a-43e1-4011-9409-bf7075d3d141

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_sc
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution {B : Type} [CommRing B] (F : C ⥤ CommAlgCat.{0} R) (io' : ∀ T, B →+* F.obj T)
    (hio : ∀ (T T' : C) (φ : T ⟶ T') (b : B), mp F φ (io' T b) = io' T' b) (S : Set B)
    (hS : Ideal.span S = ⊤) (n : ℕ) (z : Cn F (n + 1))
    (h : ∀ f ∈ S, ∃ (N : ℕ) (y : Cn F n), dn F n y = sc F (fun T ↦ io' T f ^ N) (n + 1) z) :
    ∃ y, dn F n y = z := by
  let I : Ideal B :=
    { carrier := {b | ∃ y, dn F n y = sc F (fun T ↦ io' T b) (n + 1) z}
      add_mem' := by
        rintro a b ⟨y, hy⟩ ⟨y', hy'⟩
        refine ⟨y + y', ?_⟩
        rw [map_add, hy, hy']
        funext c
        simp only [sc, Pi.add_apply, map_add, add_mul]
      zero_mem' := ⟨0, by
        rw [map_zero]; funext c; simp [sc]⟩
      smul_mem' := by
        rintro a b ⟨y, hy⟩
        refine ⟨sc F (fun T ↦ io' T a) n y, ?_⟩
        rw [dn_sc F _ fun T T' φ ↦ hio T T' φ a, hy]
        funext c
        simp only [sc, smul_eq_mul, map_mul, _root_.mul_assoc] }
  have hI : S ⊆ I.radical := fun f hf ↦ by
    obtain ⟨N, y, hy⟩ := h f hf
    refine ⟨N, y, hy.trans ?_⟩
    funext c
    simp only [sc, map_pow]
  have h1 : I.radical = ⊤ := top_le_iff.1 (hS ▸ Ideal.span_le.2 hI)
  have h2 : (1 : B) ∈ I := by
    rw [Ideal.radical_eq_top.1 h1]; trivial
  obtain ⟨y, hy⟩ := h2
  refine ⟨y, hy.trans ?_⟩
  funext c
  simp only [sc, map_one, _root_.one_mul]
end GlobalTheory.CompanionTheory.AffAcyc
