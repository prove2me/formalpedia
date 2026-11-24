-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.good_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:18.825992+00:00
-- url     : https://prove2.me/submissions/c9fc099e-f5d4-4ad0-875d-dc01021c84be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
import Theorems.Thm_GlobalTheory_SS_FrobField_absFrob_appLE
import Theorems.Thm_GlobalTheory_SS_FrobField_good_of_cover
import Theorems.Thm_GlobalTheory_SS_FrobField_appLE_congr_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField
namespace GlobalTheory.SS.FrobField
theorem _root_.solution {X G S T : Scheme.{0}} [IsAffine S] [IsAffine T] {g : X ⟶ G} {s : X ⟶ T}
    {a : G ⟶ S} {b : T ⟶ S} (H : IsPullback g s a b) (p r : ℕ) (hp : p.Prime) (hc : (p : Γ(X, ⊤)) = 0)
    (hT : ∀ c : Γ(T, ⊤), ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) (F : End X)
    (hg : (show X ⟶ X from F) ≫ g = absFrob X p r hp hc ≫ g) (hs : (show X ⟶ X from F) ≫ s = s)
    (U : X.Opens) (hU : IsCompact (U : Set X)) (f : Γ(X, U)) : Good F (p ^ r) U f := by
  refine good_of_cover (pow_pos hp.pos r) (fun x => ?_) U hU f
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g x)) isOpen_univ
  have : IsAffineHom b := inferInstance
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip this
  refine ⟨g ⁻¹ᵁ V, hx, IsAffineOpen.preimage hV g, fun f => ?_⟩
  have hF : g ⁻¹ᵁ V = (show X ⟶ X from F) ⁻¹ᵁ g ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hg]; rfl
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hV)
  have hle : ⊤ ≤ goodSubring F p r hp _ (cast_zero hc _) hF := by
    rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1, le_rfl, ?_⟩
      rw [pow_one, pow_one]
      refine ⟨hF, ?_⟩
      have e1 := Scheme.Hom.appLE_comp_appLE (show X ⟶ X from F) g V (g ⁻¹ᵁ V) (g ⁻¹ᵁ V) le_rfl hF.le
      have e2 := Scheme.Hom.appLE_comp_appLE (absFrob X p r hp hc) g V (g ⁻¹ᵁ V) (g ⁻¹ᵁ V) le_rfl le_rfl
      have e3 := (e1.trans (appLE_congr_hom hg _ _ _ _)).trans e2.symm
      exact (congrArg (fun φ => φ.hom y) e3).trans (absFrob_appLE X p r hp hc _ _ _)
    · obtain ⟨m, hm, hc'⟩ := hT c
      have h1 : ∀ n : ℕ, (show X ⟶ X from F ^ n) ≫ s = s ∧
          g ⁻¹ᵁ V = (show X ⟶ X from F ^ n) ⁻¹ᵁ g ⁻¹ᵁ V := by
        intro n
        induction n with
        | zero => exact ⟨Category.id_comp _, rfl⟩
        | succ n ih =>
          rw [pow_succ]
          change ((show X ⟶ X from F) ≫ (show X ⟶ X from F ^ n)) ≫ s = s ∧
            g ⁻¹ᵁ V = ((show X ⟶ X from F) ≫ (show X ⟶ X from F ^ n)) ⁻¹ᵁ g ⁻¹ᵁ V
          rw [Category.assoc, ih.1, hs, Scheme.Hom.comp_preimage, ← ih.2, ← hF]
          exact ⟨rfl, rfl⟩
      refine ⟨m, hm, (h1 m).2, ?_⟩
      have e1 := Scheme.Hom.appLE_comp_appLE (show X ⟶ X from F ^ m) s ⊤ (g ⁻¹ᵁ V) (g ⁻¹ᵁ V) le_top
        (h1 m).2.le
      have e3 := e1.trans (appLE_congr_hom (h1 m).1 _ _ _ le_top)
      refine (congrArg (fun φ => φ.hom c) e3).trans ?_
      change (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom c = (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom c ^ _
      rw [← map_pow, hc']
  exact hle (Subring.mem_top f)
end GlobalTheory.SS.FrobField
