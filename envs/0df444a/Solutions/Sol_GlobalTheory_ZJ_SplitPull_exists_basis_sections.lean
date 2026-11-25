-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.exists_basis_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:20:03.581109+00:00
-- url     : https://prove2.me/submissions/0db1939a-8b81-4103-812e-1135a5e0ba16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_exists_basis_pushout

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
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
namespace GlobalTheory.ZJ.SplitPull
theorem _root_.solution {K K' : Type} [Field K] [Field K'] (f : Sp K' ⟶ Sp K) :
    ∃ (J : Type) (e : J → Γ(Sp K', ⊤)), ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (iX : X ⟶ Sp K) (iY : Y ⟶ Sp K'),
      IsPullback g iY iX f →
      (∀ U : X.Opens, IsAffineOpen U → ∀ u : Γ(Y, g ⁻¹ᵁ U), ∃ (s : Finset J) (x : J → Γ(X, U)),
        u = ∑ l ∈ s, (g.app U).hom (x l) * (iY.appLE ⊤ (g ⁻¹ᵁ U) le_top).hom (e l)) ∧
      ∀ (s : Finset J) (x : J → Γ(X, ⊤)), ∑ l ∈ s, g.appTop.hom (x l) * iY.appTop.hom (e l) = 0 →
        ∀ l ∈ s, x l = 0 := by
  have hR : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨J, e, he⟩ := exists_basis_pushout hR (f.appLE ⊤ ⊤ le_top)
  refine ⟨J, e, fun X Y g iX iY h => ?_⟩
  have po : ∀ U : X.Opens, IsAffineOpen U → _ := fun U hU => he _ _ _ _ _
    ((isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top
      le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
        (isAffineOpen_top _) hU))
  refine ⟨fun U hU u => ?_, fun s x hx l hl => ?_⟩
  · have := (po U hU).1 u
    rwa [Scheme.Hom.appLE_eq_app] at this
  · refine X.IsSheaf.section_ext fun y _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine ⟨U, le_top, hy, ?_⟩
    rw [map_zero]
    refine (po U hU).2 s (fun l => resG X le_top (x l)) ?_ l hl
    have := congrArg (resG Y (le_top : g ⁻¹ᵁ U ≤ ⊤)) hx
    rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    congr 1
    exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ U) => q.hom (x l)) (g.map_appLE le_rfl (homOfLE le_top).op)
end GlobalTheory.ZJ.SplitPull
