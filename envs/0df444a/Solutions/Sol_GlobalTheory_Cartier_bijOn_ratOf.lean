-- Prove2me | solution 1 for GlobalTheory.Cartier.bijOn_ratOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:44.146859+00:00
-- url     : https://prove2.me/submissions/cf72bd65-2f96-4203-bb61-caf304317c1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_germ
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_ne_zero
import Theorems.Thm_GlobalTheory_Cartier_ext_germK
import Theorems.Thm_GlobalTheory_Cartier_germK_eq_mul_ratOf

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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable [IsIntegral X]
namespace GlobalTheory.Cartier
theorem _root_.solution {L : LB X} (hL : L.IsLB) {s : L.Sec} (hs : IsRegularSec s) (V : X.Opens)
    [Nonempty V] : Set.BijOn (ratOf hL s V) (secOn L V) (ratSecs s V) := by
  refine ⟨fun t ht i _ => ⟨t i, germK_eq_mul_ratOf hL hs V ht i⟩, fun t ht t' ht' e => ?_,
    fun h hh => ?_⟩
  · funext i
    refine ext_germK fun hη => ?_
    have : Nonempty (V ⊓ L.U i : X.Opens) := ⟨⟨_, hη⟩⟩
    exact (germK_eq_mul_ratOf hL hs V ht i).trans
      ((congrArg _ e).trans (germK_eq_mul_ratOf hL hs V ht' i).symm)
  · have ex : ∀ i, ∃ a : Γ(X, V ⊓ L.U i), ∀ hη : genericPoint X ∈ V ⊓ L.U i,
        (X.presheaf.germ _ _ hη).hom a = (X.presheaf.germ _ _ hη.2).hom (s.f i) * h := by
      intro i
      by_cases hi : Nonempty (V ⊓ L.U i : X.Opens)
      · obtain ⟨a, ha⟩ := hh i
        exact ⟨a, fun hη => ha.trans (congrArg (· * h) (germ_resG _ _ hη _))⟩
      · exact ⟨0, fun hη => (hi ⟨⟨_, hη⟩⟩).elim⟩
    choose t ht using ex
    have hts : t ∈ secOn L V := fun i j => ext_germK fun hη => by
      have hm' : genericPoint X ∈ L.U i ⊓ L.U j := ⟨hη.1.2, hη.2⟩
      have e₂ := congrArg (X.presheaf.germ _ _ hm').hom (s.compat i j)
      rw [map_mul, germ_resG, germ_resG] at e₂
      rw [map_mul, germ_resG, germ_resG, germ_resG, ht, ht, ← mul_assoc]
      exact congrArg (· * h) e₂
    refine ⟨t, hts, ?_⟩
    have hm : genericPoint X ∈ V ⊓ L.U (genericChart hL) :=
      ⟨genericPoint_mem V, mem_genericChart hL⟩
    have hne : @id X.functionField
        ((X.presheaf.germ _ _ (mem_genericChart hL)).hom (s.f (genericChart hL))) ≠ 0 :=
      nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 (hs _) _ _)
    have key : ∀ b : X.functionField, b ≠ 0 → b * h * b⁻¹ = h := fun b hb => by field_simp
    exact (congrArg (· * _) (ht _ hm)).trans (key _ hne)
end GlobalTheory.Cartier
