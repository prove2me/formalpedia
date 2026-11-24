-- Prove2me | solution 1 for GlobalTheory.KS.exists_dual_family_mod_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:53.315642+00:00
-- url     : https://prove2.me/submissions/ddfe304a-8262-40d8-b42a-03517955fb04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (B : Submodule K V) (g : ℕ) (φ : Fin g → V)
    (h : ∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0) :
    ∃ β : Fin g → Module.Dual K V, (∀ b, B ≤ LinearMap.ker (β b)) ∧
      ∀ b a, β b (φ a) = if a = b then 1 else 0 := by
  classical

  have hli : LinearIndependent K (fun a => B.mkQ (φ a)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : B.mkQ (∑ a, c a • φ a) = 0 := by
      simpa [map_sum, map_smul] using hc
    have hc0 := h c ((Submodule.Quotient.mk_eq_zero B).mp h0)
    intro i
    simp [hc0]

  let e := Module.Basis.span hli
  choose ext hext using fun b => LinearMap.exists_extend (e.coord b)
  refine ⟨fun b => (ext b).comp B.mkQ, fun b x hx => ?_, fun b a => ?_⟩
  · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero B).mpr hx]
  · have hmem : B.mkQ (φ a) ∈ Submodule.span K (Set.range fun a => B.mkQ (φ a)) :=
      Submodule.subset_span ⟨a, rfl⟩
    have he : (⟨B.mkQ (φ a), hmem⟩ : Submodule.span K (Set.range fun a => B.mkQ (φ a))) = e a :=
      (Module.Basis.span_apply hli a).symm
    have hb := LinearMap.congr_fun (hext b) ⟨B.mkQ (φ a), hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hb
    rw [LinearMap.comp_apply, hb, he, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
end GlobalTheory.KS
