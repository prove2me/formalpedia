-- Prove2me | solution 1 for GlobalTheory.CompleteJoin.exists_subring_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:27.163275+00:00
-- url     : https://prove2.me/submissions/6903c906-4587-4ccb-93c3-eeade866dbab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompleteNormalSubringJoin
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_HasTriangularWeight_smul
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.CompleteJoin
variable {C : Type} [NormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]
namespace GlobalTheory.CompleteJoin
theorem _root_.solution {R V : Type} [CommRing R] [CommRing V] {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] V] [Module.Finite ℤ_[p] V] (f : R →+* C) (g : V →+* C) (φ : ℤ_[p] →+* R)
    (h : f.comp φ = g.comp (algebraMap ℤ_[p] V)) :
    ∃ (S : Subring C) (ψ : R →+* S), ψ.Finite ∧ (∀ a, (ψ a : C) = f a) ∧ ∀ a, g a ∈ S := by
  letI := f.toAlgebra
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := V)
  have hint : ∀ x : V, IsIntegral R (g x) := fun x =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x).map_of_comp_eq φ g h
  have hfin : Module.Finite R (Algebra.adjoin R (g '' s)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image g)
      (by rintro _ ⟨x, -, rfl⟩; exact hint x)
  refine ⟨(Algebra.adjoin R (g '' s)).toSubring, algebraMap R (Algebra.adjoin R (g '' s)),
    (RingHom.finite_algebraMap (B := Algebra.adjoin R (g '' s))).2 hfin, fun _ => rfl, fun a => ?_⟩
  have ha : a ∈ Submodule.span ℤ_[p] (s : Set V) := hs ▸ Submodule.mem_top
  change g a ∈ Algebra.adjoin R (g '' s)
  induction ha using Submodule.span_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    have : g (algebraMap ℤ_[p] V c) = algebraMap R C (φ c) := (RingHom.congr_fun h c).symm
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
end GlobalTheory.CompleteJoin
