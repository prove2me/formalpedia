-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.finite_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:05.150649+00:00
-- url     : https://prove2.me/submissions/a43f63d2-f641-43e9-8d04-51d129da4c47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (R : Submodule O A) (hR : R.FG)
    (a : O) (ha : a ≠ 0) : Finite {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ Ideal.span {a}) := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  haveI : Module.Finite O R := Module.Finite.iff_fg.2 hR
  set J : Submodule O R := Ideal.span {a} • (⊤ : Submodule O R) with hJ
  haveI hQ : Finite (R ⧸ J) := Submodule.finite_quotient_smul (Ideal.span {a}) (N := ⊤) Module.Finite.fg_top
  have hJle : ∀ N : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N}, J ≤ N.1.comap R.subtype := by
    intro N x hx
    rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul]
    exact N.2.2 _ y.2
  let φ : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} → Set (R ⧸ J) := fun N =>
    ((N.1.comap R.subtype).map J.mkQ : Set (R ⧸ J))
  refine Finite.of_injective φ ?_
  intro N N' h
  have h1 : (N.1.comap R.subtype).map J.mkQ = (N'.1.comap R.subtype).map J.mkQ := SetLike.coe_injective h
  have h2 := congrArg (Submodule.comap J.mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hJle N),
    sup_eq_right.2 (hJle N')] at h2
  have h3 := congrArg (Submodule.map R.subtype) h2
  rw [Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype,
    inf_eq_right.2 N.2.1, inf_eq_right.2 N'.2.1] at h3
  exact Subtype.ext h3
end GlobalTheory.UnitLemma.Desc
