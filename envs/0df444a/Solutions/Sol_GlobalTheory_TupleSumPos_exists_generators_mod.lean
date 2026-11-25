-- Prove2me | solution 1 for GlobalTheory.TupleSumPos.exists_generators_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:46.642963+00:00
-- url     : https://prove2.me/submissions/e56707b2-c2d9-4e93-9eca-95c2d22f248a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorsLattice
import Theorems.Thm_GlobalTheory_TupleSumPos_finrank_fibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.TupleSumPos
namespace GlobalTheory.TupleSumPos
theorem _root_.solution (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (m : O) [Finite (O ⧸ Ideal.span {m})] (r : ℕ)
    (hr : Module.finrank O M = r) :
    ∃ e : Fin r → M, ∀ x : M, ∃ (c : Fin r → O) (y : M), x = ∑ k, c k • e k + m • y := by
  set I : Ideal O := Ideal.span {m} with hI
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  have hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1) :=
    TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective
  have hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y := fun x => by
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩
  choose e he using fun k => hs (B k)
  have hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) =
      ∑ k, Ideal.Quotient.mk I (c k) • B k := fun c => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  refine ⟨e, fun x => ?_⟩
  choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)
  obtain ⟨y, hy⟩ := (hk (x - ∑ k, c k • e k)).1 (by
    rw [map_sub, hc]
    simp only [hc']
    rw [B.sum_repr, sub_self])
  exact ⟨c, y, by rw [← hy]; abel⟩
end GlobalTheory.TupleSumPos
