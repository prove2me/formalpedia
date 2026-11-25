-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finite_of_finite_quotient_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:55.592267+00:00
-- url     : https://prove2.me/submissions/59e3d367-be5b-43f1-9dce-8e5a9d2eba8b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) [IsPrecomplete I A] [IsHausdorff I M]
    [Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))] : Module.Finite A M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := M ⧸ (I • ⊤ : Submodule A M))
  choose m hm using fun i => Submodule.Quotient.mk_surjective _ (g i)
  have : IsPrecomplete I (Fin n → A) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : A, ∀ k, u k i ≡ L [SMOD (I ^ k • ⊤ : Submodule A A)] := fun i =>
      IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => by
        have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := A) (φ := fun _ => A) i)
          (SModEq.sub_mem.1 (hu hab))
        rw [Submodule.map_smul''] at this
        exact SModEq.sub_mem.2 (Submodule.smul_mono le_rfl le_top this)
    choose L hL using h1
    refine ⟨L, fun k => SModEq.sub_mem.2 ?_⟩
    rw [← Finset.univ_sum_single (u k - L)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h2 : u k i - L i ∈ I ^ k := by simpa using SModEq.sub_mem.1 (hL i k)
    have h3 : (Pi.single i ((u k - L) i) : Fin n → A) = (u k i - L i) • Pi.single i 1 := by
      rw [← Pi.single_smul']; simp
    rw [h3]
    exact Submodule.smul_mem_smul h2 trivial
  refine Module.Finite.of_surjective (Fintype.linearCombination A m)
    (surjective_of_mkQ_comp_surjective (I := I) ?_)
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, by simp [hm]⟩
end GlobalTheory.FormalIsogeny
