-- Prove2me | solution 1 for GlobalTheory.GelfandKazhdan.transpose_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:35.483802+00:00
-- url     : https://prove2.me/submissions/1f1cca6f-2af0-4ba6-a572-3c1699c3bb4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhausStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
import Theorems.Thm_GlobalTheory_GelfandKazhdan_invariant_of_anti
import Theorems.Thm_GlobalTheory_GelfandKazhdan_trGL_mul
import Theorems.Thm_GlobalTheory_SmGL_exists_open_normalised_subgroup_subset
import Theorems.Thm_GlobalTheory_T_matrix_conj_transpose_by_symmetric_taussky_zassenhaus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
noncomputable section
open GlobalTheory GlobalTheory.GelfandKazhdan
namespace GlobalTheory.GelfandKazhdan
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ)
    (hT : ∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ)
    (φ ψ : SB (GL n k)) (h : ∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) :
    T ψ = T φ := by
  have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => h x (trGL x) rfl)
  rw [e]
  refine invariant_of_anti trHomeo trGL_mul trGL_trGL (KO k n) SplitFlip.isOpen_KO
    SplitFlip.isCompact_KO (fun x hx => ?_) (exists_open_normalised_subgroup_subset k n)
    (fun x => ?_) T hT φ
  · obtain ⟨h1, h2⟩ := (SplitFlip.mem_KO_iff _).1 hx
    exact (SplitFlip.mem_KO_iff _).2 ⟨fun i j => h1 j i, fun i j => h2 j i⟩
  · obtain ⟨P, ⟨s, rfl⟩, h1, h2⟩ := GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus k n x.val
    exact ⟨s, Units.ext h1, Units.ext h2⟩
end GlobalTheory.GelfandKazhdan
