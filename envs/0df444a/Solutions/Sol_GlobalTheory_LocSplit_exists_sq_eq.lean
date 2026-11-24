-- Prove2me | solution 1 for GlobalTheory.LocSplit.exists_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:06.511913+00:00
-- url     : https://prove2.me/submissions/cb664e29-191c-4089-9da7-7f7e0ebbecd8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_GlobalTheory_LocSplit_exists_val_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K) (hd : DenseRange ι)
  (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
include hd hv
namespace GlobalTheory.LocSplit
theorem _root_.solution (a : 𝓞 F) (ha : ∀ n : ℕ, ∃ m : ℤ, a - (m : 𝓞 F) ^ 2 ∈ p.asIdeal ^ n) :
    ∃ β : K, β ^ 2 = ι a := by
  haveI : T2Space K := IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx =>
    ⟨{y | valuation K y < valuation K x},
      (IsValuativeTopology.hasBasis_nhds_zero' K).mem_of_mem (by simpa using hx), by simp⟩
  have hc : IsCompact (Set.range fun x : 𝒪[K] => (x : K) ^ 2) :=
    isCompact_range (by fun_prop)
  have hm : ι a ∈ closure (Set.range fun x : 𝒪[K] => (x : K) ^ 2) := by
    rw [mem_closure_iff_nhds_basis (IsValuativeTopology.hasBasis_nhds' (ι a))]
    intro γ hγ
    obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
    obtain ⟨y, hy0, hy⟩ := exists_val_eq ι hd z (by simpa using hγ)
    have h0 : p.valuation F y ≠ 0 := by simpa using hy0
    obtain ⟨m, hm⟩ := ha ((WithZero.log (p.valuation F y)).natAbs + 1)
    refine ⟨_, ⟨(m : 𝒪[K]), rfl⟩, ?_⟩
    rw [← p.intValuation_le_pow_iff_mem, ← p.valuation_of_algebraMap (K := F)] at hm
    have h1 : p.valuation F (algebraMap (𝓞 F) F (a - (m : 𝓞 F) ^ 2)) < p.valuation F y := by
      refine lt_of_le_of_lt hm ?_
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_lt_exp]
      omega
    rw [← not_le, ← hv, not_le, hy] at h1
    rw [Set.mem_setOf_eq, Valuation.map_sub_swap]
    simpa using h1
  rw [hc.isClosed.closure_eq] at hm
  obtain ⟨β, hβ⟩ := hm
  exact ⟨β, hβ⟩
end GlobalTheory.LocSplit
