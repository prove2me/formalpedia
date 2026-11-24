-- Prove2me | solution 1 for GlobalTheory.SatakeBound.exists_cosets_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:48.131687+00:00
-- url     : https://prove2.me/submissions/c17adbe7-382e-4a93-9c06-bc711ad60f38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_hermGL_injective
import Theorems.Thm_GlobalTheory_SatakeBound_exists_smul_hermGL
import Theorems.Thm_GlobalTheory_SatakeBound_apply_hermGL
import Theorems.Thm_GlobalTheory_SatakeBound_card_hermIdx
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
namespace GlobalTheory.SatakeBound
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (m : ℕ), ∃ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)), (∀ x ∈ KO k (Fin n), ∀ c ∈ S, x • c ∈ S) ∧ ∀ (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → ∑ c ∈ S, φ c.out = ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i) ^ a i := by
  intro k _ _ _ _ n m
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hq := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hfin : ∀ a : Fin n → ℕ, Finite (HermIdx p a) := fun a => Nat.finite_of_card_ne_zero (by
    rw [card_hermIdx hp]; positivity)
  let _ : ∀ a : Fin n → ℕ, Fintype (HermIdx p a) := fun a => Fintype.ofFinite _
  refine ⟨((Finset.piAntidiag Finset.univ m).sigma fun a => (Finset.univ : Finset (HermIdx p a))).map
    ⟨_, hermGL_injective hp⟩, fun x hx c hc => ?_, fun γ φ h => ?_⟩
  · obtain ⟨⟨a, c⟩, h, rfl⟩ := Finset.mem_map.1 hc
    obtain ⟨a', c', h1, h2⟩ := exists_smul_hermGL hp hx a c
    refine Finset.mem_map.2 ⟨⟨a', c'⟩, ?_, h2⟩
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true] at h ⊢
    exact h1.trans h
  · rw [Finset.sum_map, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Function.Embedding.coeFn_mk, apply_hermGL hp h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, card_hermIdx hp, mul_pow, Finset.prod_mul_distrib]
    push_cast
    rfl
end GlobalTheory.SatakeBound
