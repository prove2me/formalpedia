-- Prove2me | solution 1 for GlobalTheory.SatakeBound.apply_hermGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:11.918803+00:00
-- url     : https://prove2.me/submissions/1f60bdda-9215-4ebd-9df2-3f71789d3c13

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
import Theorems.Thm_GlobalTheory_SatakeBound_val_hermGL
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_nabs_eq_zpow
import Theorems.Thm_GlobalTheory_SmGL_mem_borel
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser
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
theorem _root_.solution (hp : Irreducible p) {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (h : IsBorelSph k γ φ)
    (a : Fin n → ℕ) (c : HermIdx p a) :
    φ (hermGL hp a c : GL (Fin n) k ⧸ KO k (Fin n)).out = ∏ i, γ i ^ a i := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (hermGL hp a c)
  have h0 : (p : k) ≠ 0 := by simpa using hp.ne_zero
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have ho : ∀ m : ℕ, ord k (Units.mk0 _ h0 ^ m) = m := fun m => by
    have h1 := GlobalTheory.LGrp.nabs_eq_zpow (Units.mk0 _ h0 ^ m)
    have h2 : nabs k (Units.mk0 _ h0 ^ m) = nabs k (Units.mk0 _ h0) ^ m := by simp [nabs]
    rw [h2, nabs_uniformiser hp (x := Units.mk0 _ h0) rfl, inv_pow, ← zpow_natCast, ← _root_.zpow_neg] at h1
    exact neg_injective (zpow_right_injective₀ (by positivity) hq.ne' h1).symm
  rw [hy, h.1 _ _ y.2, h.2 _ ((mem_borel k).2 fun i j hij => ?_) (fun i => Units.mk0 _ h0 ^ a i) fun i => ?_]
  · simp only [ho, zpow_natCast]
  · simp [val_hermGL, hermMat_gt c hij]
  · simp [val_hermGL, hermMat_diag]
    rfl
end GlobalTheory.SatakeBound
