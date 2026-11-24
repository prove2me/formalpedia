-- Prove2me | solution 1 for GlobalTheory.QNorm.mem_sUnits_sup_of_local_orders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:47.360985+00:00
-- url     : https://prove2.me/submissions/64304ed1-ea30-4709-95ef-8924531d1a64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenNormsOfUnitNonsquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Theorems.Thm_GlobalTheory_QNorm_finite_valuation_ne_one
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (N : Subgroup Fˣ) (t : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ n ∈ N,
      v.valuation F (n : F) = v.valuation F (t : F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (n : F) = 1) :
    t ∈ sUnits F S ⊔ N := by
  classical
  choose! n hnN hnv hnw using h
  set T := (finite_valuation_ne_one F t).toFinset \ S with hT
  have hP : ∏ v ∈ T, n v ∈ N :=
    N.prod_mem (fun v hv => hnN v (Finset.mem_sdiff.1 hv).2)
  have hU : t * (∏ v ∈ T, n v)⁻¹ ∈ sUnits F S := by
    rw [mem_sUnits]
    intro w hw
    have key : w.valuation F ((∏ v ∈ T, n v : Fˣ) : F) = w.valuation F (t : F) := by
      rw [Units.coe_prod, map_prod]
      by_cases hwT : w ∈ T
      · rw [Finset.prod_eq_single w]
        · exact hnv w hw
        · intro v hv hne
          exact hnw v (Finset.mem_sdiff.1 hv).2 w hw hne.symm
        · intro h'; exact absurd hwT h'
      · have h1 : w.valuation F (t : F) = 1 := by
          by_contra hc
          exact hwT (Finset.mem_sdiff.2 ⟨by simpa using hc, hw⟩)
        rw [h1]
        refine Finset.prod_eq_one (fun v hv => ?_)
        exact hnw v (Finset.mem_sdiff.1 hv).2 w hw (fun e => hwT (e ▸ hv))
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, key]
    exact mul_inv_cancel₀ (by simp)
  have : t = t * (∏ v ∈ T, n v)⁻¹ * ∏ v ∈ T, n v := by group
  rw [this]
  exact Subgroup.mul_mem_sup hU hP
end GlobalTheory.QNorm
