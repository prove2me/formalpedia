-- Prove2me | solution 1 for GroundTheory.Global.eq_decompositionToLocal_arithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:40.655576+00:00
-- url     : https://prove2.me/submissions/de2b322f-420b-480b-bd81-597b39588071

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
import Theorems.Thm_GroundTheory_Global_isArithFrobAt_iff_decompositionToLocal
import Theorems.Thm_GroundTheory_Global_natCard_inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (hτ : ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
      τ x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L]) :
    τ = decompositionToLocal v w (arithFrobAtDecomposition w) := by
  obtain ⟨σ, rfl⟩ := (decompositionToLocal_bijective v w).2 τ
  congr 1
  have hσ : IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal :=
    (isArithFrobAt_iff_decompositionToLocal v w σ).2 hτ
  have hmem := hσ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal)
  have hbot : w.asIdeal.inertia Gal(L/K) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ ((natCard_inertia v w).trans he)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact Subtype.ext hmem
end GroundTheory.Global
