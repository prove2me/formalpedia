-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.isOfFinOrder_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:53.46285+00:00
-- url     : https://prove2.me/submissions/d882a7f1-afc8-4291-b337-4be86e256d11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_bar
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
local notation "cc" => IsCMField.complexConj E
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (k : Eˣ) (h : ∀ w : HeightOneSpectrum (𝓞 E), (bar w).valuation E k = w.valuation E k) :
    IsOfFinOrder (k / Units.map (cc).toRingEquiv.toMonoidHom k) := by
  have e : ((k / Units.map (cc).toRingEquiv.toMonoidHom k : Eˣ) : E) = (k : E) / cc (k : E) := by simp
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((k : E) / cc (k : E)) fun w => by
    have := h w
    rw [val_bar] at this
    rw [map_div₀, ← this]
    exact div_self_le_one _
  obtain ⟨n, hn, h1⟩ := Embeddings.pow_eq_one_of_norm_eq_one E ℂ (x := (k : E) / cc (k : E)) (ha ▸ a.isIntegral_coe) fun σ => by
    rw [map_div₀, IsCMField.complexEmbedding_complexConj, norm_div, Complex.norm_conj, div_self (by simp)]
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.ext (by rw [Units.val_pow_eq_pow_val, e, h1, Units.val_one])⟩
end GlobalTheory.CMVal.ValEx
