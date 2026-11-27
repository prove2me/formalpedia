-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.IsFrobSS.iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:45.554907+00:00
-- url     : https://prove2.me/submissions/db8b2be2-2698-403e-aab5-4bca92154a9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
import Theorems.Thm_P2M_GlobalTheory_WeilDeligne_IsFrobSS___unique_f10a1346b496
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne
namespace IsFrobSS
theorem _root_.solution {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V} {ρ' : Weil h → End ℂ V'}
    {N' : End ℂ V'} {b : WDRep h V'} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N' b)
    (e : V ≃ₗ[ℂ] V') (hρ : ∀ g v, e (ρ g v) = ρ' g (e v)) (hN : ∀ v, e (N v) = N' (e v)) :
    a.Iso b := by
  have h1 : ∀ g, ρ' g = e.conjAlgEquiv ℂ (ρ g) := fun g => LinearMap.ext fun v => by
    simp [hρ]
  have h2 : IsFrobSS ρ' (a.transport e).N (a.transport e) := ⟨rfl, fun g => by
    rw [h1]
    refine ⟨(ha.2 g).1.map (e.conjAlgEquiv ℂ), ?_⟩
    have := (ha.2 g).2.map (e.conjAlgEquiv ℂ)
    rwa [map_sub] at this⟩
  refine ⟨e, fun g v => ?_, fun v => by rw [ha.1, hb.1, hN]⟩
  rw [← h2.ρ_unique hb]
  show _ = e.conjAlgEquiv ℂ (a.ρ g) (e v)
  simp
end IsFrobSS
end GlobalTheory.WeilDeligne
