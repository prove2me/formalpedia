-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.VirtualTrace.trace_listSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:47:33.265711+00:00
-- url     : https://prove2.me/submissions/cb02bba0-6c02-4098-9ef6-ab45b739cfed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultiplicativeVirtualCharacter
import Theorems.Thm_GlobalTheory_WeilDeligne_VirtualTrace_trace_std
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.VirtualTrace
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne.VirtualTrace
theorem _root_.solution (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : Subsingleton (Fin (listSum h []).1 → ℂ) := by
      show Subsingleton (Fin 0 → ℂ); infer_instance
    have hz : (listSum h []).2.ρ σ ^ k = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (trace_std (x.2.sum (listSum h L).2) σ k).trans ?_
    rw [WDRep.sum_ρ, ← ih]
    have : ((x.2.ρ σ).prodMap ((listSum h L).2.ρ σ)) ^ k = (x.2.ρ σ ^ k).prodMap ((listSum h L).2.ρ σ ^ k) :=
      (map_pow (LinearMap.prodMapRingHom ℂ _ _) (x.2.ρ σ, (listSum h L).2.ρ σ) k).symm
    rw [this, LinearMap.trace_prodMap']
end GlobalTheory.WeilDeligne.VirtualTrace
