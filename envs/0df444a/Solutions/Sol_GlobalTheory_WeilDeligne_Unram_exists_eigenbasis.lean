-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.Unram.exists_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:47:43.103804+00:00
-- url     : https://prove2.me/submissions/3fadaa53-d916-4d67-b73e-f26be4c77e5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.Unram
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.Unram
theorem _root_.solution {f : End ℂ V} (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin (finrank ℂ V)) ℂ V) (c : Fin (finrank ℂ V) → ℂ), ∀ i, f (b i) = c i • b i := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℂ (⋃ α, (f.eigenspace α : Set V))
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hspan, Submodule.span_iUnion, ← hf.iSup_eigenspace_eq_top]
    simp
  let b0 : Basis s ℂ V := Basis.mk hli htop
  let b := b0.reindex (b0.indexEquiv (finBasis ℂ V))
  have hb : ∀ i, ∃ α : ℂ, f (b i) = α • b i := by
    intro i
    have : b i ∈ s := by
      simp only [b, b0, Basis.reindex_apply, Basis.mk_apply]
      exact Subtype.prop _
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp (hs this)
    exact ⟨α, End.mem_eigenspace_iff.mp hα⟩
  choose c hc using hb
  exact ⟨b, c, hc⟩
end GlobalTheory.WeilDeligne.Unram
