-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.exists_ofMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:45.454859+00:00
-- url     : https://prove2.me/submissions/50b15f3b-09ef-41f5-aea5-9ec92d87f380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_exists_rep
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
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
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (x : WD h) : ∃ (n : ℕ) (ρ : Weil h →* GL (Fin n) ℂ)
    (N : Matrix (Fin n) (Fin n) ℂ) (h1 : _) (h2 : _) (h3 : _) (h4 : _),
    mk (WDRep.ofMatrix ρ N h1 h2 h3 h4) = x := by
  obtain ⟨n, a, rfl⟩ := exists_rep x
  refine ⟨n, a.toGL, LinearMap.toMatrix' a.N, a.smooth.of_le fun σ hσ => ?_, fun σ => ?_, ?_,
    fun σ => ?_, sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩⟩
  · ext : 1
    simp [hσ]
  · simpa using a.semisimple σ
  · exact a.nilpotent.map
      (LinearMap.toMatrixAlgEquiv' : End ℂ (Fin n → ℂ) ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
  · have := congrArg
      (LinearMap.toMatrixAlgEquiv' : End ℂ (Fin n → ℂ) ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (a.comm σ)
    rw [map_mul, map_smul, map_mul] at this
    exact this
  · show Matrix.toLin' (LinearMap.toMatrix' (a.ρ σ)) v = a.ρ σ v
    rw [Matrix.toLin'_toMatrix']
  · show Matrix.toLin' (LinearMap.toMatrix' a.N) v = a.N v
    rw [Matrix.toLin'_toMatrix']
end GlobalTheory.WeilDeligne.WD
