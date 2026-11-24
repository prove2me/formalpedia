-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.UnitaryConv.conv_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:00:01.704813+00:00
-- url     : https://prove2.me/submissions/286dfdad-d0cc-4263-b50c-5b463c4a1328

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_mk_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_eq_of_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_rep_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv
theorem _root_.solution {G' : Type} [Group G'] (φ : G' →* G) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {l : G → ℝ}
    (hΓ : ∀ γ ∈ Γ', φ γ ∈ Γ) (hP : ∀ γ ∈ Γ', φ γ ∈ P → γ ∈ P')
    (hl : ∀ γ ∈ Γ, γ ∈ P → ∀ g, l (γ * g) = l g) (hc : Conv Γ P l) :
    Conv Γ' P' fun g => l (φ g) := by
  intro g'
  have hinj : Function.Injective (fun q' : Cos P' Γ' =>
      (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ)) := by
    intro q₁ q₂ h
    have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) _ _).mp h
    apply cos_eq_of_rep
    have hmem : rep q₂ * (rep q₁)⁻¹ ∈ Γ' :=
      Γ'.mul_mem (Quotient.out q₂).2 (Γ'.inv_mem (Quotient.out q₁).2)
    refine hP _ hmem ?_
    rw [map_mul, map_inv]
    exact h'
  refine ((hc (φ g')).comp_injective hinj).congr fun q' => ?_
  obtain ⟨p, hpΓ, hpP, hp⟩ := rep_mk (P := P) (Γ := Γ) ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩
  show Real.exp (l (rep (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ) * φ g')) =
    Real.exp (l (φ (rep q' * g')))
  rw [hp, map_mul, mul_assoc, hl p hpΓ hpP]
end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
