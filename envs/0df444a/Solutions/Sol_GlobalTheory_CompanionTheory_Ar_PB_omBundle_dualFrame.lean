-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.omBundle_dualFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:01:01.798672+00:00
-- url     : https://prove2.me/submissions/0070a06e-b332-496d-a192-aff14ce67abb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_mem_V_iff_omBundle
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_mem_span_basis_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_restrict_isVBOn
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_lat_restrict_comap_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S x) (τ : CMType H) (q : Cpt 𝔐.ξ) {φ : Fin D.q → Module.Dual Ω (𝔐.Vgen (.inr τ))}
    (hφ : (omBundle 𝔐 τ).IsFrameAt φ q) :
    (∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, φ a (v b) = if a = b then 1 else 0) ∧
    ∀ v : Fin D.q → 𝔐.Vgen (.inr τ), (∀ a b, φ a (v b) = if a = b then 1 else 0) →
      (𝔐.V (.inr τ)).IsFrameAt (fun b => (v b : 𝔐.Li)) q := by
  obtain ⟨hres, hmap⟩ := Lat.restrict_isVBOn _ _ _ _ _ _ _ _ (𝔐.vb (.inr τ))
  obtain ⟨U, hU, b, hb, hf⟩ := hres q trivial
  let B : Module.Basis (Fin D.q) Ω (𝔐.Vgen (.inr τ)) := Module.Basis.mk (hf q trivial hU).1 hb.ge
  haveI := Module.Finite.of_basis B
  have hrk : Module.finrank Ω (𝔐.Vgen (.inr τ)) = D.q := by simpa using Module.finrank_eq_card_basis B
  constructor
  · let C := basisOfLinearIndependentOfCardEqFinrank' φ hφ.1 (by simp [Subspace.dual_finrank_eq, hrk])
    have hC : ∀ a, C a = φ a := fun a => by simp [C]
    refine ⟨fun b => (Module.evalEquiv Ω _).symm (C.coord b), fun a b => ?_⟩
    rw [Module.apply_evalEquiv_symm_apply, ← hC, Module.Basis.coord_apply, C.repr_self, Finsupp.single_apply]
  · intro v hv
    have hli : LinearIndependent Ω v := LinearIndependent.of_pairwise_dual_eq_zero_one v φ
      (fun a b hab => (hv a b).trans (if_neg hab)) (fun a => by rw [hv, if_pos rfl])
    let C := basisOfLinearIndependentOfCardEqFinrank' v hli (by simp [hrk])
    have hC : ⇑C = v := by simp [C]
    have hr : ∀ e a, C.repr e a = φ a e := fun e a => by
      conv_rhs => rw [← C.sum_repr e]
      simp [hC, hv]
    refine ⟨hli.map' (𝔐.Vgen (.inr τ)).subtype (Submodule.ker_subtype _), ?_⟩
    have key : ∀ e : 𝔐.Vgen (.inr τ), (e : 𝔐.Li) ∈ 𝔐.V (.inr τ) q ↔
        e ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range v) := fun e => by
      rw [← hC, LatDual.mem_span_basis_iff, mem_V_iff_omBundle, hφ.2]
      refine ⟨fun h a => hr e a ▸ h _ (Submodule.subset_span ⟨a, rfl⟩), fun h ψ hψ => ?_⟩
      induction hψ using Submodule.span_induction with
      | mem ψ hψ => obtain ⟨a, rfl⟩ := hψ; exact hr e a ▸ h a
      | zero => simp
      | add ψ ψ' _ _ h1 h2 => simpa using add_mem h1 h2
      | smul t ψ _ h1 => exact mul_mem t.2 h1
    refine le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)
    · have he' : e ∈ _ := (hmap q trivial).ge he
      obtain ⟨e, -, rfl⟩ := Submodule.mem_map.1 he'
      have h2 := (key e).1 he
      rwa [← lat_restrict_comap_span] at h2
    · rintro _ ⟨b, rfl⟩
      exact (key _).2 (Submodule.subset_span ⟨b, rfl⟩)
end GlobalTheory.CompanionTheory.Ar.PB
