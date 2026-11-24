-- Prove2me | solution 1 for GlobalTheory.HolHom.differentiableOn_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:20.061854+00:00
-- url     : https://prove2.me/submissions/7534264c-20c8-4e74-929a-92565995c99e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_HolAt_precomp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_eq_of_forall_fderiv_eq
import Theorems.Thm_GlobalTheory_HolHom_differentiableAt_partial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}
namespace GlobalTheory.HolHom
theorem _root_.solution {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [FiniteDimensional ℂ V] {B : Set P} {y : P → (Sp ℂ ⟶ S)} {e : ∀ b, V → (Over.mk (y b) ⟶ G)}
    {e' : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : P × V => (e bz.1 bz.2).left))
    (hol' : IsHolTo (B ×ˢ Set.univ) (fun bz : P × (Fin g → ℂ) => (e' bz.1 bz.2).left))
    (hdiff : ∀ b ∈ B, ∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' b 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' b z).left) w v.left)
    {h : P → V →ₗ[ℂ] (Fin g → ℂ)} (hh : ∀ b ∈ B, ∀ z, e b z = e' b (h b z)) :
    DifferentiableOn ℂ (fun b => LinearMap.toContinuousLinearMap (h b)) B := by
  intro b₀ hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hslice : ∀ b ∈ B, HolAt (fun z => (e' b z).left) 0 := fun b hb =>
    (holAt_of_isHolTo hol' (z := (b, 0)) ⟨hb, trivial⟩).precomp (k := fun z => (b, z)) (by fun_prop)
  let s : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ) := {l | ∃ (U : G.left.Opens) (_ : ⊤ ≤ (e' b₀ 0).left ⁻¹ᵁ U) (f : Γ(G.left, U)),
    l = (fderiv ℂ (fun z => valAt' (e' b₀ z).left U f) 0).toLinearMap}
  have hs : Submodule.span ℂ s = ⊤ := Submodule.span_eq_top_of_ne_zero fun w hw => by
    by_contra hne
    refine hw (eq_of_forall_fderiv_eq (hslice b₀ hb₀) (hdiff b₀ hb₀) fun U hU f => ?_)
    rw [map_zero]
    by_contra h0
    exact hne ⟨_, ⟨U, hU, f, rfl⟩, h0⟩
  have key : ∀ l ∈ Submodule.span ℂ s, ∃ (m : P → (Fin g → ℂ) →L[ℂ] ℂ) (n : P → V →L[ℂ] ℂ),
      DifferentiableAt ℂ m b₀ ∧ DifferentiableAt ℂ n b₀ ∧ (m b₀).toLinearMap = l ∧
        ∀ᶠ b in 𝓝 b₀, ∀ z, m b (h b z) = n b z := by
    intro l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨U, hU, f, rfl⟩ := hl
      have hU' : ⊤ ≤ (e b₀ 0).left ⁻¹ᵁ U := by rw [hh b₀ hb₀, map_zero]; exact hU
      refine ⟨fun b => fderiv ℂ (fun z => valAt' (e' b z).left U f) 0,
        fun b => fderiv ℂ (fun z => valAt' (e b z).left U f) 0,
        differentiableAt_partial (hol' U f).1 (hol' U f).2 ⟨⟨hb₀, trivial⟩, hU⟩,
        differentiableAt_partial (hol U f).1 (hol U f).2 ⟨⟨hb₀, trivial⟩, hU'⟩, rfl, ?_⟩
      have h3 : ContinuousAt (fun b : P => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
      filter_upwards [h3.eventually ((hol' U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)] with b hb z
      have h1 : HasFDerivAt (fun t => valAt' (e' b t).left U f) (fderiv ℂ (fun t => valAt' (e' b t).left U f) 0)
          (LinearMap.toContinuousLinearMap (h b) 0) := by
        rw [map_zero]; exact ((hslice b hb.1.1 U hb.2).2 f).hasFDerivAt
      simp only [hh b hb.1.1]
      exact (congrArg (· z) (h1.comp 0 (LinearMap.toContinuousLinearMap (h b)).hasFDerivAt).fderiv).symm
    | zero => exact ⟨0, 0, differentiableAt_const _, differentiableAt_const _, rfl, .of_forall fun _ _ => rfl⟩
    | add l l' _ _ ih ih' =>
      obtain ⟨m, n, hm, hn, rfl, hmn⟩ := ih
      obtain ⟨m', n', hm', hn', rfl, hmn'⟩ := ih'
      refine ⟨m + m', n + n', hm.add hm', hn.add hn', rfl, ?_⟩
      filter_upwards [hmn, hmn'] with b h1 h2 z
      simp [h1 z, h2 z]
    | smul a l _ ih =>
      obtain ⟨m, n, hm, hn, rfl, hmn⟩ := ih
      refine ⟨a • m, a • n, hm.const_smul a, hn.const_smul a, rfl, ?_⟩
      filter_upwards [hmn] with b h1 z
      simp [h1 z]
  choose m n hm hn hm0 hmn using fun i : Fin g => key (LinearMap.proj i) (hs.ge trivial)
  let M : P → (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fun b => ContinuousLinearMap.pi fun i => m i b
  let N : P → V →L[ℂ] (Fin g → ℂ) := fun b => ContinuousLinearMap.pi fun i => n i b
  have hM : DifferentiableAt ℂ M b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b₀
      (differentiableAt_pi.2 hm)
  have hN : DifferentiableAt ℂ N b₀ :=
    (ContinuousLinearMap.piEquivL ℂ V (fun _ : Fin g => ℂ)).differentiableAt.comp b₀ (differentiableAt_pi.2 hn)
  have hM0 : M b₀ = (ContinuousLinearEquiv.refl ℂ (Fin g → ℂ) : _ →L[ℂ] _) := by
    ext1 w
    funext i
    exact congrArg (· w) (congrArg DFunLike.coe (hm0 i))
  have hinv : ∀ᶠ b in 𝓝 b₀, (M b).IsInvertible :=
    hM.continuousAt.eventually (hM0 ▸ (ContinuousLinearEquiv.refl ℂ (Fin g → ℂ)).nhds :)
  have hI : DifferentiableAt ℂ (fun b => (M b).inverse) b₀ :=
    ((hinv.self_of_nhds.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp b₀ hM
  refine (hI.clm_comp hN).congr_of_eventuallyEq ?_
  filter_upwards [hinv, eventually_all.2 hmn] with b hb hb'
  ext1 z
  have : M b (h b z) = N b z := funext fun i => hb' i z
  exact (hb.inverse_apply_eq.2 this.symm).symm
end GlobalTheory.HolHom
