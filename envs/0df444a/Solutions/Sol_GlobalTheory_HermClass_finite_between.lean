-- Prove2me | solution 1 for GlobalTheory.HermClass.finite_between
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:21.350105+00:00
-- url     : https://prove2.me/submissions/dad57bcc-7051-4c39-aa30-d1ba0c35041d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
namespace GlobalTheory.HermClass
theorem _root_.solution {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (L₀ : Submodule ℤ V) (h₀ : L₀.FG) {M : ℤ} (hM : M ≠ 0) :
    {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀}.Finite := by
  classical
  have hcast : ∀ x : V, (M : E) • x = M • x := fun x => Int.cast_smul_eq_zsmul E M x
  let μ : V →ₗ[ℤ] V := M • LinearMap.id
  have hμ : ∀ x, μ x = M • x := fun x => rfl
  have hinj : Function.Injective μ := by
    intro x y hxy
    rw [hμ, hμ, ← hcast, ← hcast] at hxy
    exact smul_right_injective V (Int.cast_ne_zero.mpr hM) hxy
  let L' := L₀.comap μ
  have hL'fg : L'.FG :=
    Submodule.fg_of_fg_map_injective μ hinj (h₀.of_le (Submodule.map_comap_le μ L₀))
  let K : Submodule ℤ L' := L₀.comap L'.subtype
  have : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hL'fg
  have : Finite (L' ⧸ K) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
    rw [Submonoid.smul_def, ← LinearMap.map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact x.2
  have : Finite (Submodule ℤ (L' ⧸ K)) :=
    Finite.of_injective (fun P : Submodule ℤ (L' ⧸ K) => (P : Set (L' ⧸ K))) SetLike.coe_injective
  let g : Submodule ℤ V → Submodule ℤ (L' ⧸ K) := fun L => (L.comap L'.subtype).map K.mkQ
  have key : ∀ L : Submodule ℤ V, L ∈ {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀} →
      ((g L).comap K.mkQ).map L'.subtype = L := by
    rintro L ⟨hle, hM'⟩
    have hK : K ≤ L.comap L'.subtype := fun x hx => hle hx
    have hL' : L ≤ L' := fun x hx => show μ x ∈ L₀ by rw [hμ, ← hcast]; exact hM' x hx
    simp only [g, Submodule.comap_map_mkQ, sup_eq_right.mpr hK, Submodule.map_comap_subtype,
      inf_eq_right.mpr hL']
  refine Set.Finite.of_finite_image (Set.toFinite _) (f := g) ?_
  intro L₁ h₁ L₂ h₂ h12
  exact (key L₁ h₁).symm.trans
    ((congrArg (fun P => (P.comap K.mkQ).map L'.subtype) h12).trans (key L₂ h₂))
end GlobalTheory.HermClass
