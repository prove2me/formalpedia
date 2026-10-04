-- Prove2me | solution 1 for HunterPDE.Elliptic.fredholm_alternative_operator
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:31:41.62086+00:00
-- url     : https://prove2.me/submissions/d0cdd293-fa85-4e73-9c64-084c5e167fb4

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_Fredholm

open scoped InnerProductSpace

namespace HunterPDE.Elliptic

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- `range T† ⊆ (ker T)ᗮ`. -/
lemma range_adjoint_le_core (T : H →L[𝕜] H) :
    LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) ≤
      (LinearMap.ker (T : H →ₗ[𝕜] H))ᗮ := by
  rintro _ ⟨x, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  simp only [ContinuousLinearMap.coe_coe] at hu ⊢
  rw [ContinuousLinearMap.adjoint_inner_right, hu, inner_zero_left]

/-- If `range T` is closed then `(ker T)ᗮ ⊆ range T†` (a Hilbert-space closed range theorem,
proved with the open mapping theorem for `T : (ker T)ᗮ → range T`). -/
lemma orthogonal_ker_le_range_adjoint_core (T : H →L[𝕜] H)
    (hR : IsClosed (LinearMap.range (T : H →ₗ[𝕜] H) : Set H)) :
    (LinearMap.ker (T : H →ₗ[𝕜] H))ᗮ ≤
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) := by
  set K : Submodule 𝕜 H := LinearMap.ker (T : H →ₗ[𝕜] H) with hKdef
  set R : Submodule 𝕜 H := LinearMap.range (T : H →ₗ[𝕜] H) with hRdef
  have : CompleteSpace R := hR.completeSpace_coe
  have hKc : IsClosed (K : Set H) := T.isClosed_ker
  have : CompleteSpace K := hKc.completeSpace_coe
  have : CompleteSpace Kᗮ := (Submodule.isClosed_orthogonal K).completeSpace_coe
  have hTmem : ∀ v : H, T v ∈ R := fun v => LinearMap.mem_range_self (T : H →ₗ[𝕜] H) v
  have hPK : ∀ v : H, T (K.starProjection v) = 0 := fun v => by
    have hm := K.starProjection_apply_mem v
    have hm' := LinearMap.mem_ker.mp hm
    simpa using hm'
  -- the restricted map `S : Kᗮ → R`
  let S : Kᗮ →L[𝕜] R := (T.comp Kᗮ.subtypeL).codRestrict R (fun x => hTmem x)
  have hS_apply : ∀ x : Kᗮ, (S x : H) = T x := fun x => rfl
  have hker : S.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hTx : T x = 0 := by
      have := congrArg Subtype.val hx
      simpa [hS_apply] using this
    have hxK : (x : H) ∈ K := LinearMap.mem_ker.mpr (by simpa using hTx)
    have hmem : (x : H) ∈ K ⊓ Kᗮ := ⟨hxK, x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hsurj : S.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := hy
    refine ⟨⟨v - K.starProjection v, K.sub_starProjection_mem_orthogonal v⟩, ?_⟩
    apply Subtype.ext
    simp [hS_apply, map_sub, hPK]
  let S' := ContinuousLinearEquiv.ofBijective S hker hsurj
  intro y hy
  let ℓ : H →L[𝕜] 𝕜 :=
    (innerSL 𝕜 y).comp (Kᗮ.subtypeL.comp ((S'.symm : R →L[𝕜] Kᗮ).comp R.orthogonalProjectionOnto))
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm ℓ, ?_⟩
  apply ext_inner_right 𝕜
  intro v
  simp only [ContinuousLinearMap.coe_coe]
  rw [ContinuousLinearMap.adjoint_inner_left, InnerProductSpace.toDual_symm_apply]
  have hTv : R.orthogonalProjectionOnto (T v) = ⟨T v, hTmem v⟩ :=
    R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T v, hTmem v⟩
  have hS'symm : S'.symm ⟨T v, hTmem v⟩ =
      ⟨v - K.starProjection v, K.sub_starProjection_mem_orthogonal v⟩ := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [S', hS_apply, map_sub, hPK]
  have hℓ : ℓ (T v) = ⟪y, ((S'.symm (R.orthogonalProjectionOnto (T v)) : Kᗮ) : H)⟫_𝕜 := by
    simp [ℓ]
  rw [hℓ, hTv, hS'symm]
  simp only [inner_sub_right]
  rw [Submodule.inner_left_of_mem_orthogonal (K.starProjection_apply_mem v) hy, sub_zero]

end HunterPDE.Elliptic

theorem solution {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (T : H →L[𝕜] H) (hT : HunterPDE.Elliptic.IsFredholm T)
    (hind : HunterPDE.Elliptic.index T = 0) :
    (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊥ ∧
      LinearMap.ker (T : H →ₗ[𝕜] H) = ⊥ ∧
      LinearMap.range (T : H →ₗ[𝕜] H) = ⊤ ∧
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊤) ∨
    (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) ≠ ⊥ ∧
      FiniteDimensional 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) ∧
      FiniteDimensional 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) ∧
      Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) =
        Module.finrank 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) ∧
      LinearMap.range (T : H →ₗ[𝕜] H) =
        (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H))ᗮ ∧
      LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) =
        (LinearMap.ker (T : H →ₗ[𝕜] H))ᗮ) := by
  obtain ⟨hKfin, hR, hRfin⟩ := hT
  have hkerAdj : LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) =
      (LinearMap.range (T : H →ₗ[𝕜] H))ᗮ := T.orthogonal_range.symm
  have hrangeT : LinearMap.range (T : H →ₗ[𝕜] H) =
      (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H))ᗮ := by
    rw [hkerAdj, Submodule.orthogonal_orthogonal_eq_closure, hR.submodule_topologicalClosure_eq]
  have hrangeAdj : LinearMap.range (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) =
      (LinearMap.ker (T : H →ₗ[𝕜] H))ᗮ :=
    le_antisymm (HunterPDE.Elliptic.range_adjoint_le_core T)
      (HunterPDE.Elliptic.orthogonal_ker_le_range_adjoint_core T hR)
  have hAfin : FiniteDimensional 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) := by
    rw [hkerAdj]; exact hRfin
  have hfin_eq : Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) =
      Module.finrank 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H)) := by
    have h := hind
    unfold HunterPDE.Elliptic.index at h
    rw [hkerAdj]
    have h' : (Module.finrank 𝕜 (LinearMap.ker (T : H →ₗ[𝕜] H)) : ℤ) =
        Module.finrank 𝕜 (LinearMap.range (T : H →ₗ[𝕜] H))ᗮ := by linarith
    exact_mod_cast h'
  by_cases hadj : LinearMap.ker (ContinuousLinearMap.adjoint T : H →ₗ[𝕜] H) = ⊥
  · left
    have hK : LinearMap.ker (T : H →ₗ[𝕜] H) = ⊥ := by
      rw [← Submodule.finrank_eq_zero, hfin_eq, hadj, finrank_bot]
    refine ⟨hadj, hK, ?_, ?_⟩
    · rw [hrangeT, hadj, Submodule.bot_orthogonal_eq_top]
    · rw [hrangeAdj, hK, Submodule.bot_orthogonal_eq_top]
  · right
    exact ⟨hadj, hKfin, hAfin, hfin_eq, hrangeT, hrangeAdj⟩

#print axioms solution
