-- Prove2me | solution 1 for MasulloGRH.kernel_of_strict_LF_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:41:52.873289+00:00
-- url     : https://prove2.me/submissions/29a5f1bc-a58f-4f09-9a18-b459754ccb9e

import Theorems.Thm_MasulloGRH_limit_subspace_iff_bounded_lifting
import Theorems.Thm_MasulloGRH_bounded_lifting_strict_nuclear_quotient
import Theorems.Thm_MasulloGRH_frechet_of_closed_linear_embedding
import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv
import Theorems.Thm_MasulloGRH_nuclear_permanence

open MasulloGRH Set Topology

universe w

private theorem closed_stage (F G : Type w) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (u : F →ₗ[ℂ] G)
    (hu : IsClosedEmbedding u) (hG : IsFrechet G ∧ IsNuclear G) :
    IsFrechet F ∧ IsNuclear F := by
  classical
  let e := LinearEquiv.ofInjective u hu.injective
  let ec : F ≃L[ℂ] LinearMap.range u :=
    { e with
      continuous_toFun := hu.continuous.subtype_mk _
      continuous_invFun := by
        apply hu.isEmbedding.continuous_iff.mpr
        have he : u ∘ e.symm = (Subtype.val : LinearMap.range u → G) :=
          funext fun y => congrArg Subtype.val (e.apply_symm_apply y)
        change Continuous ((u : F → G) ∘ e.symm)
        rw [he]
        exact continuous_subtype_val }
  exact ⟨frechet_of_closed_linear_embedding F G u hu hG.1,
    nuclear_of_continuousLinearEquiv _ _ ec ((nuclear_permanence.1 G hG.2).1 (LinearMap.range u))⟩

private theorem transport_domain {A B T : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (f : B → T) (τ : TopologicalSpace T) :
    @Continuous A T _ τ (f ∘ e) ↔ @Continuous B T _ τ f := by
  letI := τ
  exact ⟨fun h => by simpa [Function.comp_assoc] using h.comp e.symm.continuous,
    fun h => h.comp e.continuous⟩

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsStrictLFOfNuclearFrechet E) (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hQ : IsStrictLFOfNuclearFrechet (E ⧸ V)) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) ∧ IsStrictLFOfNuclearFrechet V := by
  have hLift := bounded_lifting_strict_nuclear_quotient E hE V hV hQ
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hE
  have hrec := (limit_subspace_iff_bounded_lifting E X hmono hexh hX htop V hV).mpr hLift
  let Y (n : ℕ) : Submodule ℂ V := (X n).comap V.subtype
  let e (n : ℕ) : ↥(V ⊓ X n) ≃ₜ Y n :=
      { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
        invFun := fun y => ⟨y.val.val, y.val.property, y.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
        continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have htransfer (n : ℕ) (τ : TopologicalSpace V) := @transport_domain ↥(V ⊓ X n) ↥(Y n) V instTopologicalSpaceSubtype (@instTopologicalSpaceSubtype V _ instTopologicalSpaceSubtype) (e n) Subtype.val τ
  refine ⟨hLift, Y, fun i j hij x hx => hmono hij hx, fun x => hexh x.val, ?_, ?_⟩
  · intro n
    let u : Y n →ₗ[ℂ] X n := (V.subtype.comp (Y n).subtype).codRestrict (X n) (fun y => y.property)
    apply closed_stage _ _ u _ (hX n)
    constructor
    · apply (IsEmbedding.of_comp_iff (g := (Subtype.val : X n → E)) .subtypeVal).mp
      change IsEmbedding ((Subtype.val : V → E) ∘ (Subtype.val : Y n → V))
      exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    · have heq : range u = (Subtype.val : X n → E) ⁻¹' (V : Set E) := by
        ext y
        exact ⟨fun ⟨x, hx⟩ => hx ▸ x.val.property,
          fun hy => ⟨⟨⟨y.val, hy⟩, y.property⟩, rfl⟩⟩
      rw [heq]
      exact hV.preimage continuous_subtype_val
  · trans sInf {t | IsLocallyConvexTopology V t ∧
        ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}
    · exact hrec
    congr 1
    ext τ
    apply and_congr_right
    intro _
    apply forall_congr'
    intro n
    exact htransfer n τ
