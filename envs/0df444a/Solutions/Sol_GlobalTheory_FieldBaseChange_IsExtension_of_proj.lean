-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.IsExtension.of_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:55.909557+00:00
-- url     : https://prove2.me/submissions/68536b7f-5af2-4f62-95b3-302bbb8012c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_expansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
namespace GlobalTheory.FieldBaseChange
namespace IsExtension
theorem _root_.solution {J : Type} {P Q : J → Type} [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module F (Q j)] (a : V →ₛₗ[algebraMap K F] W)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] Q j) (hb : ∀ j, IsExtension (b j))
    (π : ∀ j, V →ₗ[K] P j) (π' : ∀ j, W →ₗ[F] Q j) (comm : ∀ j v, π' j (a v) = b j (π j v))
    (inj' : ∀ x, (∀ j, π' j x = 0) → x = 0) (T : Finset J) (inj : ∀ v, (∀ j ∈ T, π j v = 0) → v = 0)
    (desc : ∀ (ℓ : F →ₗ[K] K) (Λ : ∀ j, Q j →+ P j), (∀ j, IsCoord (b j) ℓ (Λ j)) →
      ∀ x, ∃ v, ∀ j, π j v = Λ j (π' j x)) : IsExtension a := by
  classical
  have hcoord : ∀ ℓ : F →ₗ[K] K, ∃ Λ, IsCoord a ℓ Λ := by
    intro ℓ
    choose Λj hΛj using fun j => (hb j).coord ℓ
    choose f hf using desc ℓ Λj hΛj
    have uniq : ∀ v v' : V, (∀ j, π j v = π j v') → v = v' := fun v v' e =>
      sub_eq_zero.mp (inj _ (fun j _ => by rw [map_sub, e j, sub_self]))
    refine ⟨{ toFun := f
              map_zero' := uniq _ _ (fun j => by simp [hf])
              map_add' := fun x y => uniq _ _ (fun j => by simp [hf]) }, fun c v => ?_⟩
    refine uniq _ _ (fun j => ?_)
    show π j (f (c • a v)) = π j (ℓ c • v)
    rw [hf, map_smul, comm, hΛj j c (π j v), map_smul]
  refine ⟨?_, hcoord⟩
  let β := Module.Free.chooseBasis K F
  choose Λj hΛj using fun j i => (hb j).coord (β.coord i)
  rw [eq_top_iff]
  intro x _
  choose v hv using fun i => desc (β.coord i) (fun j => Λj j i) (fun j => hΛj j i) x
  choose S hS hS' using fun j => exists_expansion β (hb j).span (fun i => hΛj j i) (π' j x)
  have hv0 : ∀ i ∉ T.biUnion S, v i = 0 := fun i hi => inj _ (fun j hj => by
    rw [hv i j]
    exact hS j i (fun h => hi (Finset.mem_biUnion.mpr ⟨j, hj, h⟩)))
  have hx : x = ∑ i ∈ T.biUnion S, β i • a (v i) := by
    refine (sub_eq_zero.mp (inj' _ (fun j => ?_)))
    rw [map_sub, sub_eq_zero, map_sum]
    simp only [map_smul, comm, hv]
    conv_lhs => rw [hS' j (T.biUnion S ∪ S j) Finset.subset_union_right]
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    rw [← hv i j, hv0 i hi, map_zero, map_zero, smul_zero]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩))
end IsExtension
end GlobalTheory.FieldBaseChange
