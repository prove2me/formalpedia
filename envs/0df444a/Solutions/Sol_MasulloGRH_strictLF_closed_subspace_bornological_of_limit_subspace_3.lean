-- Prove2me | solution 3 for MasulloGRH.strictLF_closed_subspace_bornological_of_limit_subspace
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T00:02:12.446877+00:00
-- url     : https://prove2.me/submissions/dcba44d8-23dc-44f0-b5b9-b790de47124a

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

open MasulloGRH Set Topology

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    IsBornological V  := by
  classical
  intro p hp
  obtain ⟨⟨⟨ι, hi, q, hq⟩, _⟩, _⟩ := bounded_in_strict_frechet_stages E X hmono hexh hX htop
  let _ := hq.topologicalAddGroup
  let _ := hq.continuousSMul
  let J (n : ℕ) : (V ⊓ X n : Submodule ℂ E) →ₗ[ℂ] V := Submodule.inclusion inf_le_left
  have hb (n : ℕ) (A : Set (V ⊓ X n : Submodule ℂ E)) (hA : Bornology.IsVonNBounded ℂ A) :
      BddAbove (p '' ((J n) '' A)) := by
    let j : (V ⊓ X n : Submodule ℂ E) →L[ℂ] V :=
      ⟨J n, continuous_subtype_val.subtype_mk _⟩
    exact hp (j '' A) (hA.image j)
  let family : SeminormFamily ℂ V ι := fun _ => p
  let t := family.moduleFilterBasis.topology
  have hfamily : WithSeminorms (topology := t) family := ⟨rfl⟩
  have hstep (n : ℕ) : @Continuous _ _ _ t (J n) := by
    let _ : TopologicalSpace.MetrizableSpace (X n) := (hX n).2.2
    have he : IsEmbedding (Submodule.inclusion (show V ⊓ X n ≤ X n from inf_le_right)) :=
      IsEmbedding.inclusion (show (V ⊓ X n : Submodule ℂ E) ≤ X n from inf_le_right)
    let _ := he.metrizableSpace
    let _ : TopologicalSpace V := t
    let _ := hfamily.topologicalAddGroup
    let _ := hfamily.continuousSMul
    apply (J n).continuous_of_locally_bounded
    intro A hA
    exact hfamily.isVonNBounded_iff_seminorm_bddAbove.mpr (fun _ => hb n A hA)
  have hle : (instTopologicalSpaceSubtype : TopologicalSpace V) ≤ t := by
    rw [hlim]
    exact sInf_le ⟨⟨ι, hi, family, hfamily⟩, hstep⟩
  have hp' : @Continuous V ℝ t _ p := hfamily.continuous_seminorm (Classical.choice hi)
  exact continuous_iff_le_induced.mpr (hle.trans (continuous_iff_le_induced.mp hp'))
