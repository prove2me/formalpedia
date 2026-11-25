-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.exists_adapted_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:38.910997+00:00
-- url     : https://prove2.me/submissions/b926195e-1dda-437e-b085-4da0aad00476

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_exists_lift_adapted
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_isAlt_standardAltForm
import Theorems.Thm_GlobalTheory_isSymplecticBasisOfType_standardAltForm
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_standardAltForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
open TensorProduct
variable {S R Λ l : Type*} [CommRing S] [CommRing R] [AddCommGroup Λ] [Module S Λ] [Fintype l]
  {B : LinearMap.BilinForm S Λ}
namespace GlobalTheory
namespace IsSymplecticBasis
theorem _root_.solution [Finite (MaximalSpectrum R)] {f : S →+* R}
    (hf : Surjective f) (hB : B.IsAlt) {b : Basis (l ⊕ l) S Λ} (hb : IsSymplecticBasis B b)
    {P Q : Submodule S Λ} (hIP : RingHom.ker f • ⊤ ≤ P) (hIQ : RingHom.ker f • ⊤ ≤ Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, f (B x y) = 0) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, f (B x y) = 0)
    (hPQ : P ⊔ Q = ⊤) :
    ∃ c : Basis (l ⊕ l) S Λ, IsSymplecticBasis B c ∧
      (∀ x, x ∈ P ↔ ∀ i, f (c.repr x (.inr i)) = 0) ∧
      ∀ x, x ∈ Q ↔ ∀ i, f (c.repr x (.inl i)) = 0 := by
  classical
  have : RingHomSurjective f := ⟨hf⟩
  let φ : Λ →ₛₗ[f] (l ⊕ l → R) :=
    { toFun := fun x i => f (b.repr x i)
      map_add' := fun x y => by ext; simp
      map_smul' := fun a x => by ext; simp }
  have hφ : ∀ x y, standardAltForm (fun _ : l => (1 : R)) (φ x) (φ y) = f (B x y) := fun x y => by
    simp [standardAltForm_apply, hb.apply_eq_sum hB, φ]
  have hker : LinearMap.ker φ ≤ RingHom.ker f • ⊤ := fun x hx => by
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (congrFun hx i) Submodule.mem_top
  have hsurj : Surjective φ := fun y => by
    choose z hz using fun i => hf (y i)
    exact ⟨∑ i, z i • b i, funext fun i => (congrArg f (congrFun (b.repr_sum_self z) i)).trans (hz i)⟩
  have hmem : ∀ {T : Submodule S Λ}, RingHom.ker f • ⊤ ≤ T → ∀ x, φ x ∈ T.map φ ↔ x ∈ T :=
    fun hT x => by
      rw [← Submodule.mem_comap, Submodule.comap_map_eq, sup_eq_left.2 (hker.trans hT)]
  obtain ⟨c, hc, -, -, h₁, h₂⟩ := hb.exists_lift_adapted hf hB (isAlt_standardAltForm _) φ
    (isSymplecticBasisOfType_standardAltForm fun _ : l => (1 : R))
    (fun i => by ext j; simp [φ, Finsupp.single_apply, Pi.single_apply, eq_comm])
    (P := P.map φ) (Q := Q.map φ)
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [hφ, hP x hx y hy])
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [hφ, hQ x hx y hy])
    (by rw [← Submodule.map_sup, hPQ, Submodule.map_top, LinearMap.range_eq_top.2 hsurj])
  exact ⟨c, hc, fun x => by rw [← h₁, hmem hIP], fun x => by rw [← h₂, hmem hIQ]⟩
end IsSymplecticBasis
end GlobalTheory
