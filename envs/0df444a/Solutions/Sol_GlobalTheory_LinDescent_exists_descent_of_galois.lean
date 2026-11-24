-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_descent_of_galois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:46:29.25477+00:00
-- url     : https://prove2.me/submissions/0054b5cf-c36f-4007-9989-103b07a64350

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_of_mem_basicOpen
import Theorems.Thm_GlobalTheory_LinDescent_exists_inv_sec
import Theorems.Thm_GlobalTheory_LinDescent_LocTransitive_exists_apply_eq
import Theorems.Thm_GlobalTheory_LinDescent_exists_descent_of_invGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
theorem _root_.solution [Group C] [Finite C] [IsFinite π] [Flat π] [Surjective π]
    (hL : L.IsLB) (ht1 : t 1 = 𝟙 X) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hπ : ∀ c, t c ≫ π = π) (h : LocTransitive t π)
    (hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ t c)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c)))) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e, IsInvGen u (π ⁻¹ᵁ V) e := fun y => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (π x)) isOpen_univ
    have hinv : ∀ (V : Y.Opens) c, π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ π ⁻¹ᵁ V := fun V c => by
      rw [← Scheme.Hom.comp_preimage, hπ]
    obtain ⟨s, h1, h2, i₀, h3⟩ := exists_inv_sec hL ht1 ht hfree hu hc
      (IsAffineOpen.preimage hV₀ π) (hinv V₀) x hx
    let N : X.Opens := ⨆ i, X.basicOpen (s i)
    let V : Y.Opens := ⟨(π '' (N : Set X)ᶜ)ᶜ, (π.isClosedMap _ N.isOpen.isClosed_compl).isOpen_compl⟩
    have hN : ∀ x', x' ∈ π ⁻¹ᵁ V → ∃ i, x' ∈ X.basicOpen (s i) := fun x' hx' => by
      by_contra hh
      exact hx' ⟨x', fun hh' => hh (Opens.mem_iSup.1 hh'), rfl⟩
    have hN' : ∀ x', x' ∈ π ⁻¹ᵁ V → x' ∈ π ⁻¹ᵁ V₀ := fun x' hx' => by
      obtain ⟨i, hi⟩ := hN x' hx'
      exact (X.basicOpen_le _ hi).1
    have l : ∀ i, π ⁻¹ᵁ V ⊓ L.U i ≤ π ⁻¹ᵁ V₀ ⊓ L.U i := fun i x' hx' => ⟨hN' x' hx'.1, hx'.2⟩
    have hu' : ∀ i, IsUnit (rs (l i) (s i)) := fun i => isUnit_of_mem_basicOpen _ fun x' hx' => by
      obtain ⟨j, hj⟩ := hN x' hx'.1
      have hj' := X.basicOpen_le _ hj
      refine (isUnit_gs_iff (𝟙 X) x' _ hx' _).1 ?_
      rw [gs_res (𝟙 X) x' _ hx', h1 _ (𝟙 X) x' i j hj'.1 hx'.2 hj'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X) x' _ hj' _).2 hj)
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V → r z ∈ L.U i →
        (gm r z _ (hu' i).unit).val = gs r z _ (s i) := fun Z r z i a b =>
      (gs_unit r z (π ⁻¹ᵁ V ⊓ L.U i) ⟨a, b⟩ _).symm.trans (gs_res r z (l i) ⟨a, b⟩ _)
    refine ⟨V, ?_, fun i => (hu' i).unit, fun Z r z i j a b c => Units.ext ?_,
      fun c Z r z i k a b d => Units.ext ?_⟩
    · rintro ⟨x', hx', e⟩
      obtain ⟨c, rfl⟩ := h.exists_apply_eq e
      obtain ⟨k, hk⟩ := exists_chart hL (t c x)
      have h4 := X.basicOpen_le _ h3
      have h5 := (isUnit_gs_iff (𝟙 X) x _ h4 _).2 h3
      rw [h2 c _ (𝟙 X) x i₀ k hx h4.2 hk] at h5
      exact hx' (Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff (𝟙 X ≫ t c) x (π ⁻¹ᵁ V₀ ⊓ L.U k)
        ⟨hinv V₀ c hx, hk⟩ _).1 (isUnit_of_mul_isUnit_right h5)⟩)
    · rw [Units.val_mul, v Z r z i a b, v Z r z j a c]
      exact h1 Z r z i j (hN' _ a) b c
    · rw [Units.val_mul, v Z r z i a b, v Z (r ≫ t c) z k (hinv V c a) d]
      exact h2 c Z r z i k (hN' _ a) b d
  choose V hV e he using H
  exact exists_descent_of_invGen hL hπ h V hV e he
end GlobalTheory.LinDescent
