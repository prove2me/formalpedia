-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.chow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:40.749228+00:00
-- url     : https://prove2.me/submissions/56bdc5f5-3c1f-4896-80a9-609bb7a55bec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_exists_closed_affineSpace
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_exists_affine_le_or_disjoint
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_exists_charts
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_on_chart
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_isIso_on_open
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_mem_basicOpen_of_mul_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution (R : Type) [CommRing R] [IsNoetherianRing R] (W : Scheme)
    (f : W ⟶ Spec (CommRingCat.of R)) (hsep : IsSeparated f) (hft : LocallyOfFiniteType f)
    (hqc : QuasiCompact f) (hne : Nonempty W) :
    ∃ (W' : Scheme) (P : Scheme) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R))
      (U : W.Opens), IsProper π ∧ Set.Nonempty (U : Set W) ∧ IsIso (π ∣_ U) ∧ IsProjOver s ∧
        IsImmersion q ∧ q ≫ s = π ≫ f := by
  classical
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨t, ht, hcov⟩ : ∃ t : Finset W.Opens, (∀ O ∈ t, IsAffineOpen O) ∧
      ∀ x : W, ∃ O ∈ t, x ∈ O := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun O : W.affineOpens ↦ (O.1 : Set W))
      (fun O ↦ O.1.isOpen) (fun x _ ↦ by
        obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
          W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩)
    refine ⟨t.image Subtype.val, ?_, fun x ↦ ?_⟩
    · intro O hO
      obtain ⟨O, -, rfl⟩ := Finset.mem_image.mp hO
      exact O.2
    · obtain ⟨O, hO, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact ⟨O.1, Finset.mem_image_of_mem _ hO, hx⟩
  obtain ⟨U, hU, hUne, hdich⟩ := exists_affine_le_or_disjoint t
  let I : Type := {O : t // U ≤ O.1}
  have hgen (i : I) : ∃ (σ : Type) (_ : Fintype σ) (g : σ → Γ(i.1.1.toScheme, ⊤)),
      IsClosedImmersion (AffineSpace.homOfVector (i.1.1.ι ≫ f) g) := by
    have : IsAffine i.1.1.toScheme := ht _ i.1.2
    exact exists_closed_affineSpace _
  choose σ hσ g hg using hgen
  let x (i : I) (a : Option (σ i)) : Γ(U.toScheme, ⊤) :=
    (W.homOfLE i.2).appTop (a.elim 1 (g i))
  let m (K : ∀ i, Option (σ i)) : Γ(U.toScheme, ⊤) := ∏ i, x i (K i)
  have hx0 (i : I) : x i none = 1 := map_one _
  have hm0 : m (fun _ ↦ none) = 1 := Finset.prod_eq_one fun i _ ↦ hx0 i
  have hm (K : ∀ i, Option (σ i)) (i : I) (hK : K i = none) (a : Option (σ i)) :
      m (Function.update K i a) = x i a * m K := by
    simp only [m]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self,
      ← Finset.mul_prod_erase _ (fun i ↦ x i (K i)) (Finset.mem_univ i), hK, hx0, one_mul]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (∀ i, Option (σ i)) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e := Fintype.equivFinOfCardEq hN
  obtain ⟨D, r, hD, hr, hφ⟩ := exists_charts R N
  obtain ⟨φ, hφs, hφ⟩ := hφ U (U.ι ≫ f) (fun K ↦ m (e.symm K)) (e fun _ ↦ none)
    (by rw [e.symm_apply_apply, hm0]; exact isUnit_one)
  let s := PSpace.str R N
  let γ : U.toScheme ⟶ pullback f s := pullback.lift U.ι φ hφs.symm
  have : IsAffine U.toScheme := hU
  have : QuasiCompact (γ ≫ pullback.fst f s ≫ f) := inferInstance
  have : QuasiCompact γ := QuasiCompact.of_comp γ (pullback.fst f s ≫ f)
  have h₁ : γ.toImage ≫ γ.imageι ≫ pullback.fst f s = U.ι := by
    rw [γ.toImage_imageι_assoc, pullback.lift_fst]
  have h₂ : γ.toImage ≫ γ.imageι ≫ pullback.snd f s = φ := by
    rw [γ.toImage_imageι_assoc, pullback.lift_snd]
  refine ⟨γ.image, PSpace R N, γ.imageι ≫ pullback.fst f s, γ.imageι ≫ pullback.snd f s, s, U,
    inferInstance, hUne, isIso_on_open f s U _ γ.toImage h₁,
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_, by simp [pullback.condition]⟩
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun _ _ _ _ ↦ inferInstance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion)
    (fun K : {K : ∀ i, Option (σ i) // ∃ i, K i = none} ↦ D (e K.1)) ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨O, hOt, hzO⟩ := hcov ((γ.imageι ≫ pullback.fst f s) z)
    have hUO : U ≤ O := by
      refine (hdich O hOt).resolve_right fun hdis ↦ ?_
      obtain ⟨w, hw⟩ := γ.toImage.denseRange.exists_mem_open
        ((γ.imageι ≫ pullback.fst f s) ⁻¹ᵁ O).isOpen ⟨z, hzO⟩
      change (γ.imageι ≫ pullback.fst f s) (γ.toImage w) ∈ O at hw
      rw [← Scheme.Hom.comp_apply, h₁] at hw
      exact Set.disjoint_left.mp hdis w.2 hw
    let i : I := ⟨⟨O, hOt⟩, hUO⟩
    obtain ⟨K, hK⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hD.ge (Set.mem_univ ((γ.imageι ≫ pullback.snd f s) z)))
    obtain ⟨K, rfl⟩ := e.surjective K
    obtain ⟨w, hw, hwz⟩ := mem_basicOpen_of_mul_eq_one U O hUO φ _ _ γ.toImage h₁ h₂
      ((K i).elim 1 (g i)) (D (e K)) (r (e (Function.update K i none)) (e K)) (by
        intro V a b hab
        obtain ⟨hu, hb⟩ := hφ (e K) V a b hab
        have hb' := hb (e (Function.update K i none))
        simp only [e.symm_apply_apply] at hu hb'
        have hK' := hm (Function.update K i none) i (Function.update_self _ _ _) (K i)
        rw [Function.update_idem, Function.update_eq_self] at hK'
        refine hu.mul_left_inj.mp ?_
        rw [mul_right_comm, hb', one_mul, ← map_mul, mul_comm, hK']) z hzO hK
    refine TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨Function.update K i none, i, Function.update_self _ _ _⟩, ?_⟩
    rw [← hwz]
    exact hr _ _ hw
  · rintro ⟨K, i, hK⟩
    have := hg i
    have := closed_on_chart f s U i.1.1 i.2 φ γ.imageι γ.toImage h₁ h₂ (g i) (D (e K))
      (fun a ↦ r (e (Function.update K i (some a))) (e K)) (by
        intro V a b hab c
        obtain ⟨hu, hb⟩ := hφ (e K) V a b hab
        have hb' := hb (e (Function.update K i (some c)))
        simp only [e.symm_apply_apply] at hu hb'
        refine hu.mul_left_inj.mp ?_
        rw [hb', hm K i hK, map_mul]
        rfl)
    exact inferInstanceAs (IsImmersion ((γ.imageι ≫ pullback.snd f s) ∣_ D (e K)))
end GlobalTheory.DenseClosedAffineSubsets
