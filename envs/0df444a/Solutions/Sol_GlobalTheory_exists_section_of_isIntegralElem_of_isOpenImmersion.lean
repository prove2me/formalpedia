-- Prove2me | solution 1 for GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:01.970292+00:00
-- url     : https://prove2.me/submissions/08f9bda3-01a0-44c7-a725-25c8a4bfc0c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLocalSectionOfIsIntegralElemNormalScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  intro hd U s hs u hu
  let C : irreducibleComponents Z := ⟨_, irreducibleComponent_mem_irreducibleComponents u⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from
      ⟨hu, mem_irreducibleComponent⟩)
    (U ⊓ IsNormalScheme.component C).isOpen
  have hWU : W ≤ U := fun x hx ↦ (hWle hx).1
  refine ⟨W, hWU, huW, ?_⟩
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩
  obtain ⟨_, _⟩ := IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr
  obtain ⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W),
      (letI := Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩;
        IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by
    let P : Spec Γ(Z, W) := ⟨⊥, Ideal.isPrime_bot⟩
    have hxW : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
    refine ⟨_, hxW, ?_, ?_⟩
    · let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
      have h := hW.isLocalization_stalk' P hxW
      have e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W) := by
        ext a
        simp [P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      unfold IsLocalization.AtPrime at h
      rw [e] at h
      exact h
    · intro w hw
      obtain ⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hw
      exact ((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    obtain ⟨w, hw, hwr⟩ := hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩
    exact (hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr
  let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
  let _ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W) := (j.app W).hom.toAlgebra
  have hyW : y ∈ j ⁻¹ᵁ W := hxW
  have hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom =
      (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom := by
    change _ = (j.app W).hom.comp _
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]
    rfl
  have hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]
  have hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) =
      T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a) :=
    j.germ_stalkMap_apply W y hxW a
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  let φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y) :=
    T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)
  have hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y) :=
    { φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)
  refine ⟨a, ?_⟩
  have hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0 := by
    rw [map_sub, ← hgerm, ← hφ, sub_eq_zero]
    exact congr(j.stalkMap y $ha)
  have : IsReduced T := isReduced_of_isOpenImmersion j
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro t ht
  have hyt : y ⤳ t :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))
  have hy : y ∈ T.basicOpen
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) :=
    hyt.mem_open (T.basicOpen _).isOpen ht
  rw [Scheme.mem_basicOpen _ _ _ hyW, hg] at hy
  exact (not_isUnit_zero hy).elim
end GlobalTheory
