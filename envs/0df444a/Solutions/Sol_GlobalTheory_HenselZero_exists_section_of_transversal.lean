-- Prove2me | solution 1 for GlobalTheory.HenselZero.exists_section_of_transversal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:32.763432+00:00
-- url     : https://prove2.me/submissions/f7f525b0-7854-412f-9a6a-a0a9cc400ab1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Theorems.Thm_GlobalTheory_HenselZero_exists_factor_stalk
import Theorems.Thm_GlobalTheory_HenselZero_exists_formallySmooth_stalk
import Theorems.Thm_GlobalTheory_HenselZero_fromSpecStalk_mem_basicOpen
import Theorems.Thm_GlobalTheory_HenselZero_maximalIdeal_le_span_sup
import Theorems.Thm_GlobalTheory_HenselZero_exists_algHom_ker_eq
import Theorems.Thm_GlobalTheory_JacGen_valT_specMap_fromSpecStalk
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
namespace GlobalTheory.HenselZero
theorem _root_.solution {O ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Fintype ι] [DecidableEq ι] {X Y : Scheme.{0}} {p : X ⟶ Sp O} [Smooth p]
    {q : Y ⟶ Sp (ResidueField O)} {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
    (t : Sp (ResidueField O) ⟶ Y) (ht : t ≫ q = 𝟙 _) (pt : Sp (ResidueField O)) {U : X.Opens} (hU : φ (t pt) ∈ U)
    (f : ι → Γ(X, U)) (hf : ∀ i, valT (t ≫ φ) U (f i) = 0)
    (hm : maximalIdeal _ ≤ Ideal.span (Set.range fun i => gs φ (t pt) U (f i)))
    (w : ι → (Sp (DualNumber (ResidueField O)) ⟶ Y))
    (hw₁ : ∀ k, spMap (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom ≫ w k = t)
    (hw₂ : ∀ k, w k ≫ q = spMap (algebraMap _ _))
    (hd : (Matrix.of fun i k => (valT (w k ≫ φ) U (f i)).snd).det ≠ 0) :
    ∃ z : Sp O ⟶ X, z ≫ p = 𝟙 _ ∧ spMap (residue O) ≫ z = t ≫ φ ∧ (∀ i, valT z U (f i) = 0) ∧
      ∀ y, y ⤳ φ (t pt) → (∀ i, y ∉ X.basicOpen (f i)) → ∃ r, z r = y := by
  obtain rfl : pt = closedPoint (ResidueField O) := Subsingleton.elim (α := PrimeSpectrum (ResidueField O)) _ _
  set y₀ := φ (t (closedPoint (ResidueField O))) with hy₀
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨α, hs, hα⟩ := exists_formallySmooth_stalk p y₀
  obtain ⟨u, hu⟩ := exists_factor_stalk (t ≫ φ) (y := y₀) rfl
  have : IsLocalRing (DualNumber (ResidueField O)) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _
  have hχ := fun k => exists_factor_stalk (w k ≫ φ) (y := y₀) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    rw [← comap_closedPoint (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom,
      hy₀, ← hw₁ k]
    rfl)
  choose χ hχ using hχ
  letI := α.hom.toAlgebra
  have : Algebra.FormallySmooth O (X.presheaf.stalk y₀) := hs
  have e₁ : α ≫ u = CommRingCat.ofHom (residue O) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hu, hφ.w, reassoc_of% ht]
  have e₂ : ∀ k, χ k ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom = u := fun k => by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk y₀), Spec.map_comp, Category.assoc, hχ, hu, ← hw₁ k, Category.assoc]
  have e₃ : ∀ k, α ≫ χ k = CommRingCat.ofHom (residue O) ≫ CommRingCat.ofHom (algebraMap _ _) := fun k => by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ, hφ.w, reassoc_of% hw₂, Spec.map_comp]
  obtain ⟨ψ, hψ, hk⟩ := exists_algHom_ker_eq (O := O) (fun i => (X.presheaf.germ U y₀ hU).hom (f i)) u.hom
    (fun r => congrArg (fun g => g.hom r) e₁)
    (fun i => (JacGen.valT_specMap_fromSpecStalk hU u (f i)).symm.trans (hu ▸ hf i))
    (fun k => (χ k).hom) (fun k a => congrArg (fun g => g.hom a) (e₂ k))
    (fun k r => congrArg (fun g => g.hom r) (e₃ k))
    (by
      refine fun h => hd (Eq.trans ?_ h)
      congr 1
      ext i k
      rw [Matrix.of_apply, Matrix.of_apply, ← hχ, JacGen.valT_specMap_fromSpecStalk hU])
    (maximalIdeal_le_span_sup hφ _ α hα _ (hm.trans_eq (congrArg (fun F => Ideal.span (Set.range F))
      (funext fun i => (gs_eq φ _ U hU _).trans (Scheme.Hom.germ_stalkMap_apply φ U _ hU _).symm))))
  have hs' : Function.Surjective ψ := fun r => ⟨_, ψ.commutes r⟩
  refine ⟨spMap ψ.toRingHom ≫ X.fromSpecStalk y₀, ?_, ?_, fun i => ?_, fun y hy hyf => ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact ψ.commutes r
  · rw [← hu, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact hψ a
  · exact (JacGen.valT_specMap_fromSpecStalk hU (CommRingCat.ofHom ψ.toRingHom) (f i)).trans
      (hk.ge (Ideal.subset_span ⟨i, rfl⟩))
  · obtain ⟨r, rfl⟩ : y ∈ Set.range (X.fromSpecStalk y₀) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    obtain ⟨r', hr'⟩ : r ∈ Set.range (PrimeSpectrum.comap ψ.toRingHom) := by
      rw [range_comap_of_surjective _ _ hs']
      refine hk.le.trans (Ideal.span_le.2 ?_)
      rintro _ ⟨i, rfl⟩
      by_contra hn
      exact hyf i (fromSpecStalk_mem_basicOpen hU _ r hn)
    exact ⟨r', congrArg (X.fromSpecStalk y₀) hr'⟩
end GlobalTheory.HenselZero
