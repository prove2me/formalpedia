-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c858afda-58f0-5796-8c66-3ba55e54404a

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range.GoodReductionJacobian"

open scoped TensorProduct

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.baseChangePointOfBase_coe RelativeGroupLaw.baseChange_one RelativeGroupLaw RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "baseChangePointOfBase_coe baseChange baseChange_one schemeNsmul schemeNsmul_over schemeKer schemeKerStr one_natural one inv fibre baseChange_schemeNsmul_comp_fst_and_eq_pullback_map"
namespace R0
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem one_baseChange_fst {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    ((L.baseChange ι).one (𝟙 _)).1 ≫ pullback.fst f ι = ι ≫ (L.one (𝟙 _)).1 := by
  rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) (𝟙 _ ≫ ι) ι (by rw [Category.comp_id, Category.id_comp])
  rw [← h]
  rfl

theorem kerFst_comp_eq_snd {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f = pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1 := by
  calc _ = pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ L.schemeNsmul n ≫ f := by rw [L.schemeNsmul_over]
    _ = (pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ (L.one (𝟙 _)).1) ≫ f := by rw [← Category.assoc, pullback.condition]
    _ = _ := by rw [Category.assoc, (L.one (𝟙 _)).2, Category.comp_id]

theorem exists_kerBaseChangeIso {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    ∃ θ : (L.baseChange ι).schemeKer n ≅ pullback (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι,
      θ.hom ≫ pullback.snd _ ι = (L.baseChange ι).schemeKerStr n ∧
      θ.hom ≫ pullback.fst _ ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 =
        pullback.fst ((L.baseChange ι).schemeNsmul n) ((L.baseChange ι).one (𝟙 _)).1 ≫ pullback.fst f ι := by

  set e := (L.one (𝟙 (Spec (CommRingCat.of R)))).1 with he_def
  set LR := L.baseChange ι
  set eR := (LR.one (𝟙 (Spec (CommRingCat.of R')))).1 with heR_def
  have F1 := (GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι L n).1
  have F1' := (GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι L n).2.1
  have F2 : eR ≫ pullback.fst f ι = ι ≫ e := one_baseChange_fst L ι
  have F2' : eR ≫ pullback.snd f ι = 𝟙 _ := (LR.one (𝟙 _)).2
  have F3 : pullback.fst (L.schemeNsmul n) e ≫ f = pullback.snd (L.schemeNsmul n) e := kerFst_comp_eq_snd L n
  have F4 : pullback.fst (LR.schemeNsmul n) eR ≫ pullback.snd f ι = pullback.snd (LR.schemeNsmul n) eR := by
    calc _ = pullback.fst (LR.schemeNsmul n) eR ≫ LR.schemeNsmul n ≫ pullback.snd f ι := by rw [F1']
      _ = (pullback.snd (LR.schemeNsmul n) eR ≫ eR) ≫ pullback.snd f ι := by rw [← Category.assoc, pullback.condition]
      _ = _ := by rw [Category.assoc, F2', Category.comp_id]

  have hc : (pullback.fst (LR.schemeNsmul n) eR ≫ pullback.fst f ι) ≫ L.schemeNsmul n =
      (pullback.snd (LR.schemeNsmul n) eR ≫ ι) ≫ e := by
    rw [Category.assoc, ← F1, ← Category.assoc, pullback.condition, Category.assoc, F2, Category.assoc]
  let c : LR.schemeKer n ⟶ L.schemeKer n := pullback.lift _ _ hc
  have hcf : c ≫ pullback.fst _ _ = pullback.fst (LR.schemeNsmul n) eR ≫ pullback.fst f ι := pullback.lift_fst _ _ _
  have hcs : c ≫ pullback.snd _ _ = pullback.snd (LR.schemeNsmul n) eR ≫ ι := pullback.lift_snd _ _ _
  have hhom : c ≫ (pullback.fst (L.schemeNsmul n) e ≫ f) = pullback.snd (LR.schemeNsmul n) eR ≫ ι := by
    rw [← Category.assoc, hcf, Category.assoc, pullback.condition, ← Category.assoc, F4]
  let hom : LR.schemeKer n ⟶ pullback (pullback.fst (L.schemeNsmul n) e ≫ f) ι := pullback.lift c _ hhom

  have hu : (pullback.fst (pullback.fst (L.schemeNsmul n) e ≫ f) ι ≫ pullback.fst (L.schemeNsmul n) e) ≫ f =
      pullback.snd (pullback.fst (L.schemeNsmul n) e ≫ f) ι ≫ ι := by
    rw [Category.assoc]; exact pullback.condition
  let u : pullback (pullback.fst (L.schemeNsmul n) e ≫ f) ι ⟶ pullback f ι := pullback.lift _ _ hu
  have huf : u ≫ pullback.fst f ι = pullback.fst _ ι ≫ pullback.fst (L.schemeNsmul n) e := pullback.lift_fst _ _ _
  have hus : u ≫ pullback.snd f ι = pullback.snd _ ι := pullback.lift_snd _ _ _
  have pc := pullback.condition (f := pullback.fst (L.schemeNsmul n) e ≫ f) (g := ι)
  have hinv : u ≫ LR.schemeNsmul n = pullback.snd (pullback.fst (L.schemeNsmul n) e ≫ f) ι ≫ eR := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [F1, reassoc_of% huf, pullback.condition, ← reassoc_of% F3, F2]
      exact (reassoc_of% pc) _
    · simp only [Category.assoc]
      rw [F1', hus, F2', Category.comp_id]
  let inv : pullback (pullback.fst (L.schemeNsmul n) e ≫ f) ι ⟶ LR.schemeKer n := pullback.lift u _ hinv
  have hif : inv ≫ pullback.fst _ _ = u := pullback.lift_fst _ _ _
  have his : inv ≫ pullback.snd _ _ = pullback.snd _ ι := pullback.lift_snd _ _ _
  have hhf : hom ≫ pullback.fst _ ι = c := pullback.lift_fst _ _ _
  have hhs : hom ≫ pullback.snd _ ι = pullback.snd (LR.schemeNsmul n) eR := pullback.lift_snd _ _ _
  refine ⟨⟨hom, inv, ?_, ?_⟩, hhs, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, hif, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, huf, ← Category.assoc, hhf, hcf]
      · rw [Category.assoc, hus, hhs, F4]
    · rw [Category.assoc, his, hhs, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, hhf, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hcf, ← Category.assoc, hif, huf]
      · rw [Category.assoc, hcs, ← Category.assoc, his, ← F3]
        exact pc.symm
    · rw [Category.assoc, hhs, his, Category.id_comp]
  · change hom ≫ _ = _
    rw [← Category.assoc, hhf, hcf]

theorem exists_iso_schemeKer_pullback {R R' k : Type} [CommRing R] [CommRing R'] [CommRing k] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (ιk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')) (n : ℕ) :
    ∃ Φ : (L.baseChange (ιk ≫ ι)).schemeKer n ≅ pullback ((L.baseChange ι).schemeKerStr n) ιk,
      Φ.hom ≫ pullback.snd _ _ = (L.baseChange (ιk ≫ ι)).schemeKerStr n := by
  obtain ⟨θ₁, hθ₁, -⟩ := exists_kerBaseChangeIso L ι n
  obtain ⟨θ₂, hθ₂, -⟩ := exists_kerBaseChangeIso L (ιk ≫ ι) n

  let e₁ : pullback (pullback.snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι) ιk ≅ pullback (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) (ιk ≫ ι) := pullbackLeftPullbackSndIso (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι ιk
  have he₁ : e₁.hom ≫ pullback.snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) (ιk ≫ ι) = pullback.snd (pullback.snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι) ιk :=
    pullbackLeftPullbackSndIso_hom_snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι ιk
  have hsq : θ₁.inv ≫ (L.baseChange ι).schemeKerStr n = pullback.snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι := by
    rw [Iso.inv_comp_eq]; exact hθ₁.symm
  let m : pullback (pullback.snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι) ιk ⟶ pullback ((L.baseChange ι).schemeKerStr n) ιk :=
    pullback.map (pullback.snd (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f) ι) ιk ((L.baseChange ι).schemeKerStr n) ιk θ₁.inv (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, hsq]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  have hm : m ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [pullback.lift_snd]
    exact Category.comp_id _
  refine ⟨θ₂ ≪≫ e₁.symm ≪≫ asIso m, ?_⟩
  show (θ₂.hom ≫ e₁.inv ≫ m) ≫ _ = _
  rw [Category.assoc, Category.assoc, hm, ← hθ₂]
  congr 1
  rw [← he₁, Iso.inv_hom_id_assoc]

theorem specMap_base_eq_closedPoint {R' k : Type} [CommRing R'] [IsLocalRing R'] [Field k] (π : R' →+* k)
    (hker : ∀ x : R', π x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R') (y : ↥(Spec (CommRingCat.of k))) :
    (Spec.map (CommRingCat.ofHom π)).base y = IsLocalRing.closedPoint R' := by
  apply PrimeSpectrum.ext
  rw [IsLocalRing.closedPoint]
  show Ideal.comap π y.asIdeal = IsLocalRing.maximalIdeal R'
  have hy : y.asIdeal = ⊥ := by
    haveI : Subsingleton (PrimeSpectrum k) := inferInstance
    have : y = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
    rw [this]; rfl
  ext x
  rw [Ideal.mem_comap, hy, Ideal.mem_bot, hker]

theorem exists_linearEquiv_sections_opensRange {R' : Type} [CommRing R'] {K : Scheme.{0}} (s : K ⟶ Spec (CommRingCat.of R'))
    (A : Type) [CommRing A] [Algebra R' A]
    (j : Spec (CommRingCat.of A) ⟶ K) (hj : j ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R' A))) [IsOpenImmersion j] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom s j.opensRange
    Nonempty (Γ(K, j.opensRange) ≃ₗ[R'] A) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom s j.opensRange

  let φ : Γ(K, j.opensRange) ≅ CommRingCat.of A := (IsOpenImmersion.ΓIsoTop j).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of A)
  have hinv : (IsOpenImmersion.ΓIsoTop j).inv = j.appLE j.opensRange ⊤ (by rw [Scheme.Hom.preimage_opensRange]) := by
    rw [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Scheme.Hom.appIso_hom', Iso.op_inv,
      Scheme.Hom.map_appLE]
  have hφ : ∀ r : R', φ.hom.hom (algebraMap R' Γ(K, j.opensRange) r) = algebraMap R' A r := by
    intro r
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
    show (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((IsOpenImmersion.ΓIsoTop j).inv.hom
      ((s.appLE ⊤ j.opensRange le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom r))) = _
    rw [hinv, ← CommRingCat.comp_apply (s.appLE ⊤ j.opensRange le_top), Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R')) (e : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ g ⁻¹ᵁ ⊤),
        g = Spec.map (CommRingCat.ofHom (algebraMap R' A)) → g.appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom (algebraMap R' A))).appTop := by
      rintro g e rfl
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [key _ _ hj, ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of A)).hom, Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (Scheme.ΓSpecIso (CommRingCat.of R')).hom, Iso.inv_hom_id]
    rfl
  let ψ : Γ(K, j.opensRange) ≃+* A := φ.commRingCatIsoToRingEquiv
  have hψ : ∀ r : R', ψ (algebraMap R' Γ(K, j.opensRange) r) = algebraMap R' A r := hφ
  let ψa : Γ(K, j.opensRange) ≃ₐ[R'] A := AlgEquiv.ofRingEquiv (f := ψ) hψ
  exact ⟨ψa.toLinearEquiv⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem main
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {R' : Type} [CommRing R'] [IsLocalRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {k : Type} [Field k] (π : R' →+* k) (hker : ∀ x : R', π x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R')
    (c : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hc : Spec.map (CommRingCat.ofHom π) ≫ ι = c)
    (n : ℕ) (A : Type) [CommRing A] [Algebra R' A] [Module.Finite R' A] [Module.Free R' A]
    (j : Spec (CommRingCat.of A) ⟶ (L.baseChange ι).schemeKer n)
    (hj : j ≫ (L.baseChange ι).schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R' A)))
    (hjo : IsOpenImmersion j)
    (hcov : ∀ x : ↥((L.baseChange ι).schemeKer n),
      ((L.baseChange ι).schemeKerStr n).base x = IsLocalRing.closedPoint R' → x ∈ Set.range j.base) :
    IsFinite ((L.baseChange c).schemeKerStr n) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange c).schemeKerStr n) ⊤
     Module.finrank R' A = Module.finrank k Γ((L.baseChange c).schemeKer n, ⊤)) := by
  classical
  subst hc
  letI : Algebra R' k := π.toAlgebra
  haveI := hjo
  have hιk : Scheme.TwoAffineOpenCover.specMap R' k = Spec.map (CommRingCat.ofHom π) := rfl
  have hU : IsAffineOpen j.opensRange := isAffineOpen_opensRange j

  have htop : (pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⁻¹ᵁ j.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z _
    change (pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)).base z ∈ Set.range j.base
    apply hcov
    have hz := congrArg (fun φ => φ.base z) (pullback.condition (f := ((L.baseChange ι).schemeKerStr n)) (g := Scheme.TwoAffineOpenCover.specMap R' k))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hz
    rw [hz]
    exact specMap_base_eq_closedPoint π hker _

  letI := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange ι).schemeKerStr n) j.opensRange
  obtain ⟨eA⟩ := exists_linearEquiv_sections_opensRange ((L.baseChange ι).schemeKerStr n) A j hj
  haveI : Module.Free R' Γ(((L.baseChange ι).schemeKer n), j.opensRange) := Module.Free.of_equiv eA.symm
  haveI : Module.Finite R' Γ(((L.baseChange ι).schemeKer n), j.opensRange) := Module.Finite.equiv eA.symm
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen ((L.baseChange ι).schemeKerStr n) j.opensRange hU k

  have hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ((pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⁻¹ᵁ j.opensRange)
      Module.finrank k Γ(pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k), (pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⁻¹ᵁ j.opensRange) = Module.finrank R' A ∧
      Module.Finite k Γ(pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k), (pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⁻¹ᵁ j.opensRange) := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ((pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⁻¹ᵁ j.opensRange)
    refine ⟨?_, Module.Finite.equiv e.toLinearEquiv⟩
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_baseChange]
    exact eA.finrank_eq

  have hrank' : letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⊤
      Module.finrank k Γ((pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)), ⊤) = Module.finrank R' A ∧ Module.Finite k Γ((pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)), ⊤) := by
    rw [← htop]; exact hrank

  have happTop : ∀ {Y Z : Scheme.{0}} (g : Y ⟶ Z) (e : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = g.appTop := by
    intro Y Z g e
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl

  obtain ⟨Φ, hΦ⟩ := exists_iso_schemeKer_pullback L ι (Spec.map (CommRingCat.ofHom π)) n

  have hsec : letI := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKerStr n) ⊤
      Module.finrank k Γ(((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKer n), ⊤) = Module.finrank R' A ∧ Module.Finite k Γ(((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKer n), ⊤) := by
    letI iP := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⊤
    letI iK := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKerStr n) ⊤
    let eΓ : Γ((pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)), ⊤) ≅ Γ(((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKer n), ⊤) := Scheme.Γ.mapIso Φ.op
    have heΓ : eΓ.hom = Φ.hom.appTop := by
      show Scheme.Γ.map Φ.op.hom = _
      rw [Iso.op_hom, Scheme.Γ_map_op]
    have hcomm : ∀ r : k, eΓ.commRingCatIsoToRingEquiv (algebraMap k Γ((pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)), ⊤) r) = algebraMap k Γ(((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKer n), ⊤) r := by
      intro r
      show eΓ.hom.hom _ = _
      rw [heΓ, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, happTop, happTop,
        ← hΦ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    let ψ : Γ((pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)), ⊤) ≃ₐ[k] Γ(((L.baseChange (Spec.map (CommRingCat.ofHom π) ≫ ι)).schemeKer n), ⊤) := AlgEquiv.ofRingEquiv (f := eΓ.commRingCatIsoToRingEquiv) hcomm
    haveI := hrank'.2
    exact ⟨by rw [← ψ.toLinearEquiv.finrank_eq]; exact hrank'.1, Module.Finite.equiv ψ.toLinearEquiv⟩

  haveI : IsAffineHom (pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) := Scheme.TwoAffineOpenCover.isAffineHom_fst ((L.baseChange ι).schemeKerStr n) k
  have hPtop : IsAffineOpen (⊤ : (pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)).Opens) := htop ▸ hU.preimage (pullback.fst ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k))
  haveI : IsAffine (⊤ : (pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)).Opens) := hPtop
  haveI : IsAffine (pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) := IsAffine.of_isIso ((pullback ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)).topIso).inv
  have hfinP : IsFinite (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)) ⊤
    have h1 : RingHom.Finite ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (pullback.snd ((L.baseChange ι).schemeKerStr n) (Scheme.TwoAffineOpenCover.specMap R' k)).appLE ⊤ ⊤ le_top).hom := hrank'.2
    have h2 : RingHom.Finite (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom :=
      RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.surjective
    have h3 := RingHom.Finite.comp h1 h2
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id_assoc, happTop] at h3
    exact h3
  refine ⟨?_, hsec.1.symm⟩
  rw [← hΦ]
  infer_instance

end GoodReductionJacobian.RelativeGroupLaw.R0

theorem solution
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {R' : Type} [CommRing R'] [IsLocalRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {k : Type} [Field k] (π : R' →+* k) (hker : ∀ x : R', π x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R')
    (c : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hc : Spec.map (CommRingCat.ofHom π) ≫ ι = c)
    (n : ℕ) (A : Type) [CommRing A] [Algebra R' A] [Module.Finite R' A] [Module.Free R' A]
    (j : Spec (CommRingCat.of A) ⟶ (L.baseChange ι).schemeKer n)
    (hj : j ≫ (L.baseChange ι).schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R' A)))
    (hjo : IsOpenImmersion j) (hjc : IsClosedImmersion j)
    (hcov : ∀ x : ↥((L.baseChange ι).schemeKer n),
      ((L.baseChange ι).schemeKerStr n).base x = IsLocalRing.closedPoint R' → x ∈ Set.range j.base) :
    IsFinite ((L.baseChange c).schemeKerStr n) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange c).schemeKerStr n) ⊤
     Module.finrank R' A = Module.finrank k Γ((L.baseChange c).schemeKer n, ⊤)) :=
  GoodReductionJacobian.RelativeGroupLaw.R0.main L ι π hker c hc n A j hj hjo hcov

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range (solution)
