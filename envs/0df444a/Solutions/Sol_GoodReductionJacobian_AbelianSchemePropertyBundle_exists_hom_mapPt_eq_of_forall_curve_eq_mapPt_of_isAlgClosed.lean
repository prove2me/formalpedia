-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8fed4834-fdb5-5953-b69c-c1b67e63ecf9

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

noncomputable section

namespace K6bAlgGraphSol

universe u

theorem map_foldr_eq_foldr_map {α β : Type*} (mA : α → α → α) (eA : α) (mB : β → β → β) (eB : β)
    (φ : α → β) (hmul : ∀ a b, φ (mA a b) = mB (φ a) (φ b)) (hone : φ eA = eB) (l : List α) :
    φ (l.foldr mA eA) = (l.map φ).foldr mB eB := by
  induction l with
  | nil => simpa using hone
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, hmul, ih]

section Points

variable {k : Type u} [Field k]

theorem map_one_of_map_mul {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    {f' : A' ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f) (L' : RelativeGroupLaw k f')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (h : SchemeHomOver t f → SchemeHomOver t f')
    (hh : ∀ P Q, h (L.mul t P Q) = L'.mul t (h P) (h Q)) :
    h (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have e : h (L.one t) * h (L.one t) = h (L.one t) := by
    show L'.mul t _ _ = _
    rw [← hh, L.one_mul]
  exact mul_right_cancel (e.trans (one_mul _).symm)

theorem map_inv_of_map_mul {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    {f' : A' ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f) (L' : RelativeGroupLaw k f')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (h : SchemeHomOver t f → SchemeHomOver t f')
    (hh : ∀ P Q, h (L.mul t P Q) = L'.mul t (h P) (h Q)) (P : SchemeHomOver t f) :
    h (L.inv t P) = L'.inv t (h P) := by
  letI := L'.pointGroup t
  have e : h (L.inv t P) * h P = 1 := by
    show L'.mul t _ _ = L'.one t
    rw [← hh, L.inv_mul_cancel, map_one_of_map_mul L L' t h hh]
  exact eq_inv_of_mul_eq_one_left e

theorem prodFstPt_foldr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    {f' : A' ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f) (L' : RelativeGroupLaw k f')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (l : List (SchemeHomOver t (prodStr f f'))) :
    prodFstPt (l.foldr (fun Q R => (L.prod L').mul t Q R) ((L.prod L').one t)) =
      (l.map prodFstPt).foldr (fun Q R => L.mul t Q R) (L.one t) :=
  map_foldr_eq_foldr_map _ _ _ _ prodFstPt
    (fun a b => by rw [RelativeGroupLaw.prod_mul, prodFstPt_prodPairPt])
    (by rw [RelativeGroupLaw.prod_one, prodFstPt_prodPairPt]) l

theorem prodSndPt_foldr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    {f' : A' ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f) (L' : RelativeGroupLaw k f')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (l : List (SchemeHomOver t (prodStr f f'))) :
    prodSndPt (l.foldr (fun Q R => (L.prod L').mul t Q R) ((L.prod L').one t)) =
      (l.map prodSndPt).foldr (fun Q R => L'.mul t Q R) (L'.one t) :=
  map_foldr_eq_foldr_map _ _ _ _ prodSndPt
    (fun a b => by rw [RelativeGroupLaw.prod_mul, prodSndPt_prodPairPt])
    (by rw [RelativeGroupLaw.prod_one, prodSndPt_prodPairPt]) l

end Points

section Image

universe v

theorem isReduced_image {X Y : Scheme.{v}} (σ : X ⟶ Y) [QuasiCompact σ] [IsReduced X] :
    IsReduced σ.image := by
  suffices H : ∀ x : σ.image, _root_.IsReduced (σ.image.presheaf.stalk x) by
    haveI := H
    exact isReduced_of_isReduced_stalk _
  intro x

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (σ.imageι x)) isOpen_univ
  have hV : IsAffineOpen (σ.imageι ⁻¹ᵁ U) := hU.preimage σ.imageι
  have hxV : x ∈ σ.imageι ⁻¹ᵁ U := hxU

  haveI hred : _root_.IsReduced Γ(σ.image, σ.imageι ⁻¹ᵁ U) :=
    isReduced_of_injective _ (σ.toImage_app_injective ⟨U, hU⟩)

  letI := σ.image.presheaf.algebra_section_stalk (⟨x, hxV⟩ : (σ.imageι ⁻¹ᵁ U : σ.image.Opens))
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ hred

theorem range_imageι_eq {X Y : Scheme.{v}} (σ : X ⟶ Y) [QuasiCompact σ] (hσ : IsClosed (Set.range σ)) :
    Set.range σ.imageι = Set.range σ := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker, hσ.closure_eq]

end Image

section RatPts

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_section_of_nonempty {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] [Nonempty T] :
    ∃ s : Spec (CommRingCat.of k) ⟶ T, s ≫ t = 𝟙 _ := by
  haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace (Y := Spec (CommRingCat.of k)) t
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set T).Nonempty)
    isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint t x hx, pointOfClosedPoint_comp t x hx⟩

end RatPts

section Main

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
  {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
  (hA : AbelianSchemePropertyBundle k f)
  {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f')
  (hA' : AbelianSchemePropertyBundle k f')
  (h : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f')
  (hh : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
    h (L.mul (𝟙 (Spec (CommRingCat.of k))) P Q) = L'.mul (𝟙 (Spec (CommRingCat.of k))) (h P) (h Q))
  {n : ℕ} (C : Fin n → Scheme.{0}) (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
  (ν : ∀ i : Fin n, C i ⟶ A) (hν : ∀ i : Fin n, ν i ≫ f = c i)
  (hC : ∀ i : Fin n, IsProper (c i) ∧ SmoothOfRelativeDimension 1 (c i) ∧ IsIntegral (C i))
  (hsurj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
    ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
      (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr
          (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R)
          (L.one (𝟙 (Spec (CommRingCat.of k)))) = P)
  (w : ∀ i : Fin n, C i ⟶ A') (hw : ∀ i : Fin n, w i ≫ f' = c i)
  (hhw : ∀ (i : Fin n) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i)),
    h (mapPt (ν i) (hν i) y) = mapPt (w i) (hw i) y)

local notation "S" => Spec (CommRingCat.of k)

include hA hA' hh hC hsurj hhw in
theorem main :
    ∃ (u : A ⟶ A') (hu : u ≫ f' = f),
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, mapPt u hu P = h P := by
  classical

  haveI : IsProper f := hA.proper
  haveI : IsProper f' := hA'.proper
  have hB : AbelianSchemePropertyBundle k (prodStr f f') := abelianSchemePropertyBundle_prodStr hA hA'
  haveI : IsProper (prodStr f f') := hB.proper
  haveI : GeometricallyIntegral (prodStr f f') := hB.geometricallyIntegral
  have hcB : (L.prod L').IsCommutative :=
    RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral (L.prod L')
  haveI : IsIntegral A := hA.isIntegral_of_field

  have hh1 : h (L.one (𝟙 S)) = L'.one (𝟙 S) := map_one_of_map_mul L L' (𝟙 S) h hh
  have hhinv : ∀ P, h (L.inv (𝟙 S) P) = L'.inv (𝟙 S) (h P) := map_inv_of_map_mul L L' (𝟙 S) h hh

  let νw : ∀ i : Fin n, SchemeHomOver (c i) (prodStr f f') := fun i => prodPairPt ⟨ν i, hν i⟩ ⟨w i, hw i⟩
  haveI : ∀ i : Fin n, IsProper (c i) := fun i => (hC i).1
  haveI : ∀ i : Fin n, IsIntegral (C i) := fun i => (hC i).2.2
  obtain ⟨X, x, hxP, hXint, V, hVa, hVb⟩ :=
    RelativeGroupLaw.exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed (L.prod L') c νw
  haveI : IsProper x := hxP
  haveI : IsIntegral X := hXint

  let foldA : (∀ i : Fin n, SchemeHomOver (𝟙 S) (c i)) → SchemeHomOver (𝟙 S) f := fun y =>
    (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr (fun Q R => L.mul (𝟙 S) Q R) (L.one (𝟙 S))
  let foldA' : (∀ i : Fin n, SchemeHomOver (𝟙 S) (c i)) → SchemeHomOver (𝟙 S) f' := fun y =>
    (List.ofFn (fun i : Fin n => mapPt (w i) (hw i) (y i))).foldr (fun Q R => L'.mul (𝟙 S) Q R) (L'.one (𝟙 S))
  let foldB : (∀ i : Fin n, SchemeHomOver (𝟙 S) (c i)) → SchemeHomOver (𝟙 S) (prodStr f f') := fun y =>
    (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (νw i)).foldr
      (fun Q R => (L.prod L').mul (𝟙 S) Q R) ((L.prod L').one (𝟙 S))
  have foldB_fst : ∀ y, prodFstPt (foldB y) = foldA y := by
    intro y
    simp only [foldB, foldA, prodFstPt_foldr, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    show prodFstPt (NeronModelInfra.schemeHomOverComp (y i) (prodPairPt ⟨ν i, hν i⟩ ⟨w i, hw i⟩)) = _
    rw [prodFstPt_schemeHomOverComp, prodFstPt_prodPairPt]
    rfl
  have foldB_snd : ∀ y, prodSndPt (foldB y) = foldA' y := by
    intro y
    simp only [foldB, foldA', prodSndPt_foldr, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    show prodSndPt (NeronModelInfra.schemeHomOverComp (y i) (prodPairPt ⟨ν i, hν i⟩ ⟨w i, hw i⟩)) = _
    rw [prodSndPt_schemeHomOverComp, prodSndPt_prodPairPt]
    rfl

  have h_foldA : ∀ y, h (foldA y) = foldA' y := by
    intro y
    simp only [foldA, foldA']
    rw [map_foldr_eq_foldr_map _ _ (fun Q R => L'.mul (𝟙 S) Q R) (L'.one (𝟙 S)) h hh hh1, List.map_ofFn]
    congr 2
    funext i
    exact hhw i (y i)

  have key1 : ∀ P : SchemeHomOver (𝟙 S) x,
      prodSndPt (NeronModelInfra.schemeHomOverComp P V) = h (prodFstPt (NeronModelInfra.schemeHomOverComp P V)) := by
    intro P
    obtain ⟨y, hy⟩ := hVa P
    change NeronModelInfra.schemeHomOverComp P V = foldB y at hy
    rw [hy, foldB_fst, foldB_snd, h_foldA]

  have key2 : ∀ Q : SchemeHomOver (𝟙 S) f,
      ∃ P : SchemeHomOver (𝟙 S) x, prodFstPt (NeronModelInfra.schemeHomOverComp P V) = Q := by
    intro Q
    obtain ⟨y, hy⟩ := hsurj Q
    obtain ⟨P, hP⟩ := hVb y
    refine ⟨P, ?_⟩
    change NeronModelInfra.schemeHomOverComp P V = foldB y at hP
    rw [hP, foldB_fst]
    exact hy

  let σ : X ⟶ pullback f f' := V.1
  have hσ : σ ≫ prodStr f f' = x := V.2
  haveI : IsProper (σ ≫ prodStr f f') := by rw [hσ]; infer_instance
  haveI : IsProper σ := IsProper.of_comp σ (prodStr f f')
  let Z : Scheme.{0} := σ.image
  let ιZ : Z ⟶ pullback f f' := σ.imageι
  let z : Z ⟶ S := ιZ ≫ prodStr f f'
  let ι : SchemeHomOver z (prodStr f f') := ⟨ιZ, rfl⟩
  haveI : IsClosedImmersion ι.1 := inferInstanceAs (IsClosedImmersion σ.imageι)
  haveI : IsReduced Z := isReduced_image σ
  haveI : LocallyOfFiniteType z := inferInstanceAs (LocallyOfFiniteType (ιZ ≫ prodStr f f'))
  have hrange : Set.range ιZ = Set.range σ := range_imageι_eq σ σ.isClosedMap.isClosed_range

  have ι_inj : ∀ {T : Scheme.{0}} (t : T ⟶ S),
      Function.Injective fun a : SchemeHomOver t z => NeronModelInfra.schemeHomOverComp a ι := by
    intro T t a b hab
    apply Subtype.ext
    rw [← cancel_mono ιZ]
    exact congrArg Subtype.val hab

  have key3 : ∀ ζ : SchemeHomOver (𝟙 S) z,
      ∃ P : SchemeHomOver (𝟙 S) x, NeronModelInfra.schemeHomOverComp P V = NeronModelInfra.schemeHomOverComp ζ ι := by
    intro ζ
    obtain ⟨ξ, hξ⟩ : ιZ (ζ.1 (IsLocalRing.closedPoint k)) ∈ Set.range σ := hrange ▸ Set.mem_range_self _
    obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ζ.1 ≫ ιZ) (g := σ)
      (IsLocalRing.closedPoint k) ξ (by rw [Scheme.Hom.comp_apply, hξ])
    haveI : Nonempty ↥(pullback (ζ.1 ≫ ιZ) σ) := ⟨z₀⟩
    haveI : LocallyOfFiniteType (σ ≫ prodStr f f') := by rw [hσ]; infer_instance
    haveI : LocallyOfFiniteType σ := locallyOfFiniteType_of_comp σ (prodStr f f')
    obtain ⟨s, hs⟩ := exists_section_of_nonempty (pullback.fst (ζ.1 ≫ ιZ) σ)
    refine ⟨⟨s ≫ pullback.snd (ζ.1 ≫ ιZ) σ, ?_⟩, ?_⟩
    · rw [Category.assoc, ← hσ, ← Category.assoc (pullback.snd _ _), ← pullback.condition, Category.assoc,
        Category.assoc, ← Category.assoc s, hs, Category.id_comp]
      exact ζ.2
    · apply Subtype.ext
      show (s ≫ pullback.snd (ζ.1 ≫ ιZ) σ) ≫ σ = ζ.1 ≫ ιZ
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]

  have key4 : ∀ ζ : SchemeHomOver (𝟙 S) z,
      prodSndPt (NeronModelInfra.schemeHomOverComp ζ ι) = h (prodFstPt (NeronModelInfra.schemeHomOverComp ζ ι)) := by
    intro ζ
    obtain ⟨P, hP⟩ := key3 ζ
    rw [← hP]
    exact key1 P

  have key5 : ∀ Q : SchemeHomOver (𝟙 S) f,
      ∃ ζ : SchemeHomOver (𝟙 S) z, prodFstPt (NeronModelInfra.schemeHomOverComp ζ ι) = Q := by
    intro Q
    obtain ⟨P, hP⟩ := key2 Q
    refine ⟨⟨P.1 ≫ σ.toImage, ?_⟩, ?_⟩
    · show (P.1 ≫ σ.toImage) ≫ (ιZ ≫ prodStr f f') = 𝟙 S
      rw [Category.assoc, ← Category.assoc σ.toImage, Scheme.Hom.toImage_imageι, hσ]
      exact P.2
    · rw [← hP]
      congr 1
      apply Subtype.ext
      show (P.1 ≫ σ.toImage) ≫ ιZ = P.1 ≫ σ
      rw [Category.assoc, Scheme.Hom.toImage_imageι]

  have key6 : ∀ ζ ζ' : SchemeHomOver (𝟙 S) z,
      prodFstPt (NeronModelInfra.schemeHomOverComp ζ ι) = prodFstPt (NeronModelInfra.schemeHomOverComp ζ' ι) →
        ζ = ζ' := by
    intro ζ ζ' e
    apply ι_inj
    apply prodPt_ext e
    rw [key4, key4, e]

  have hone : ∃ o : SchemeHomOver (𝟙 S) z, NeronModelInfra.schemeHomOverComp o ι = (L.prod L').one (𝟙 S) := by
    obtain ⟨ζ, hζ⟩ := key5 (L.one (𝟙 S))
    refine ⟨ζ, prodPt_ext ?_ ?_⟩
    · rw [hζ, RelativeGroupLaw.prod_one, prodFstPt_prodPairPt]
    · rw [key4, hζ, hh1, RelativeGroupLaw.prod_one, prodSndPt_prodPairPt]
  have hmul : ∀ a b : SchemeHomOver (𝟙 S) z, ∃ w' : SchemeHomOver (𝟙 S) z,
      NeronModelInfra.schemeHomOverComp w' ι =
        (L.prod L').mul (𝟙 S) (NeronModelInfra.schemeHomOverComp a ι) (NeronModelInfra.schemeHomOverComp b ι) := by
    intro a b
    obtain ⟨ζ, hζ⟩ := key5 (L.mul (𝟙 S) (prodFstPt (NeronModelInfra.schemeHomOverComp a ι))
      (prodFstPt (NeronModelInfra.schemeHomOverComp b ι)))
    refine ⟨ζ, prodPt_ext ?_ ?_⟩
    · rw [hζ, RelativeGroupLaw.prod_mul, prodFstPt_prodPairPt]
    · rw [key4, hζ, hh, RelativeGroupLaw.prod_mul, prodSndPt_prodPairPt, ← key4, ← key4]
  have hinv : ∀ a : SchemeHomOver (𝟙 S) z, ∃ w' : SchemeHomOver (𝟙 S) z,
      NeronModelInfra.schemeHomOverComp w' ι = (L.prod L').inv (𝟙 S) (NeronModelInfra.schemeHomOverComp a ι) := by
    intro a
    obtain ⟨ζ, hζ⟩ := key5 (L.inv (𝟙 S) (prodFstPt (NeronModelInfra.schemeHomOverComp a ι)))
    refine ⟨ζ, prodPt_ext ?_ ?_⟩
    · rw [hζ, RelativeGroupLaw.prod_inv, prodFstPt_prodPairPt]
    · rw [key4, hζ, hhinv, RelativeGroupLaw.prod_inv, prodSndPt_prodPairPt, ← key4]
  obtain ⟨LZ, hLZ⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
      (L.prod L') ι hone hmul hinv
  have hcZ : LZ.IsCommutative := by
    intro T t a b
    apply ι_inj t
    show NeronModelInfra.schemeHomOverComp (LZ.mul t a b) ι = NeronModelInfra.schemeHomOverComp (LZ.mul t b a) ι
    rw [hLZ, hLZ, hcB.mul_comm]

  let p : SchemeHomOver z f := ⟨ιZ ≫ pullback.fst f f', by simp only [Category.assoc]; rfl⟩
  have hp_fst : ∀ {T : Scheme.{0}} (t : T ⟶ S) (a : SchemeHomOver t z),
      NeronModelInfra.schemeHomOverComp a p = prodFstPt (NeronModelInfra.schemeHomOverComp a ι) := by
    intro T t a
    exact Subtype.ext (Category.assoc _ _ _).symm
  have hp : ∀ {T : Scheme.{0}} (t : T ⟶ S) (a b : SchemeHomOver t z),
      NeronModelInfra.schemeHomOverComp (LZ.mul t a b) p =
        L.mul t (NeronModelInfra.schemeHomOverComp a p) (NeronModelInfra.schemeHomOverComp b p) := by
    intro T t a b
    rw [hp_fst, hp_fst, hp_fst, hLZ, RelativeGroupLaw.prod_mul, prodFstPt_prodPairPt]
  haveI : IsProper p.1 := inferInstanceAs (IsProper (ιZ ≫ pullback.fst f f'))
  have hbij : Function.Bijective fun a : SchemeHomOver (𝟙 S) z => NeronModelInfra.schemeHomOverComp a p := by
    constructor
    · intro a b e
      apply key6
      rw [← hp_fst, ← hp_fst]
      exact e
    · intro Q
      obtain ⟨ζ, hζ⟩ := key5 Q
      exact ⟨ζ, (hp_fst _ ζ).trans hζ⟩
  haveI hiso : IsIso p.1 :=
    RelativeGroupLaw.isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero LZ hcZ L p hp hbij

  have hu : (inv p.1 ≫ ιZ ≫ pullback.snd f f') ≫ f' = f := by
    rw [Category.assoc, Category.assoc, pullback_snd_comp_eq_prodStr]
    show inv p.1 ≫ (ιZ ≫ pullback.fst f f') ≫ f = f
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  refine ⟨inv p.1 ≫ ιZ ≫ pullback.snd f f', hu, ?_⟩
  intro P
  obtain ⟨ζ, hζ⟩ := key5 P
  have hζ' : ζ.1 ≫ p.1 = P.1 := by
    rw [← hp_fst] at hζ
    exact congrArg Subtype.val hζ
  have e1 : P.1 ≫ inv p.1 = ζ.1 := by
    rw [← hζ', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have e2 : mapPt (inv p.1 ≫ ιZ ≫ pullback.snd f f') hu P = prodSndPt (NeronModelInfra.schemeHomOverComp ζ ι) := by
    apply Subtype.ext
    show P.1 ≫ inv p.1 ≫ ιZ ≫ pullback.snd f f' = (ζ.1 ≫ ιZ) ≫ pullback.snd f f'
    rw [← Category.assoc, e1, Category.assoc]
  rw [e2, key4, hζ]

end Main

end K6bAlgGraphSol

end

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of k)) (L' : RelativeGroupLaw k f')
    (hA' : AbelianSchemePropertyBundle k f')

    (h : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f')
    (hh : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      h (L.mul (𝟙 (Spec (CommRingCat.of k))) P Q) = L'.mul (𝟙 (Spec (CommRingCat.of k))) (h P) (h Q))

    {n : ℕ} (C : Fin n → Scheme.{0}) (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
    (ν : ∀ i : Fin n, C i ⟶ A) (hν : ∀ i : Fin n, ν i ≫ f = c i)
    (hC : ∀ i : Fin n, IsProper (c i) ∧ SmoothOfRelativeDimension 1 (c i) ∧ IsIntegral (C i))
    (hsurj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
        (List.ofFn (fun i : Fin n => mapPt (ν i) (hν i) (y i))).foldr
            (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R)
            (L.one (𝟙 (Spec (CommRingCat.of k)))) = P)

    (w : ∀ i : Fin n, C i ⟶ A') (hw : ∀ i : Fin n, w i ≫ f' = c i)
    (hhw : ∀ (i : Fin n) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i)),
      h (mapPt (ν i) (hν i) y) = mapPt (w i) (hw i) y) :
    ∃ (u : A ⟶ A') (hu : u ≫ f' = f),
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, mapPt u hu P = h P :=
  K6bAlgGraphSol.main k f L hA f' L' hA' h hh C c ν hν hC hsurj w hw hhw

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed (solution)
