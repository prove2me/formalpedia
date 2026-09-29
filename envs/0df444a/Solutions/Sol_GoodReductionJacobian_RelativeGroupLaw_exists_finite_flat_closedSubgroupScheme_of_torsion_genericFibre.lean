-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/efe4ae0a-7afc-5e4c-812f-d09494569d47

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f)
    (N : ℕ) [IsFinite (L.schemeKerStr N)]
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK] (LBK : RelativeGroupLaw K gK)
    (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)))
    (hci : IsClosedImmersion iK.1)
    (hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t gK),
      NeronModelInfra.schemeHomOverComp (LBK.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK) (NeronModelInfra.schemeHomOverComp y iK))
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t gK),
      (L.genericFibre K).nsmul t N (NeronModelInfra.schemeHomOverComp x iK) = (L.genericFibre K).one t) :
    ∃ (E : Scheme.{u}) (ι : E ⟶ J) (_ : IsClosedImmersion ι)
      (_ : IsFinite (ι ≫ f)) (_ : Flat (ι ≫ f)) (_ : LocallyOfFinitePresentation (ι ≫ f)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ e : T ⟶ E, e ≫ ι = (L.one t).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
          ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1) ∧
      ∃ e : SchemeHomOver (pullback.snd (ι ≫ f) (specGenericFibreInclusion R K)) gK,
        IsIso e.1 ∧
        e.1 ≫ iK.1 =
          pullback.map (ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]) := by

  obtain ⟨LN, e, hflat, hmulι, -, hiso, -, hecomp⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion
      K L LBK iK hci hiK
  have hgK : iK.1 ≫ pullback.snd f (specGenericFibreInclusion R K) = gK := iK.2

  have nsmul_coe : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (y : SchemeHomOver t f),
      (L.nsmul t n y).1 = y.1 ≫ L.schemeNsmul n := by
    intro T t n y
    have H := L.nsmul_natural f t y.1 y.2 n RelativeGroupLaw.idPoint
    have hy : GoodReductionJacobian.schemeHomOverComp y.1 y.2 RelativeGroupLaw.idPoint = y :=
      Subtype.ext (Category.comp_id _)
    rw [hy] at H
    exact (congrArg Subtype.val H).symm
  have one_coe : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
    intro T t
    exact (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id _))).symm

  have nsmul_bc : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (n : ℕ)
      (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr (specGenericFibreInclusion R K) f)),
      RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) ((L.genericFibre K).nsmul t' n x) =
        L.nsmul _ n (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) x) := by
    intro T t' n x
    induction n with
    | zero => exact RelativeGroupLaw.baseChangePointToBase_one _ L t'
    | succ n ih =>
        rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
          RelativeGroupLaw.baseChangePointToBase_mul, ih]

  have hNu := hN gK ⟨𝟙 BK, Category.id_comp _⟩
  have hx : NeronModelInfra.schemeHomOverComp (⟨𝟙 BK, Category.id_comp _⟩ : SchemeHomOver gK gK) iK = iK :=
    Subtype.ext (Category.id_comp _)
  rw [hx] at hNu
  have hNu' := congrArg (fun p => (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) p).1) hNu
  simp only [nsmul_bc, RelativeGroupLaw.baseChangePointToBase_one, nsmul_coe,
    RelativeGroupLaw.baseChangePointToBase_coe] at hNu'
  rw [one_coe (gK ≫ specGenericFibreInclusion R K)] at hNu'

  haveI : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    have : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
      rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance
    exact IsClosedImmersion.of_comp _ f
  set jN : L.schemeKer N ⟶ J := pullback.fst (L.schemeNsmul N) (L.one (𝟙 (Spec (CommRingCat.of R)))).1
    with hjN

  let h' : BK ⟶ L.schemeKer N := pullback.lift (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) (gK ≫ specGenericFibreInclusion R K) hNu'
  have hh' : h' ≫ jN = (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) := pullback.lift_fst _ _ _

  have hker : jN.ker ≤ (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hh', Scheme.Hom.ker_comp, ← Scheme.IdealSheafData.map_bot]
    exact Scheme.IdealSheafData.map_mono jN bot_le
  let k : (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).image ⟶ L.schemeKer N := IsClosedImmersion.lift jN (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι hker
  have hk : k ≫ jN = (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion k := by
    have : IsClosedImmersion (k ≫ jN) := by rw [hk]; infer_instance
    exact IsClosedImmersion.of_comp k jN

  have hstr : L.schemeKerStr N = jN ≫ f := by
    have hc := pullback.condition (f := L.schemeNsmul N) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    have hc' := congrArg (· ≫ f) hc
    simp only [Category.assoc, L.schemeNsmul_over] at hc'
    rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id] at hc'
    exact hc'.symm
  haveI hfinE : IsFinite ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) := by
    have : (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f = k ≫ L.schemeKerStr N := by rw [hstr, ← Category.assoc, hk]
    rw [this]
    infer_instance

  let ιpt : SchemeHomOver ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) f := ⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩
  have hφone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      NeronModelInfra.schemeHomOverComp (LN.one t) ιpt = L.one t := by
    intro T t
    set a := NeronModelInfra.schemeHomOverComp (LN.one t) ιpt with ha
    have haa : L.mul t a a = a := by
      rw [ha, ← hmulι t (LN.one t) (LN.one t), LN.one_mul]
    calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
      _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
      _ = L.mul t (L.inv t a) (L.mul t a a) := L.mul_assoc t _ _ _
      _ = L.mul t (L.inv t a) a := by rw [haa]
      _ = L.one t := L.inv_mul_cancel t a

  have liftPt : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (e₁ : T ⟶ (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).image),
      e₁ ≫ (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι = x.1 → ∃ z : SchemeHomOver t ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f), NeronModelInfra.schemeHomOverComp z ιpt = x := by
    intro T t x e₁ he₁
    refine ⟨⟨e₁, ?_⟩, Subtype.ext he₁⟩
    rw [← Category.assoc, he₁]; exact x.2
  refine ⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).image, (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, inferInstance, hfinE, hflat, inferInstance, ?_, ?_, ?_, ⟨e, hiso, hecomp⟩⟩
  · intro T t
    refine ⟨(LN.one t).1, ?_⟩
    simpa only [NeronModelInfra.schemeHomOverComp_coe] using congrArg Subtype.val (hφone t)
  · intro T t x y hx hy
    obtain ⟨e₁, he₁⟩ := hx
    obtain ⟨e₂, he₂⟩ := hy
    obtain ⟨x', hx'⟩ := liftPt t x e₁ he₁
    obtain ⟨y', hy'⟩ := liftPt t y e₂ he₂
    refine ⟨(LN.mul t x' y').1, ?_⟩
    have H := congrArg Subtype.val (hmulι t x' y')
    rw [hx', hy'] at H
    simpa only [NeronModelInfra.schemeHomOverComp_coe] using H
  · intro T t x hx
    obtain ⟨e₁, he₁⟩ := hx
    obtain ⟨x', hx'⟩ := liftPt t x e₁ he₁
    refine ⟨(LN.inv t x').1, ?_⟩
    set b := NeronModelInfra.schemeHomOverComp (LN.inv t x') ιpt with hb
    have hbx : L.mul t b x = L.one t := by
      rw [hb, ← hx', ← hmulι t (LN.inv t x') x', LN.inv_mul_cancel, hφone]
    have : b = L.inv t x := by
      calc b = L.mul t b (L.one t) := (L.mul_one t b).symm
        _ = L.mul t b (L.mul t x (L.inv t x)) := by rw [L.mul_inv_cancel]
        _ = L.mul t (L.mul t b x) (L.inv t x) := (L.mul_assoc t _ _ _).symm
        _ = L.mul t (L.one t) (L.inv t x) := by rw [hbx]
        _ = L.inv t x := L.one_mul t _
    exact congrArg Subtype.val this

end S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre (solution)
