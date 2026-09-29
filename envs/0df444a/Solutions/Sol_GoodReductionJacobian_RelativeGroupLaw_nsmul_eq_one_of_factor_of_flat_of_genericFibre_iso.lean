-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b9fd8ba5-bc93-513d-b602-b5c1ca3fb9fd

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f) (N : ℕ)
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK]
    (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)))
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t gK),
      (L.genericFibre K).nsmul t N (NeronModelInfra.schemeHomOverComp x iK) = (L.genericFibre K).one t)
    {E : Scheme.{u}} (ι : E ⟶ J) [Flat (ι ≫ f)]
    (e : SchemeHomOver (pullback.snd (ι ≫ f) (specGenericFibreInclusion R K)) gK) (hiso : IsIso e.1)
    (hecomp : e.1 ≫ iK.1 =
      pullback.map (ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) ι (𝟙 _) (𝟙 _) (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (hx : ∃ e₀ : T ⟶ E, e₀ ≫ ι = x.1) :
    L.nsmul t N x = L.one t := by

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
  have hx1 : NeronModelInfra.schemeHomOverComp (⟨𝟙 BK, Category.id_comp _⟩ : SchemeHomOver gK gK) iK = iK :=
    Subtype.ext (Category.id_comp _)
  rw [hx1] at hNu
  have hNu' := congrArg (fun p => (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) p).1) hNu
  simp only [nsmul_bc, RelativeGroupLaw.baseChangePointToBase_one, nsmul_coe,
    RelativeGroupLaw.baseChangePointToBase_coe] at hNu'
  rw [one_coe (gK ≫ specGenericFibreInclusion R K)] at hNu'

  haveI : IsDominant (specGenericFibreInclusion R K) := by
    rw [show specGenericFibreInclusion R K = Spec.map (CommRingCat.ofHom (algebraMap R K)) from rfl,
      isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  haveI : IsSchemeTheoreticallyDominant (specGenericFibreInclusion R K) := IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : IsSchemeTheoreticallyDominant (pullback.fst (ι ≫ f) (specGenericFibreInclusion R K)) := inferInstance
  haveI : IsIso e.1 := hiso
  haveI : IsReduced (pullback (ι ≫ f) (specGenericFibreInclusion R K)) := isReduced_of_isOpenImmersion e.1
  haveI : IsReduced E := IsSchemeTheoreticallyDominant.isReduced (pullback.fst (ι ≫ f) (specGenericFibreInclusion R K))

  have hπ : pullback.fst (ι ≫ f) (specGenericFibreInclusion R K) ≫ ι = e.1 ≫ (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) := by
    rw [← Category.assoc e.1, hecomp, pullback.lift_fst]
  have hπs : pullback.fst (ι ≫ f) (specGenericFibreInclusion R K) ≫ ι ≫ f = e.1 ≫ gK ≫ specGenericFibreInclusion R K := by
    rw [← Category.assoc, hπ, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc iK.1, iK.2]
  have key : ι ≫ L.schemeNsmul N = (ι ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    refine ext_of_isDominant_of_isSeparated f ?_ (pullback.fst (ι ≫ f) (specGenericFibreInclusion R K)) ?_
    · simp only [Category.assoc, L.schemeNsmul_over]
      rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]
    · have A : pullback.fst (ι ≫ f) (specGenericFibreInclusion R K) ≫ ι ≫ L.schemeNsmul N =
          e.1 ≫ (gK ≫ specGenericFibreInclusion R K) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
        rw [← Category.assoc, hπ, Category.assoc, hNu']
      rw [A]
      conv_rhs => rw [← Category.assoc, hπs]
      simp only [Category.assoc]

  obtain ⟨e₀, he₀⟩ := hx
  apply Subtype.ext
  rw [nsmul_coe, one_coe, ← he₀, Category.assoc, key, ← x.2, ← he₀]
  simp only [Category.assoc]

end S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso (solution)
