-- Prove2me | solution 1 for NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7584d52e-3115-5ac2-a32b-11efcc307965

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
import Theorems.Thm_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
import Theorems.Thm_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mFetCovSkel

theorem exists_maximal_specializes {X : Scheme.{u}} (S : Set X) (hS : IsClosed S) (x : X) (hx : x ∈ S) :
    ∃ η ∈ S, η ⤳ x ∧ ∀ y ∈ S, y ⤳ η → y = η := by
  haveI : QuasiSober S := hS.isClosedEmbedding_subtypeVal.quasiSober
  set Z : Set S := irreducibleComponent (⟨x, hx⟩ : S) with hZ
  have hZirr : IsIrreducible Z := isIrreducible_irreducibleComponent
  have hZcl : IsClosed Z :=
    isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents _)
  obtain ⟨η, hη⟩ := QuasiSober.sober hZirr hZcl
  refine ⟨η.1, η.2, ?_, ?_⟩
  · have h1 : η ⤳ (⟨x, hx⟩ : S) := hη.specializes mem_irreducibleComponent
    exact h1.map continuous_subtype_val
  · intro y hyS hyη
    have h1 : (⟨y, hyS⟩ : S) ⤳ η := by
      rwa [← Topology.IsInducing.subtypeVal.specializes_iff]
    have h2 : Z ⊆ closure {(⟨y, hyS⟩ : S)} := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 h1)) isClosed_closure
    have h3 : closure {(⟨y, hyS⟩ : S)} = Z :=
      eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible h2
    have h4 : IsGenericPoint (⟨y, hyS⟩ : S) Z := h3
    exact congrArg Subtype.val (h4.eq hη)

end P2mFetCovSkel

open P2mFetCovSkel in
set_option linter.unusedVariables false in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
      (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧
      (∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst f f ≫ f))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ q : ↑(pullback y' y'), (pullback.fst y' y').base q ∈ Set.range ι.1.base →
        (pullback.snd y' y').base q ∈ Set.range ι.1.base → q ∈ U') := by
  classical

  obtain ⟨UY, mY, hY₁, hY₂, hYΦ, hYΦ₁, hYΦ₂, hYΨ, hYΨ₁, hYΨ₂, hassocY, hgenY, hrel⟩ :=
    NeronModelInfra.exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
      K LXK f e W m hmK hΦ hΨ X' U hUW hU₁ hU₂ hU₃

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  haveI : CompactSpace ↥(X' : Scheme.{u}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (X' : Set X))
  haveI : IsNoetherian (X' : Scheme.{u}) := {}
  haveI : QuasiCompact (X'.ι ≫ f) := inferInstance
  haveI : Smooth (X'.ι ≫ f) := inferInstance
  haveI : IsSeparated (X'.ι ≫ f) := inferInstance
  haveI : LocallyOfFiniteType (X'.ι ≫ f) := inferInstance

  have hYk : ∃ x : ↥(X' : Scheme.{u}), (X'.ι ≫ f).base x = IsLocalRing.closedPoint R := by
    obtain ⟨x₀, hx₀⟩ := hXk
    have hS : IsClosed {x : X | f.base x = IsLocalRing.closedPoint R} := by
      have : IsClosed ({IsLocalRing.closedPoint R} : Set (Spec (CommRingCat.of R))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
      exact this.preimage f.base.hom.continuous
    obtain ⟨η, hηS, -, hηmax⟩ := exists_maximal_specializes {x : X | f.base x = IsLocalRing.closedPoint R} hS x₀ hx₀
    have hηX' : η ∈ X' := hX'₂ η hηS (fun y hy hyk => hηmax y hyk hy)
    exact ⟨⟨η, hηX'⟩, by simpa [Scheme.Hom.comp_base] using hηS⟩

  obtain ⟨R', instCR, instDom, instDVR, instAlg, instFin, instEt, instFF, Y', y', ι, U', m',
      hsm, hsep, hloft, hqc, hιo, hgen, hmax, hU'₁, hU'₂, hΦ', hΦ'₁, hΦ'₂, hΨ', hΨ'₁, hΨ'₂, hassoc',
      hext, hsec, hstat⟩ :=
    NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
      (X'.ι ≫ f) UY mY hY₁ hY₂ hYΦ hYΦ₁ hYΦ₂ hYΨ hYΨ₁ hYΨ₂ (fun t u v p q => hassocY t u v p q) hYk hgenY
  haveI : Smooth y' := hsm
  haveI : IsSeparated y' := hsep
  haveI : LocallyOfFiniteType y' := hloft
  haveI : QuasiCompact y' := hqc
  haveI : IsOpenImmersion ι.1 := hιo

  obtain ⟨U'', hle, m'', hm''m', hU''₁, hU''₂, hΦ'', hΦ''₁, hΦ''₂, hΨ'', hΨ''₁, hΨ''₂, hassoc'', hsq⟩ :=
    NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
      (X'.ι ≫ f) UY mY hY₁ hY₂ hYΦ hYΦ₁ hYΦ₂ hYΨ hYΨ₁ hYΨ₂ (fun t u v p q => hassocY t u v p q) hgenY
      R' y' ι U' m' hU'₁ hU'₂ hΦ' hΦ'₁ hΦ'₂ hΨ' hΨ'₁ hΨ'₂ (fun t u v p q => hassoc' t u v p q)
      (fun t' w a b c ha hb hc => hext t' w a b c ha hb hc) hstat

  refine ⟨R', instCR, instDom, instDVR, instAlg, instFin, instEt, instFF, Y', y', ι, U'', m'',
    hsm, hsep, hloft, hqc, hιo, hgen, hmax, hU''₁, hU''₂, hΦ'', hΦ''₁, hΦ''₂, hΨ'', hΨ''₁, hΨ''₂,
    (fun t u v p q => hassoc'' t u v p q), ?_, hsec, hsq⟩

  intro T t' w a b c ha hb hc
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := hrel w.1 a.1 b.1 ha hb
  have hcv : c.1 = v ≫ mY.1 := by
    rw [← cancel_mono X'.ι, Category.assoc, hv₃, hc]
  let wY : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) :=
    ⟨v, by
      have h := a.2
      rw [← hv₁] at h
      simpa only [Category.assoc] using h⟩
  obtain ⟨w', e₁, e₂, e₃⟩ := hext t' wY a b c hv₁.symm hv₂.symm hcv
  refine ⟨⟨w'.1 ≫ (pullback y' y').homOfLE hle, ?_⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact w'.2
  · show (w'.1 ≫ (pullback y' y').homOfLE hle) ≫ U''.ι ≫ pullback.fst y' y' = _
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact e₁
  · show (w'.1 ≫ (pullback y' y').homOfLE hle) ≫ U''.ι ≫ pullback.snd y' y' = _
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact e₂
  · show (w'.1 ≫ (pullback y' y').homOfLE hle) ≫ m''.1 = _
    rw [Category.assoc, hm''m']; exact e₃

end S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing
end P2MW
export P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing (solution)
