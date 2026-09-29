-- Prove2me | solution 1 for NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7334dfe7-eff5-52d4-9b2e-a8593f8e7aa0

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mIterFin

section Algebra

theorem specMap_apply_ne_closedPoint {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
    [IsLocalRing B] [Ring.DimensionLEOne B] (hA : IsLocalRing.maximalIdeal A ≠ ⊥) (f : A →+* B)
    (hf : Function.Injective f) (p : ↥(Spec (CommRingCat.of B))) (hp : p ≠ IsLocalRing.closedPoint B) :
    (Spec.map (CommRingCat.ofHom f)).base p ≠ IsLocalRing.closedPoint A := by
  have hbot : p.asIdeal = ⊥ := by
    by_contra h
    exact hp (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal p.isPrime h)))
  intro h
  have h' : (PrimeSpectrum.comap f p).asIdeal = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal h
    first | exact this | simpa [IsLocalRing.closedPoint] using this
  rw [PrimeSpectrum.comap_asIdeal, hbot, Ideal.comap_bot_of_injective f hf] at h'
  exact hA h'.symm

theorem exists_ringHom_comp_eq {A B K : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [Module.Finite A B] [Field K] [IsAlgClosed K]
    (φ : A →+* K) (hφ : ∀ x ∈ IsLocalRing.maximalIdeal A, φ x = 0) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = φ ∧ ∀ x ∈ IsLocalRing.maximalIdeal B, ψ x = 0 := by
  classical

  haveI : IsLocalHom (algebraMap A B) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal x).mpr hxu
    have hmax : (Ideal.comap (algebraMap A B) (IsLocalRing.maximalIdeal B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (IsLocalRing.maximalIdeal B)
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have : algebraMap A B x ∈ IsLocalRing.maximalIdeal B := by
      rw [← Ideal.mem_comap, heq]; exact hxm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx

  haveI : IsLocalHom φ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have := hφ x ((IsLocalRing.mem_maximalIdeal x).mpr hxu)
    rw [this] at hx
    exact not_isUnit_zero hx
  let φ' : IsLocalRing.ResidueField A →+* K := IsLocalRing.ResidueField.lift φ
  letI : Algebra (IsLocalRing.ResidueField A) K := φ'.toAlgebra
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Algebra.IsAlgebraic.of_finite _ _
  let ψ' : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A] K := IsAlgClosed.lift
  refine ⟨ψ'.toRingHom.comp (IsLocalRing.residue B), ?_, ?_⟩
  · ext x
    change ψ' (IsLocalRing.residue B (algebraMap A B x)) = φ x
    have h1 : IsLocalRing.residue B (algebraMap A B x) =
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) (IsLocalRing.residue A x) := rfl
    rw [h1, ψ'.commutes]
    rfl
  · intro x hx
    change ψ' (IsLocalRing.residue B x) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]

end Algebra

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)}
variable {U : (pullback y y).Opens} {m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y}

variable (y U m) in

structure Strict : Prop where
  hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm))
  hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition])))
  hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1
  hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U

variable (y U m) in

structure Level (K : Type u) [Field K] (φ₀ : R →+* K) : Type (u + 1) where
  R' : Type u
  [cr : CommRing R']
  [dom : IsDomain R']
  [dvr : IsDiscreteValuationRing R']
  [alg : Algebra R R']
  [fin : Module.Finite R R']
  [et : Algebra.Etale R R']
  [ff : Module.FaithfullyFlat R R']
  φ : R' →+* K
  hφ : φ.comp (algebraMap R R') = φ₀
  hφm : ∀ x ∈ IsLocalRing.maximalIdeal R', φ x = 0
  Y' : Scheme.{u}
  y' : Y' ⟶ Spec (CommRingCat.of R')
  [sm : Smooth y']
  [sep : IsSeparated y']
  [loft : LocallyOfFiniteType y']
  [qc : QuasiCompact y']
  ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'
  [oi : IsOpenImmersion ι.1]
  hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base
  hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base
  U' : (pullback y' y').Opens
  m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'
  hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))
  hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))
  hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm))
  hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))
  hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))
  hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition])))
  hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 → p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' → q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1
  hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1

variable {K : Type u} [Field K] {φ₀ : R →+* K}

namespace Level

variable (E : Level y U m K φ₀)

scoped instance : CommRing E.R' := E.cr
scoped instance : IsDomain E.R' := E.dom
scoped instance : IsDiscreteValuationRing E.R' := E.dvr
scoped instance : Algebra R E.R' := E.alg
scoped instance : Module.Finite R E.R' := E.fin
scoped instance : Algebra.Etale R E.R' := E.et
scoped instance : Module.FaithfullyFlat R E.R' := E.ff
scoped instance : Smooth E.y' := E.sm
scoped instance : IsSeparated E.y' := E.sep
scoped instance : LocallyOfFiniteType E.y' := E.loft
scoped instance : QuasiCompact E.y' := E.qc
scoped instance : IsOpenImmersion E.ι.1 := E.oi

noncomputable abbrev s : Spec (CommRingCat.of E.R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R E.R'))

noncomputable abbrev X : Scheme.{u} := pullback (pullback.fst y y ≫ y) E.s

noncomputable abbrev prX : E.X ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) E.s

noncomputable abbrev UX : E.X.Opens := E.prX ⁻¹ᵁ U

noncomputable def hom : (E.UX : Scheme.{u}) ⟶ E.Y' :=
  pullback.lift (f := y) (g := E.s) (E.prX.resLE U E.UX le_rfl ≫ m.1) (E.UX.ι ≫ pullback.snd _ _)
    (by rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc,
          pullback.condition]) ≫ E.ι.1

theorem hom_comp_y' : E.hom ≫ E.y' = E.UX.ι ≫ pullback.snd (pullback.fst y y ≫ y) E.s := by
  rw [hom, Category.assoc, E.ι.2, pullback.lift_snd]

theorem s_apply_ne_closedPoint (p : ↥(Spec (CommRingCat.of E.R'))) (hp : p ≠ IsLocalRing.closedPoint E.R') :
    E.s.base p ≠ IsLocalRing.closedPoint R :=
  specMap_apply_ne_closedPoint (IsDiscreteValuationRing.not_a_field R) _
    (FaithfulSMul.algebraMap_injective R E.R') p hp

theorem mem_UX_of_ne (hS : Strict y U m) (q : ↥E.X)
    (hq : (pullback.snd (pullback.fst y y ≫ y) E.s).base q ≠ IsLocalRing.closedPoint E.R') : q ∈ E.UX := by
  show E.prX.base q ∈ U
  apply hS.hUK
  have h := congrArg (fun f => f.base q) (pullback.condition (f := pullback.fst y y ≫ y) (g := E.s))
  simp only [Scheme.Hom.comp_apply] at h
  rw [show (pullback.fst y y ≫ y).base (E.prX.base q) = y.base ((pullback.fst y y).base (E.prX.base q)) from
    Scheme.Hom.comp_apply _ _ _, h]
  exact E.s_apply_ne_closedPoint _ hq

variable [Smooth y]

scoped instance smooth_sndX : Smooth (pullback.snd (pullback.fst y y ≫ y) E.s) :=
  MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance

theorem dense_UX (hS : Strict y U m) : Dense (E.UX : Set ↥E.X) := by
  intro q
  have hgen := Flat.generalizingMap (pullback.snd (pullback.fst y y ≫ y) E.s)
  let η : ↥(Spec (CommRingCat.of E.R')) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E.R')
  have hη : η ⤳ (pullback.snd (pullback.fst y y ≫ y) E.s).base q :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (fun _ h => by simp [η] at h; simp [h])
  obtain ⟨q', hq', hq'η⟩ := hgen hη
  have hne : η ≠ IsLocalRing.closedPoint E.R' := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field E.R' (this.symm.trans rfl)
  have hq'U : q' ∈ E.UX := E.mem_UX_of_ne hS q' (by rw [show (pullback.snd _ E.s).base q' = η from hq'η]; exact hne)
  exact closure_mono (Set.singleton_subset_iff.mpr hq'U) (specializes_iff_mem_closure.mp hq')

scoped instance isReduced_X : IsReduced E.X :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd (pullback.fst y y ≫ y) E.s)

scoped instance isSeparated_Y' : E.Y'.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← terminal.comp_from E.y']
  infer_instance

noncomputable def pm (hS : Strict y U m) : E.X.PartialMap E.Y' := ⟨E.UX, E.dense_UX hS, E.hom⟩

noncomputable def D (hS : Strict y U m) : E.X.Opens := (E.pm hS).toRationalMap.domain

noncomputable def M (hS : Strict y U m) : ((E.D hS : E.X.Opens) : Scheme.{u}) ⟶ E.Y' :=
  ((E.pm hS).toRationalMap.toPartialMap).hom

theorem UX_le_D (hS : Strict y U m) : E.UX ≤ E.D hS := (E.pm hS).le_domain_toRationalMap

theorem homOfLE_M (hS : Strict y U m) : E.X.homOfLE (E.UX_le_D hS) ≫ E.M hS = E.hom := by
  have h := (E.pm hS).toPartialMap_toRationalMap_restrict
  first | exact h | simpa [Scheme.PartialMap.restrict_hom] using h

theorem le_D_of_hom (hS : Strict y U m) (V : E.X.Opens) (hUV : E.UX ≤ V) (g : (V : Scheme.{u}) ⟶ E.Y')
    (hg : E.X.homOfLE hUV ≫ g = E.hom) : V ≤ E.D hS := by
  let g' : E.X.PartialMap E.Y' := ⟨V, (E.dense_UX hS).mono hUV, g⟩
  have heq : g'.toRationalMap = (E.pm hS).toRationalMap := by
    rw [Scheme.PartialMap.toRationalMap_eq_iff]
    exact ⟨E.UX, E.dense_UX hS, hUV, le_rfl, by simp [Scheme.PartialMap.restrict_hom, g', pm, hg]⟩
  have := g'.le_domain_toRationalMap
  rw [heq] at this
  exact this

scoped instance isReduced_D (hS : Strict y U m) : IsReduced ((E.D hS : E.X.Opens) : Scheme.{u}) := inferInstance

theorem M_comp_y' (hS : Strict y U m) :
    E.M hS ≫ E.y' = (E.D hS).ι ≫ pullback.snd (pullback.fst y y ≫ y) E.s := by
  haveI : IsDominant (E.X.homOfLE (E.UX_le_D hS)) := Opens.isDominant_homOfLE (E.dense_UX hS) _
  apply ext_of_isDominant (E.X.homOfLE (E.UX_le_D hS))
  rw [← Category.assoc, E.homOfLE_M, hom_comp_y', ← Category.assoc, Scheme.homOfLE_ι]

noncomputable abbrev Ω (y : Y ⟶ Spec (CommRingCat.of R)) (φ₀ : R →+* K) : Scheme.{u} :=
  pullback (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀))

theorem specMap_φ_comp_s : Spec.map (CommRingCat.ofHom E.φ) ≫ E.s = Spec.map (CommRingCat.ofHom φ₀) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, E.hφ]

noncomputable def ρ : Ω y φ₀ ⟶ E.X :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom E.φ)) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, E.specMap_φ_comp_s])

def Z (hS : Strict y U m) : Set ↥(Ω y φ₀) := E.ρ.base ⁻¹' (E.D hS : Set ↥E.X)ᶜ

theorem isClosed_Z (hS : Strict y U m) : IsClosed (E.Z hS) :=
  ((E.D hS).isOpen.isClosed_compl).preimage E.ρ.base.hom.continuous

section Stat

variable {R'' : Type u} [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra E.R' R'']

noncomputable abbrev t (R'' : Type u) [CommRing R''] [Algebra E.R' R''] :
    Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of E.R') :=
  Spec.map (CommRingCat.ofHom (algebraMap E.R' R''))

noncomputable def P (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) : pullback y s ⟶ E.X :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := E.s)
    (pullback.lift (f := y) (g := y) (pullback.snd y s ≫ a) (pullback.fst y s)
      (by rw [Category.assoc, ha, pullback.condition]))
    (pullback.snd y s ≫ E.t R'')
    (by rw [pullback.lift_fst_assoc, Category.assoc, ha, Category.assoc, ← hs])

@[reassoc (attr := simp)]
theorem P_prX (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) :
    E.P s hs a ha ≫ E.prX = pullback.lift (f := y) (g := y) (pullback.snd y s ≫ a) (pullback.fst y s)
      (by rw [Category.assoc, ha, pullback.condition]) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem P_snd (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) :
    E.P s hs a ha ≫ pullback.snd (pullback.fst y y ≫ y) E.s = pullback.snd y s ≫ E.t R'' :=
  pullback.lift_snd _ _ _

def Stat (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of R'') ⟶ Y) : Prop :=
  ∃ τ : pullback y s ⟶ pullback E.y' (E.t R''),
    τ ≫ pullback.snd E.y' (E.t R'') = pullback.snd y s ∧
    ∀ {T : Scheme.{u}} (x : T ⟶ pullback y s) (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y E.s),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y s ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y s →
      v ≫ pullback.fst y E.s = w ≫ m.1 →
      v ≫ pullback.snd y E.s = x ≫ pullback.snd y s ≫ E.t R'' →
      x ≫ τ ≫ pullback.fst E.y' (E.t R'') = v ≫ E.ι.1

theorem stat_of_range_subset (hS : Strict y U m)
    (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s)
    (hP : Set.range (E.P s hs a ha).base ⊆ (E.D hS : Set ↥E.X)) : E.Stat s a := by

  let P' : pullback y s ⟶ (E.D hS : Scheme.{u}) :=
    IsOpenImmersion.lift (E.D hS).ι (E.P s hs a ha) (by rwa [Scheme.Opens.range_ι])
  have hP' : P' ≫ (E.D hS).ι = E.P s hs a ha := IsOpenImmersion.lift_fac _ _ _
  let τ₀ : pullback y s ⟶ E.Y' := P' ≫ E.M hS
  have hτ₀ : τ₀ ≫ E.y' = pullback.snd y s ≫ E.t R'' := by
    rw [Category.assoc, E.M_comp_y', ← Category.assoc, hP', E.P_snd]
  refine ⟨pullback.lift τ₀ (pullback.snd y s) hτ₀, pullback.lift_snd _ _ _, ?_⟩
  intro T x w v h1 h2 h3 h4
  rw [pullback.lift_fst]

  have hxP : x ≫ E.P s hs a ha ≫ E.prX = w ≫ U.ι := by
    rw [E.P_prX]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; exact h1.symm
    · rw [Category.assoc, pullback.lift_snd]; exact h2.symm
  have hrange : Set.range (x ≫ E.P s hs a ha).base ⊆ Set.range E.UX.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    show E.prX.base ((x ≫ E.P s hs a ha).base z) ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc, hxP, Scheme.Hom.comp_apply]
    exact (w.base z).2
  let x' : T ⟶ (E.UX : Scheme.{u}) := IsOpenImmersion.lift E.UX.ι (x ≫ E.P s hs a ha) hrange
  have hx' : x' ≫ E.UX.ι = x ≫ E.P s hs a ha := IsOpenImmersion.lift_fac _ _ _
  have hxP' : x ≫ P' = x' ≫ E.X.homOfLE (E.UX_le_D hS) := by
    rw [← cancel_mono (E.D hS).ι, Category.assoc, hP', Category.assoc, Scheme.homOfLE_ι, hx']
  have hw : x' ≫ E.prX.resLE U E.UX le_rfl = w := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hx', Category.assoc, hxP]
  have hv : x' ≫ pullback.lift (f := y) (g := E.s) (E.prX.resLE U E.UX le_rfl ≫ m.1) (E.UX.ι ≫ pullback.snd _ _)
      (by rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc,
          pullback.condition]) = v := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hw, h3]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hx', Category.assoc, E.P_snd, h4]
  show x ≫ (P' ≫ E.M hS) = v ≫ E.ι.1
  rw [← Category.assoc, hxP', Category.assoc, E.homOfLE_M, hom, ← Category.assoc, hv]

theorem exists_not_mem_D (hS : Strict y U m)
    (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) (hn : ¬ E.Stat s a) :
    ∃ b : ↥(pullback y s), (E.P s hs a ha).base b ∉ E.D hS := by
  by_contra h
  push Not at h
  exact hn (E.stat_of_range_subset hS s hs a ha (by rintro _ ⟨b, rfl⟩; exact h b))

end Stat

def HasSec : Prop := ∃ a' : Spec (CommRingCat.of E.R') ⟶ E.Y', a' ≫ E.y' = 𝟙 _

section Next

variable [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y] [IsAlgClosed K]
variable {R'' : Type u} [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra E.R' R'']
  [Module.Finite E.R' R''] [Algebra.Etale E.R' R''] [Module.FaithfullyFlat E.R' R'']
  [Algebra R R''] [IsScalarTower R E.R' R'']
  [Module.Finite R R''] [Algebra.Etale R R''] [Module.FaithfullyFlat R R'']

theorem s₂_eq : Spec.map (CommRingCat.ofHom (algebraMap R R'')) = E.t R'' ≫ E.s := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

set_option maxHeartbeats 6400000 in

theorem exists_next (hS : Strict y U m)
    (s : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R)) (hs : s = E.t R'' ≫ E.s)
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = s) :
    ∃ E₂ : Level y U m K φ₀, E₂.HasSec ∧ E₂.Z hS ⊆ E.Z hS ∧
      ∀ b : ↥(pullback y s), (E.P s hs a ha).base b ∉ E.D hS → E₂.Z hS ≠ E.Z hS := by
  obtain rfl : s = Spec.map (CommRingCat.ofHom (algebraMap R R'')) := hs.trans E.s₂_eq.symm

  obtain ⟨ψ, hψ, hψm⟩ := exists_ringHom_comp_eq (A := E.R') (B := R'') E.φ E.hφm

  obtain ⟨Y'', y'', ι₂, U'', m'', hsm, hsep, hloft, hqc, hoi, hgen₂, hmax₂, h1, h2, h3, h4, h5, h6, h7, h8,
      hassoc₂, hext₂, ⟨a'', ha''⟩, ⟨j, hj, hjy, hjc⟩, ⟨D₂, hle, M₂, hM₂, hprog⟩⟩ :=
    NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
      y U m hS.hU₁ hS.hU₂ hS.hΦ hS.hΦ₁ hS.hΦ₂ hS.hΨ hS.hΨ₁ hS.hΨ₂ hS.hassoc hS.hUK
      E.R' E.y' E.ι E.hgen E.hmax E.U' E.m' E.hU'₁ E.hU'₂ E.hΦ' E.hΦ'₁ E.hΦ'₂ E.hΨ' E.hΨ'₁ E.hΨ'₂ E.hassoc' E.hext
      R'' a ha
  let E₂ : Level y U m K φ₀ :=
    { R' := R'', φ := ψ,
      hφ := by rw [IsScalarTower.algebraMap_eq R E.R' R'', ← RingHom.comp_assoc, hψ, E.hφ],
      hφm := hψm, Y' := Y'', y' := y'', sm := hsm, sep := hsep, loft := hloft, qc := hqc, ι := ι₂, oi := hoi,
      hgen := hgen₂, hmax := hmax₂, U' := U'', m' := m'', hU'₁ := h1, hU'₂ := h2, hΦ' := h3, hΦ'₁ := h4, hΦ'₂ := h5,
      hΨ' := h6, hΨ'₁ := h7, hΨ'₂ := h8, hassoc' := hassoc₂, hext := hext₂ }
  have hE₂t : E₂.t R'' = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id R'')) = 𝟙 _
    rw [CommRingCat.ofHom_id, Spec.map_id]

  let π : E₂.X ⟶ E.X := pullback.map _ _ _ _ (𝟙 _) (E.t R'') (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]; exact hs)
  have hπ₁ : π ≫ E.prX = E₂.prX := by
    simp only [π, pullback.lift_fst, Category.comp_id]
  have hπ₂ : π ≫ pullback.snd _ E.s = pullback.snd _ E₂.s ≫ E.t R'' := by
    simp only [π, pullback.lift_snd]
  have hρ : E.ρ = E₂.ρ ≫ π := by
    apply pullback.hom_ext
    · simp only [Level.ρ, π, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [Level.ρ, π, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      show _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap E.R' R''))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]

  have hUX : E₂.UX = π ⁻¹ᵁ E.UX := by
    show E₂.prX ⁻¹ᵁ U = π ⁻¹ᵁ (E.prX ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hπ₁]

  let V : E₂.X.Opens := π ⁻¹ᵁ (E.D hS)
  have hUXV : E₂.UX ≤ V := by rw [hUX]; exact fun q hq => E.UX_le_D hS hq
  have hlift : (π.resLE (E.D hS) V le_rfl ≫ E.M hS) ≫ E.y' = (V.ι ≫ pullback.snd _ E₂.s) ≫ E.t R'' := by
    rw [Category.assoc, E.M_comp_y', ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hπ₂,
      Category.assoc]
  let g : (V : Scheme.{u}) ⟶ Y'' :=
    pullback.lift (π.resLE (E.D hS) V le_rfl ≫ E.M hS) (V.ι ≫ pullback.snd _ E₂.s) hlift ≫ j

  let κ : (E₂.UX : Scheme.{u}) ⟶ (E.UX : Scheme.{u}) := π.resLE E.UX E₂.UX (le_of_eq hUX)
  have hκ : κ ≫ E.UX.ι = E₂.UX.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  have hκres : κ ≫ E.prX.resLE U E.UX le_rfl = E₂.prX.resLE U E₂.UX le_rfl := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hκ, Category.assoc, hπ₁,
      Scheme.Hom.resLE_comp_ι]

  have hcondE : (E.prX.resLE U E.UX le_rfl ≫ m.1) ≫ y = (E.UX.ι ≫ pullback.snd _ E.s) ≫ E.s := by
    rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc,
      pullback.condition]
  have hcond₂ : (E₂.prX.resLE U E₂.UX le_rfl ≫ m.1) ≫ y = (E₂.UX.ι ≫ pullback.snd _ E₂.s) ≫ E₂.s := by
    rw [Category.assoc, m.2, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc,
      pullback.condition]
  have hg : E₂.X.homOfLE hUXV ≫ g = E₂.hom := by
    show _ = pullback.lift _ _ hcond₂ ≫ ι₂.1
    simp only [g, ← Category.assoc]
    refine hjc (pullback.lift _ _ hcond₂) (κ ≫ pullback.lift _ _ hcondE) _ ?_ ?_ ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hκres]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← Category.assoc, hκ, Category.assoc, hπ₂,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_fst, Category.assoc]
      show _ = κ ≫ E.hom
      rw [← E.homOfLE_M hS, ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (E.D hS).ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
        Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι, hκ]
    · rw [Category.assoc, pullback.lift_snd, Scheme.homOfLE_ι_assoc, pullback.lift_snd]
  have hVD : V ≤ E₂.D hS := E₂.le_D_of_hom hS V hUXV g hg
  have hmono : E₂.Z hS ⊆ E.Z hS := by
    intro ω hω hω'
    apply hω
    show E₂.ρ.base ω ∈ (E₂.D hS : Set ↥E₂.X)
    apply hVD
    show π.base (E₂.ρ.base ω) ∈ (E.D hS : Set ↥E.X)
    rw [← Scheme.Hom.comp_apply, ← hρ]
    simpa [Level.Z] using hω'
  refine ⟨E₂, ⟨a'', ha''⟩, hmono, ?_⟩

  intro b hb heq
  have hs₂ : Spec.map (CommRingCat.ofHom (algebraMap R R'')) = E₂.t R'' ≫ E₂.s := by
    rw [hE₂t, Category.id_comp]
  let P₂ : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ⟶ E₂.X := E₂.P _ hs₂ a ha
  have hP₂π : P₂ ≫ π = E.P _ hs a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, hπ₁, E₂.P_prX, E.P_prX]
    · rw [Category.assoc, hπ₂, E₂.P_snd_assoc, E.P_snd, hE₂t, Category.id_comp]

  let θ₁ : E₂.X ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) :=
    pullback.lift (E₂.prX ≫ pullback.fst y y) (pullback.snd _ E₂.s) (by rw [Category.assoc]; exact pullback.condition)
  let θ₂ : E₂.X ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) :=
    pullback.lift (E₂.prX ≫ pullback.snd y y) (pullback.snd _ E₂.s)
      (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)
  have hθ : (θ₁ ≫ ι₂.1) ≫ y'' = (θ₂ ≫ ι₂.1) ≫ y'' := by
    simp only [Category.assoc, ι₂.2, θ₁, θ₂, pullback.lift_snd]
  let κ₂ : E₂.X ⟶ pullback y'' y'' := pullback.lift (θ₁ ≫ ι₂.1) (θ₂ ≫ ι₂.1) hθ

  let a₂ : Spec (CommRingCat.of R'') ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) :=
    pullback.lift a (𝟙 _) (by rw [Category.id_comp]; exact ha)
  have hq₁ : (P₂ ≫ κ₂) ≫ pullback.fst y'' y'' =
      𝟙 _ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ a₂ ≫ ι₂.1 := by
    rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, E₂.P_prX_assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, E₂.P_snd, Category.assoc, pullback.lift_snd, hE₂t]
  have hq₂ : (P₂ ≫ κ₂) ≫ pullback.snd y'' y'' = 𝟙 _ ≫ ι₂.1 := by
    rw [Category.id_comp, Category.assoc, pullback.lift_snd, ← Category.assoc]
    conv_rhs => rw [← Category.id_comp ι₂.1]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, E₂.P_prX_assoc, pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, E₂.P_snd, hE₂t, Category.id_comp, Category.comp_id]
  have hrange := hprog a₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (𝟙 _) (P₂ ≫ κ₂) hq₁ hq₂
  have hbD₂ : κ₂.base (P₂.base b) ∈ (D₂ : Set ↥(pullback y'' y'')) :=
    hrange ⟨b, (Scheme.Hom.comp_apply _ _ _).symm⟩

  let V₂ : E₂.X.Opens := κ₂ ⁻¹ᵁ D₂
  let t' : (E₂.UX : Scheme.{u}) ⟶ Spec (CommRingCat.of R'') := E₂.UX.ι ≫ pullback.snd _ E₂.s
  have hw : (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι ≫ pullback.fst y y ≫ y) =
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, pullback.condition, Category.assoc]
  have hwa : (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι ≫ pullback.fst y y) ≫ y =
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    simp only [Category.assoc]; exact hw
  have hwb : (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι ≫ pullback.snd y y) ≫ y =
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    simp only [Category.assoc]; rw [← pullback.condition (f := y) (g := y)]; exact hw
  have hwc : (E₂.prX.resLE U E₂.UX le_rfl ≫ m.1) ≫ y = t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) := by
    rw [Category.assoc, m.2]; exact hw
  let wpt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) (U.ι ≫ pullback.fst y y ≫ y) :=
    ⟨E₂.prX.resLE U E₂.UX le_rfl, hw⟩
  let apt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) y := ⟨_, hwa⟩
  let bpt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) y := ⟨_, hwb⟩
  let cpt : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R''))) y := ⟨_, hwc⟩
  obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := hext₂ t' wpt apt bpt cpt rfl rfl rfl
  have hθ₁ : E₂.UX.ι ≫ θ₁ =
      (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) apt).1 := by
    rw [RelativeGroupLaw.baseChangePointOfBase_coe]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      show E₂.UX.ι ≫ E₂.prX ≫ pullback.fst y y = (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι) ≫ pullback.fst y y
      rw [Scheme.Hom.resLE_comp_ι, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hθ₂ : E₂.UX.ι ≫ θ₂ =
      (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) bpt).1 := by
    rw [RelativeGroupLaw.baseChangePointOfBase_coe]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      show E₂.UX.ι ≫ E₂.prX ≫ pullback.snd y y = (E₂.prX.resLE U E₂.UX le_rfl ≫ U.ι) ≫ pullback.snd y y
      rw [Scheme.Hom.resLE_comp_ι, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hκ₂ : E₂.UX.ι ≫ κ₂ = w'.1 ≫ U''.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hθ₁, Category.assoc, hw'₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hθ₂, Category.assoc, hw'₂]
  have hUXV₂ : E₂.UX ≤ V₂ := by
    intro q hq
    show κ₂.base q ∈ (D₂ : Set ↥(pullback y'' y''))
    apply hle
    have : κ₂.base q = (E₂.UX.ι ≫ κ₂).base ⟨q, hq⟩ := by rw [Scheme.Hom.comp_apply]; rfl
    rw [this, hκ₂, Scheme.Hom.comp_apply]
    exact (w'.1.base _).2
  let g₂ : (V₂ : Scheme.{u}) ⟶ Y'' := κ₂.resLE D₂ V₂ le_rfl ≫ M₂.1
  have hg₂ : E₂.X.homOfLE hUXV₂ ≫ g₂ = E₂.hom := by
    have hww : E₂.X.homOfLE hUXV₂ ≫ κ₂.resLE D₂ V₂ le_rfl = w'.1 ≫ (pullback y'' y'').homOfLE hle := by
      rw [← cancel_mono D₂.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc, hκ₂,
        Category.assoc, Scheme.homOfLE_ι]
    simp only [g₂, ← Category.assoc, hww]
    rw [Category.assoc, hM₂, hw'₃, RelativeGroupLaw.baseChangePointOfBase_coe]
    show _ = pullback.lift _ _ hcond₂ ≫ ι₂.1
    rfl
  have hV₂D : V₂ ≤ E₂.D hS := E₂.le_D_of_hom hS V₂ hUXV₂ g₂ hg₂
  have hbD : P₂.base b ∈ (E₂.D hS : Set ↥E₂.X) := hV₂D hbD₂

  have hbcl : (pullback.snd _ E₂.s).base (P₂.base b) = IsLocalRing.closedPoint R'' := by
    by_contra hne
    apply hb
    apply E.UX_le_D hS
    show E.prX.base ((E.P _ hs a ha).base b) ∈ U
    rw [← hP₂π, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ E.prX, hπ₁]
    exact E₂.mem_UX_of_ne hS _ hne

  haveI : IsLocalHom (CommRingCat.ofHom ψ).hom := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have := hψm x ((IsLocalRing.mem_maximalIdeal x).mpr hxu)
    rw [show (CommRingCat.ofHom ψ).hom x = ψ x from rfl, this] at hx
    exact not_isUnit_zero hx
  have hpt : (pullback.snd _ E₂.s).base (P₂.base b) =
      (Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint K) := by
    rw [hbcl]
    exact (Spec_closedPoint (R := CommRingCat.of R'') (S := CommRingCat.of K) (f := CommRingCat.ofHom ψ)).symm
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd _ E₂.s)
    (g := Spec.map (CommRingCat.ofHom ψ)) (P₂.base b) (IsLocalRing.closedPoint K) hpt
  let lam : pullback (pullback.snd _ E₂.s) (Spec.map (CommRingCat.ofHom ψ)) ⟶ Ω y φ₀ :=
    pullback.lift (pullback.fst _ _ ≫ E₂.prX) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition (f := pullback.fst y y ≫ y) (g := E₂.s), ← Category.assoc,
            pullback.condition (f := pullback.snd (pullback.fst y y ≫ y) E₂.s) (g := Spec.map (CommRingCat.ofHom ψ)),
            Category.assoc]
          exact congrArg (pullback.snd _ _ ≫ ·) E₂.specMap_φ_comp_s)
  have hlam : lam ≫ E₂.ρ = pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp only [lam, Level.ρ, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [lam, Level.ρ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact pullback.condition.symm
  let ω : ↥(Ω y φ₀) := lam.base z
  have hω₂ : E₂.ρ.base ω = P₂.base b := by
    show (lam ≫ E₂.ρ).base z = _
    rw [hlam]; exact hz₁
  have hωE : E.ρ.base ω = (E.P _ hs a ha).base b := by
    rw [hρ, Scheme.Hom.comp_apply, hω₂, ← Scheme.Hom.comp_apply, hP₂π]
  have h₁ : ω ∈ E.Z hS := by
    show E.ρ.base ω ∈ (E.D hS : Set ↥E.X)ᶜ
    rw [hωE]; exact hb
  have h₂ : ω ∉ E₂.Z hS := by
    show ¬ (E₂.ρ.base ω ∈ (E₂.D hS : Set ↥E₂.X)ᶜ)
    rw [hω₂]; exact fun h => h hbD
  exact h₂ (heq ▸ h₁)

end Next

end Level
p2m_reactivate "P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing.P2mIterFin.Level"

section Final

variable [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem s₀_eq_id : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (CommRingCat.of R)) := by
  show Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

private noncomputable def _root_.P2mIterFin.base (hS : Strict y U m) (hφ₀m : ∀ x ∈ IsLocalRing.maximalIdeal R, φ₀ x = 0) :
    Level y U m K φ₀ where
  R' := R
  φ := φ₀
  hφ := RingHom.comp_id _
  hφm := hφ₀m
  Y' := Y
  y' := y
  ι := ⟨pullback.fst y _, by rw [pullback.condition, s₀_eq_id, Category.comp_id]⟩
  oi := by
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by rw [s₀_eq_id]; infer_instance
    exact MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ this
  hgen := fun p _ => by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by rw [s₀_eq_id]; infer_instance
    exact (MorphismProperty.pullback_fst (P := @Surjective) y _ this).surj p
  hmax := fun p _ => by
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by rw [s₀_eq_id]; infer_instance
    exact (MorphismProperty.pullback_fst (P := @Surjective) y _ this).surj p
  U' := U
  m' := m
  hU'₁ := hS.hU₁
  hU'₂ := hS.hU₂
  hΦ' := hS.hΦ
  hΦ'₁ := hS.hΦ₁
  hΦ'₂ := hS.hΦ₂
  hΨ' := hS.hΨ
  hΨ'₁ := hS.hΨ₁
  hΨ'₂ := hS.hΨ₂
  hassoc' := hS.hassoc
  hext := by
    intro T t' w a b c ha hb hc
    refine ⟨⟨w.1, by rw [w.2, s₀_eq_id, Category.comp_id]⟩, ?_, ?_, ?_⟩
    · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; exact ha.symm
    · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; exact hb.symm
    · rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]; exact hc.symm

p2m_export "P2mIterFin" "base"
end Final
p2m_reactivate "P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing.P2mIterFin.Level"

end Main
p2m_reactivate "P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing.P2mIterFin.Level"

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hS : Strict y U m) (hYk : ∃ x : Y, y.base x = IsLocalRing.closedPoint R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
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
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
          (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ : Module.FaithfullyFlat R' R'')
          (a : Spec (CommRingCat.of R'') ⟶ Y),
        a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))),
          τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ∧
          ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
            w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
            w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
            v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
            v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
            x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) := by
  classical

  let k := IsLocalRing.ResidueField R
  let K := AlgebraicClosure k
  let φ₀ : R →+* K := (algebraMap k K).comp (IsLocalRing.residue R)
  have hφ₀m : ∀ x ∈ IsLocalRing.maximalIdeal R, φ₀ x = 0 := fun x hx => by
    show algebraMap k K (IsLocalRing.residue R x) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
  have hE₀ : (base (K := K) hS hφ₀m).R' = R := rfl

  obtain ⟨x₀, hx₀⟩ := hYk
  obtain ⟨R₁, _, _, _, _, _, _, _, _, _, a₁, -, ha₁, -⟩ :=
    AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
      y ⊤ x₀ hx₀ trivial
  letI : Algebra (base (K := K) hS hφ₀m).R' R₁ := ‹Algebra R R₁›
  haveI : Module.Finite (base (K := K) hS hφ₀m).R' R₁ := ‹Module.Finite R R₁›
  haveI : Algebra.Etale (base (K := K) hS hφ₀m).R' R₁ := ‹Algebra.Etale R R₁›
  haveI : Module.FaithfullyFlat (base (K := K) hS hφ₀m).R' R₁ := ‹Module.FaithfullyFlat R R₁›
  haveI : IsScalarTower R (base (K := K) hS hφ₀m).R' R₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨E₁, hE₁sec, -, -⟩ := (base (K := K) hS hφ₀m).exists_next hS
    ((base (K := K) hS hφ₀m).t R₁ ≫ (base (K := K) hS hφ₀m).s) rfl a₁ (ha₁.trans (base (K := K) hS hφ₀m).s₂_eq)

  haveI : LocallyOfFiniteType (pullback.snd (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀))) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  haveI : QuasiCompact (pullback.snd (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀))) :=
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  haveI : IsLocallyNoetherian (Level.Ω y φ₀) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀)))
  haveI : CompactSpace ↥(Level.Ω y φ₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (pullback.fst y y ≫ y) (Spec.map (CommRingCat.ofHom φ₀)))
  haveI : IsNoetherian (Level.Ω y φ₀) := {}

  obtain ⟨C, ⟨E, hEsec, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := TopologicalSpace.Closeds ↥(Level.Ω y φ₀)))
    {C | ∃ E : Level y U m K φ₀, E.HasSec ∧ (⟨E.Z hS, E.isClosed_Z hS⟩ : TopologicalSpace.Closeds ↥(Level.Ω y φ₀)) = C}
    ⟨_, E₁, hE₁sec, rfl⟩

  refine ⟨E.R', inferInstance, inferInstance, inferInstance, E.alg, E.fin, E.et, E.ff, E.Y', E.y', E.ι, E.U', E.m',
    E.sm, E.sep, E.loft, E.qc, E.oi, E.hgen, E.hmax, E.hU'₁, E.hU'₂, E.hΦ', E.hΦ'₁, E.hΦ'₂, E.hΨ', E.hΨ'₁, E.hΨ'₂,
    E.hassoc', E.hext, hEsec, ?_⟩
  intro R'' _ _ _ _ _ _ _ a ha
  by_contra hn
  letI : Algebra R R'' := ((algebraMap E.R' R'').comp (algebraMap R E.R')).toAlgebra
  haveI : IsScalarTower R E.R' R'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite R R'' := Module.Finite.trans E.R' R''
  haveI : Algebra.Etale R R'' := Algebra.Etale.comp R E.R' R''
  haveI : Module.FaithfullyFlat R R'' := Module.FaithfullyFlat.trans R E.R' R''
  obtain ⟨b, hb⟩ := E.exists_not_mem_D hS (E.t R'' ≫ E.s) rfl a ha hn
  obtain ⟨E₂, hE₂sec, hsub, hne⟩ := E.exists_next hS (E.t R'' ≫ E.s) rfl a ha
  refine hmin ⟨E₂.Z hS, E₂.isClosed_Z hS⟩ ⟨E₂, hE₂sec, rfl⟩ (lt_of_le_of_ne hsub ?_)
  intro h
  exact hne b hb (congrArg (fun C : TopologicalSpace.Closeds ↥(Level.Ω y φ₀) => (C : Set ↥(Level.Ω y φ₀))) h)

end P2mIterFin
p2m_reactivate "P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing.P2mIterFin.Level P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing.P2mIterFin"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (hYk : ∃ x : Y, y.base x = IsLocalRing.closedPoint R)
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
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
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
          (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ : Module.FaithfullyFlat R' R'')
          (a : Spec (CommRingCat.of R'') ⟶ Y),
        a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))),
          τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ∧
          ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
            w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
            w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
            v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
            v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
            x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :=
  P2mIterFin.main y U m ⟨hU₁, hU₂, hΦ, hΦ₁, hΦ₂, hΨ, hΨ₁, hΨ₂, hassoc, hUK⟩ hYk

end S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
end P2MW
export P2MW.S_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing (solution)
