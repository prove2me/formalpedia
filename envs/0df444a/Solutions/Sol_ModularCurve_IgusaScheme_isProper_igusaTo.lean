-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isProper_igusaTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b89dc0e7-ecba-5391-bc0c-5b85cd9c8551

import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull"
p2m_open "ModularCurve"

namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull jFull_ne_zero chartAlg subset_chartAlg coe_chartIncl chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition igusaTo ιFin_igusaTo ιInf_igusaTo mem_range_ιFin_or_mem_range_ιInf"
p2m_open "ModularCurve.IgusaScheme"

namespace Proper

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

set_option quotPrecheck false in
local notation "X₀" => ModularCurve.IgusaScheme N ℓ

theorem ιFin_eq_ιInf_iff (x₀ : XFin N ℓ) (xi : XInf N ℓ) :
    (ιFin N ℓ).base x₀ = (ιInf N ℓ).base xi ↔
      ∃ u : XMid N ℓ, (fFin N ℓ).base u = x₀ ∧ (fInf N ℓ).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin N ℓ) (fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · cases fi
      cases fj
      exact ⟨u, h₁, h₂⟩
    · cases fj
    · cases fi
  · rintro ⟨u, rfl, rfl⟩
    change (fFin N ℓ ≫ ιFin N ℓ).base u = (fInf N ℓ ≫ ιInf N ℓ).base u
    rw [glue_condition]

theorem range_fInf : Set.range (fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf N ℓ))) :
      Set (PrimeSpectrum (chartAlgInf N ℓ))) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jInvChartInf N ℓ)

theorem range_fFin : Set.range (fFin N ℓ).base =
    ((PrimeSpectrum.basicOpen (jChartFin N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin N ℓ))) :
      Set (PrimeSpectrum (chartAlgFin N ℓ))) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jChartFin N ℓ)

theorem ιInf_mem_range_ιFin_iff (xi : XInf N ℓ) :
    (ιInf N ℓ).base xi ∈ Set.range (ιFin N ℓ).base ↔ jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨u, -, hu⟩ := (ιFin_eq_ιInf_iff N ℓ x₀ xi).mp h
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(fFin N ℓ).base u, (ιFin_eq_ιInf_iff N ℓ _ _).mpr ⟨u, rfl, rfl⟩⟩

theorem ιFin_mem_range_ιInf_iff (x₀ : XFin N ℓ) :
    (ιFin N ℓ).base x₀ ∈ Set.range (ιInf N ℓ).base ↔ jChartFin N ℓ ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨u, hu, -⟩ := (ιFin_eq_ιInf_iff N ℓ x₀ xi).mp h.symm
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(fInf N ℓ).base u, ((ιFin_eq_ιInf_iff N ℓ _ _).mpr ⟨u, rfl, rfl⟩).symm⟩

theorem mem_range_ιInf_of_not_mem_range_ιFin {x : X₀}
    (hx : x ∉ Set.range (ιFin N ℓ).base) : x ∈ Set.range (ιInf N ℓ).base :=
  (mem_range_ιFin_or_mem_range_ιInf N ℓ x).resolve_left hx

abbrev ιMid : XMid N ℓ ⟶ X₀ := fFin N ℓ ≫ ιFin N ℓ

scoped instance isOpenImmersion_ιMid : IsOpenImmersion (ιMid N ℓ) := IsOpenImmersion.comp _ _

theorem ιMid_eq' : ιMid N ℓ = fInf N ℓ ≫ ιInf N ℓ := glue_condition N ℓ

scoped instance compactSpace : CompactSpace X₀ := by
  refine ⟨?_⟩
  have h : Set.range (ιFin N ℓ).base ∪ Set.range (ιInf N ℓ).base = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_range_ιFin_or_mem_range_ιInf N ℓ x
  rw [← h]
  exact (isCompact_range (ιFin N ℓ).base.hom.continuous).union
    (isCompact_range (ιInf N ℓ).base.hom.continuous)

scoped instance quasiCompact_igusaTo : QuasiCompact (igusaTo N ℓ) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

scoped instance isNoetherianRing_base : IsNoetherianRing ℤℓ :=
  haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  inferInstance

section FiniteType

variable [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)]
  [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)]

scoped instance isNoetherianRing_chartAlgFin : IsNoetherianRing (chartAlgFin N ℓ) :=
  Algebra.FiniteType.isNoetherianRing ℤℓ _

scoped instance isNoetherianRing_chartAlgInf : IsNoetherianRing (chartAlgInf N ℓ) :=
  Algebra.FiniteType.isNoetherianRing ℤℓ _

scoped instance isNoetherianRing_chartAlgMid : IsNoetherianRing (chartAlgMid N ℓ) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact IsLocalization.isNoetherianRing (Submonoid.powers (jChartFin N ℓ)) _ inferInstance

scoped instance isLocallyNoetherian : IsLocallyNoetherian X₀ := by
  refine (isLocallyNoetherian_iff_openCover (X := X₀)
    (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ)))).mpr ?_
  rintro (_ | _ | _)
  · change IsLocallyNoetherian (XMid N ℓ)
    infer_instance
  · change IsLocallyNoetherian (XFin N ℓ)
    infer_instance
  · change IsLocallyNoetherian (XInf N ℓ)
    infer_instance

scoped instance quasiSeparated_igusaTo : QuasiSeparated (igusaTo N ℓ) :=
  QuasiSeparated.of_quasiSeparatedSpace _

scoped instance locallyOfFiniteType_igusaTo : LocallyOfFiniteType (igusaTo N ℓ) := by
  have h₀' : LocallyOfFiniteType (ιFin N ℓ ≫ igusaTo N ℓ) := by
    rw [ιFin_igusaTo, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (ιInf N ℓ ≫ igusaTo N ℓ) := by
    rw [ιInf_igusaTo, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).f none ≫
        igusaTo N ℓ = fFin N ℓ ≫ (ιFin N ℓ ≫ igusaTo N ℓ) := by
      show colimit.ι (span (fFin N ℓ) (fInf N ℓ)) none ≫ igusaTo N ℓ = _
      rw [← colimit.w (span (fFin N ℓ) (fInf N ℓ)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs (LocallyOfFiniteType (fFin N ℓ ≫ (ιFin N ℓ ≫ igusaTo N ℓ)))
  · change LocallyOfFiniteType (ιFin N ℓ ≫ igusaTo N ℓ)
    exact h₀'
  · change LocallyOfFiniteType (ιInf N ℓ ≫ igusaTo N ℓ)
    exact hInf'

end FiniteType

section RingLemmas

variable {B R K : Type*} [CommRing B] [CommRing R] [CommRing K]

def liftOfRange (j : R →+* K) (hj : Function.Injective j) (g : B →+* K)
    (h : ∀ b, g b ∈ j.range) : B →+* R :=
  (RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (g.codRestrict j.range h)

theorem liftOfRange_spec (j : R →+* K) (hj : Function.Injective j) (g : B →+* K)
    (h : ∀ b, g b ∈ j.range) (b : B) : j (liftOfRange j hj g h b) = g b := by
  set e := RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩
  have : e (e.symm ⟨g b, h b⟩) = ⟨g b, h b⟩ := e.apply_symm_apply _
  exact congrArg Subtype.val this

theorem comp_liftOfRange (j : R →+* K) (hj : Function.Injective j) (g : B →+* K)
    (h : ∀ b, g b ∈ j.range) : j.comp (liftOfRange j hj g h) = g :=
  RingHom.ext (liftOfRange_spec j hj g h)

end RingLemmas

theorem SpecMap_cancel {R K Y : CommRingCat.{0}} (j : R ⟶ K) (hj : Function.Injective j)
    (u v : Spec R ⟶ Spec Y) (h : Spec.map j ≫ u = Spec.map j ≫ v) : u = v := by
  haveI : Mono j := ConcreteCategory.mono_of_injective j hj
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [cancel_mono] at h'
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, h']

section Existence

variable {N ℓ}

structure ChartDatum (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) where

  g : CommRingCat.of (A : Type) ⟶ CommRingCat.of S.K
  fac : Spec.map g ≫ ι = S.i₁
  compat : CommRingCat.ofHom (algebraMap ℤℓ A) ≫ g =
    Spec.preimage S.i₂ ≫ CommRingCat.ofHom (algebraMap S.R S.K)

def chartDatumOfMem (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) [IsOpenImmersion ι]
    (hι : ι ≫ igusaTo N ℓ = Spec.map (CommRingCat.ofHom (algebraMap ℤℓ A)))
    (hx : S.i₁.base (closedPoint S.K) ∈ Set.range ι.base) : ChartDatum S A ι := by
  have H : Set.range S.i₁.base ⊆ Set.range ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint S.K := Subsingleton.elim _ _
    exact hx
  refine ⟨Spec.preimage (IsOpenImmersion.lift ι S.i₁ H), ?_, ?_⟩
  · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← hι,
      ← Category.assoc, IsOpenImmersion.lift_fac]
    exact S.commSq.w

theorem hasLift_of_chartDatum (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι)
    (hrange : ∀ a : A, D.g.hom a ∈ (algebraMap S.R S.K).range) : S.commSq.HasLift := by
  let ψ : (A : Type) →+* S.R :=
    liftOfRange (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) D.g.hom hrange
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap S.R S.K) = D.g := by
    ext a
    exact liftOfRange_spec (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) _ hrange a
  let l : Spec (.of S.R) ⟶ X₀ := Spec.map (CommRingCat.ofHom ψ) ≫ ι
  have fac_left : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ := by
    rw [← D.fac, ← hψ, Spec.map_comp, Category.assoc]
  refine CommSq.HasLift.mk' ⟨l, fac_left, ?_⟩
  apply SpecMap_cancel (CommRingCat.ofHom (algebraMap S.R S.K)) (IsFractionRing.injective S.R S.K)
  rw [← Category.assoc, fac_left, S.commSq.w]

theorem algebraMap_mem_range (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι) (c : ℤℓ) :
    D.g.hom (algebraMap ℤℓ A c) ∈ (algebraMap S.R S.K).range := by
  refine ⟨(Spec.preimage S.i₂).hom c, ?_⟩
  have := congrArg (fun f : CommRingCat.of ℤℓ ⟶ CommRingCat.of S.K => f.hom c) D.compat
  exact this.symm

theorem mem_range_of_isIntegral (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι)
    (T : Set FN) (hTA : T ⊆ A) (hAT : A ≤ chartAlg N ℓ T)
    (hT : ∀ (t : FN) (ht : t ∈ T), D.g.hom ⟨t, hTA ht⟩ ∈ (algebraMap S.R S.K).range) (a : A) :
    D.g.hom a ∈ (algebraMap S.R S.K).range := by
  classical
  haveI : IsIntegrallyClosed S.R := GCDMonoid.toIsIntegrallyClosed
  have hadjA : Algebra.adjoin ℤℓ T ≤ A := Algebra.adjoin_le hTA
  let incl : Algebra.adjoin ℤℓ T →+* A := (Subalgebra.inclusion hadjA).toRingHom
  let g₀ : Algebra.adjoin ℤℓ T →+* S.K := D.g.hom.comp incl

  have hg₀ : ∀ (y : FN) (hy : y ∈ Algebra.adjoin ℤℓ T),
      D.g.hom ⟨y, hadjA hy⟩ ∈ (algebraMap S.R S.K).range := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact hT y hy
    | algebraMap c => exact algebraMap_mem_range S A ι D c
    | add y z hy hz ihy ihz =>
      have : (⟨y + z, hadjA (add_mem hy hz)⟩ : A) = ⟨y, hadjA hy⟩ + ⟨z, hadjA hz⟩ := rfl
      rw [this, map_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      have : (⟨y * z, hadjA (mul_mem hy hz)⟩ : A) = ⟨y, hadjA hy⟩ * ⟨z, hadjA hz⟩ := rfl
      rw [this, map_mul]
      exact mul_mem ihy ihz
  have hg₀' : ∀ y, g₀ y ∈ (algebraMap S.R S.K).range := fun y => hg₀ y y.2
  let g₁ : Algebra.adjoin ℤℓ T →+* S.R :=
    liftOfRange (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) g₀ hg₀'
  have hg₁ : (algebraMap S.R S.K).comp g₁ = g₀ := comp_liftOfRange _ _ _ _

  obtain ⟨f, hf, hfa⟩ : IsIntegral (Algebra.adjoin ℤℓ T) (a : FN) := hAT a.2
  have hval : (algebraMap (Algebra.adjoin ℤℓ T) FN) = A.val.toRingHom.comp incl :=
    RingHom.ext fun _ => rfl
  have hfaA : Polynomial.eval₂ incl a f = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ f incl A.val.toRingHom a
    change A.val.toRingHom (Polynomial.eval₂ incl a f) = ((0 : A) : FN)
    rw [h, ← hval]
    exact hfa
  have hfaK : Polynomial.eval₂ g₀ (D.g.hom a) f = 0 := by
    have h := Polynomial.hom_eval₂ f incl D.g.hom a
    rw [hfaA, map_zero] at h
    exact h.symm
  have hint : IsIntegral S.R (D.g.hom a) := by
    refine ⟨f.map g₁, hf.map g₁, ?_⟩
    rw [Polynomial.eval₂_map, hg₁, hfaK]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨y, hy⟩

theorem ιFin_igusaTo' : ιFin N ℓ ≫ igusaTo N ℓ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgFin N ℓ))) := ιFin_igusaTo N ℓ

theorem ιInf_igusaTo' : ιInf N ℓ ≫ igusaTo N ℓ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgInf N ℓ))) := ιInf_igusaTo N ℓ

theorem ιMid_igusaTo : ιMid N ℓ ≫ igusaTo N ℓ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤℓ (chartAlgMid N ℓ))) := by
  rw [Category.assoc, ιFin_igusaTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom
    (RingHom.ext fun c => ((inclFin N ℓ).commutes c)))

theorem inclFin_j_mul_inclInf_jInv :
    inclFin N ℓ (jChartFin N ℓ) * inclInf N ℓ (jInvChartInf N ℓ) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf,
      Subalgebra.coe_one, mul_inv_cancel₀ (jFull_ne_zero N)])

theorem base_eq (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι) :
    ι.base ((Spec.map D.g).base (closedPoint S.K)) = S.i₁.base (closedPoint S.K) := by
  rw [← D.fac]
  rfl

theorem not_mem_of_ne_zero (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι) (a : A) (ha : D.g.hom a ≠ 0) :
    a ∉ ((Spec.map D.g).base (closedPoint S.K)).asIdeal := by
  intro hmem
  apply ha
  have h : D.g.hom a ∈ (closedPoint S.K).asIdeal := hmem
  change D.g.hom a ∈ maximalIdeal S.K at h
  rwa [maximalIdeal_eq_bot, Ideal.mem_bot] at h

theorem comp_eq_of_fac (S : ValuativeCommSq (igusaTo N ℓ)) (A : Subalgebra ℤℓ FN)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) [IsOpenImmersion ι] (D : ChartDatum S A ι)
    (DMid : ChartDatum S (chartAlgMid N ℓ) (ιMid N ℓ)) (i : A →ₐ[ℤℓ] chartAlgMid N ℓ)
    (hi : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ι = ιMid N ℓ) :
    CommRingCat.ofHom i.toRingHom ≫ DMid.g = D.g := by
  apply Spec.map_injective
  rw [← cancel_mono ι, Spec.map_comp, Category.assoc, hi, D.fac, DMid.fac]

theorem hasLift_of_mem_range_ιFin (S : ValuativeCommSq (igusaTo N ℓ))
    (hx : S.i₁.base (closedPoint S.K) ∈ Set.range (ιFin N ℓ).base) : S.commSq.HasLift := by
  let D := chartDatumOfMem S (chartAlgFin N ℓ) (ιFin N ℓ) (ιFin_igusaTo' ) hx

  have hfin : D.g.hom (jChartFin N ℓ) ∈ (algebraMap S.R S.K).range → S.commSq.HasLift := by
    intro hj
    refine hasLift_of_chartDatum S _ _ D (mem_range_of_isIntegral S _ _ D {jFull N}
      (subset_chartAlg N ℓ _) le_rfl ?_)
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hj
  rcases ValuationRing.isInteger_or_isInteger S.R (D.g.hom (jChartFin N ℓ)) with h | h
  · exact hfin (RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h))
  by_cases hj0 : D.g.hom (jChartFin N ℓ) = 0
  · exact hfin (hj0 ▸ zero_mem _)

  have hp := base_eq S _ _ D
  have hjp := not_mem_of_ne_zero S _ _ D _ hj0
  have hxInf : S.i₁.base (closedPoint S.K) ∈ Set.range (ιInf N ℓ).base := by
    rw [← hp]
    exact (ιFin_mem_range_ιInf_iff N ℓ _).mpr hjp
  obtain ⟨q, hq⟩ := hxInf
  obtain ⟨u, hu₁, hu₂⟩ := (ιFin_eq_ιInf_iff N ℓ _ q).mp (hp.trans hq.symm)
  have hxMid : S.i₁.base (closedPoint S.K) ∈ Set.range (ιMid N ℓ).base := by
    refine ⟨u, ?_⟩
    rw [← hp, ← hu₁]
    rfl
  let DInf := chartDatumOfMem S (chartAlgInf N ℓ) (ιInf N ℓ) ιInf_igusaTo' ⟨q, hq⟩
  let DMid := chartDatumOfMem S (chartAlgMid N ℓ) (ιMid N ℓ) ιMid_igusaTo hxMid
  have cFin : CommRingCat.ofHom (inclFin N ℓ).toRingHom ≫ DMid.g = D.g :=
    comp_eq_of_fac S _ _ D DMid (inclFin N ℓ) rfl
  have cInf : CommRingCat.ofHom (inclInf N ℓ).toRingHom ≫ DMid.g = DInf.g :=
    comp_eq_of_fac S _ _ DInf DMid (inclInf N ℓ) (ιMid_eq' N ℓ).symm
  have hprod : D.g.hom (jChartFin N ℓ) * DInf.g.hom (jInvChartInf N ℓ) = 1 := by
    rw [← cFin, ← cInf]
    change DMid.g.hom (inclFin N ℓ (jChartFin N ℓ)) * DMid.g.hom (inclInf N ℓ (jInvChartInf N ℓ)) = 1
    rw [← map_mul, inclFin_j_mul_inclInf_jInv, map_one]
  have hinv : DInf.g.hom (jInvChartInf N ℓ) = (D.g.hom (jChartFin N ℓ))⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  refine hasLift_of_chartDatum S _ _ DInf (mem_range_of_isIntegral S _ _ DInf {(jFull N)⁻¹}
    (subset_chartAlg N ℓ _) le_rfl ?_)
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  subst ht
  change DInf.g.hom (jInvChartInf N ℓ) ∈ _
  rw [hinv]
  exact RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h)

theorem hasLift_of_mem_range_ιInf (S : ValuativeCommSq (igusaTo N ℓ))
    (hx : S.i₁.base (closedPoint S.K) ∈ Set.range (ιInf N ℓ).base) : S.commSq.HasLift := by
  by_cases hx' : S.i₁.base (closedPoint S.K) ∈ Set.range (ιFin N ℓ).base
  · exact hasLift_of_mem_range_ιFin S hx'

  let D := chartDatumOfMem S (chartAlgInf N ℓ) (ιInf N ℓ) ιInf_igusaTo' hx
  have hp := base_eq S _ _ D
  have hj0 : D.g.hom (jInvChartInf N ℓ) = 0 := by
    by_contra h
    apply hx'
    rw [← hp]
    exact (ιInf_mem_range_ιFin_iff N ℓ _).mpr (not_mem_of_ne_zero S _ _ D _ h)
  refine hasLift_of_chartDatum S _ _ D (mem_range_of_isIntegral S _ _ D {(jFull N)⁻¹}
    (subset_chartAlg N ℓ _) le_rfl ?_)
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  subst ht
  change D.g.hom (jInvChartInf N ℓ) ∈ _
  rw [hj0]
  exact zero_mem _

variable (N ℓ) in

theorem valuativeCriterion_existence : ValuativeCriterion.Existence (igusaTo N ℓ) := by
  intro S
  rcases mem_range_ιFin_or_mem_range_ιInf N ℓ (S.i₁.base (closedPoint S.K)) with hx | hx
  · exact hasLift_of_mem_range_ιFin S hx
  · exact hasLift_of_mem_range_ιInf S hx

end Existence

section Uniqueness

variable {N ℓ}

theorem range_subset_of_closedPoint_mem {R : Type} [CommRing R] [IsLocalRing R]
    (l : Spec (CommRingCat.of R) ⟶ X₀) {Y : Scheme.{0}} (ι : Y ⟶ X₀)
    [IsOpenImmersion ι] (h : l.base (closedPoint R) ∈ Set.range ι.base) :
    Set.range l.base ⊆ Set.range ι.base := by
  rintro _ ⟨z, rfl⟩
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem l (U := ι.opensRange) h
  have hz : z ∈ l ⁻¹ᵁ ι.opensRange := by rw [htop]; trivial
  exact hz

theorem liftStruct_eq_of_mem_range {A : Type} [CommRing A]
    (ιA : Spec (CommRingCat.of A) ⟶ X₀) [IsOpenImmersion ιA]
    (S : ValuativeCommSq (igusaTo N ℓ)) (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range ιA.base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range ιA.base) : l₁ = l₂ := by
  have H₁ := range_subset_of_closedPoint_mem l₁.l ιA h₁
  have H₂ := range_subset_of_closedPoint_mem l₂.l ιA h₂
  let m₁ := IsOpenImmersion.lift ιA l₁.l H₁
  let m₂ := IsOpenImmersion.lift ιA l₂.l H₂
  have e₁ : m₁ ≫ ιA = l₁.l := IsOpenImmersion.lift_fac _ _ _
  have e₂ : m₂ ≫ ιA = l₂.l := IsOpenImmersion.lift_fac _ _ _
  have hF : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₁ =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₂ := by
    rw [← cancel_mono ιA, Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
  haveI : Mono (CommRingCat.ofHom (algebraMap S.R S.K)) :=
    ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)
  have hm : m₁ = m₂ := by
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, ← Spec.map_comp, ← Spec.map_comp] at hF
    have := Spec.map_injective hF
    rw [cancel_mono] at this
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, this]
  ext
  rw [← e₁, ← e₂, hm]

theorem false_of_liftStruct_cross (S : ValuativeCommSq (igusaTo N ℓ))
    (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιFin N ℓ).base)
    (h₁' : l₁.l.base (closedPoint S.R) ∉ Set.range (ιInf N ℓ).base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf N ℓ).base)
    (h₂' : l₂.l.base (closedPoint S.R) ∉ Set.range (ιFin N ℓ).base) : False := by
  have H₁ := range_subset_of_closedPoint_mem l₁.l (ιFin N ℓ) h₁
  have H₂ := range_subset_of_closedPoint_mem l₂.l (ιInf N ℓ) h₂
  let G₁ : CommRingCat.of (chartAlgFin N ℓ) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ιFin N ℓ) l₁.l H₁)
  let G₂ : CommRingCat.of (chartAlgInf N ℓ) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ιInf N ℓ) l₂.l H₂)
  have e₁ : Spec.map G₁ ≫ ιFin N ℓ = l₁.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have e₂ : Spec.map G₂ ≫ ιInf N ℓ = l₂.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have ht₁ : G₁ (jChartFin N ℓ) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₁'
    rw [← e₁, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ιFin_mem_range_ιInf_iff]
    exact hn
  have ht₂ : G₂ (jInvChartInf N ℓ) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₂'
    rw [← e₂, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ιInf_mem_range_ιFin_iff]
    exact hn
  let alg := CommRingCat.ofHom (algebraMap S.R S.K)
  have hov : Set.range (Spec.map alg ≫ Spec.map G₁).base ⊆ Set.range (fFin N ℓ).base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint S.K := Subsingleton.elim _ _
    have hx : (ιFin N ℓ).base ((Spec.map alg ≫ Spec.map G₁).base (closedPoint S.K)) ∈
        Set.range (ιInf N ℓ).base := by
      refine ⟨(Spec.map alg ≫ Spec.map G₂).base (closedPoint S.K), ?_⟩
      change ((Spec.map alg ≫ Spec.map G₂) ≫ ιInf N ℓ).base (closedPoint S.K) =
        ((Spec.map alg ≫ Spec.map G₁) ≫ ιFin N ℓ).base (closedPoint S.K)
      rw [Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
    rw [ιFin_mem_range_ιInf_iff] at hx
    rw [range_fFin]
    exact hx
  let u := IsOpenImmersion.lift (fFin N ℓ) (Spec.map alg ≫ Spec.map G₁) hov
  have hu₀ : u ≫ fFin N ℓ = Spec.map alg ≫ Spec.map G₁ := IsOpenImmersion.lift_fac _ _ _
  have hui : u ≫ fInf N ℓ = Spec.map alg ≫ Spec.map G₂ := by
    rw [← cancel_mono (ιInf N ℓ), Category.assoc, ← glue_condition, ← Category.assoc, hu₀,
      Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
  let W := Spec.preimage u
  have hW₀ : CommRingCat.ofHom (inclFin N ℓ).toRingHom ≫ W = G₁ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hu₀
  have hWi : CommRingCat.ofHom (inclInf N ℓ).toRingHom ≫ W = G₂ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hui
  have k₁ : W (inclFin N ℓ (jChartFin N ℓ)) = algebraMap S.R S.K (G₁ (jChartFin N ℓ)) :=
    congrArg (fun f : CommRingCat.of (chartAlgFin N ℓ) ⟶ CommRingCat.of S.K =>
      f (jChartFin N ℓ)) hW₀
  have k₂ : W (inclInf N ℓ (jInvChartInf N ℓ)) = algebraMap S.R S.K (G₂ (jInvChartInf N ℓ)) :=
    congrArg (fun f : CommRingCat.of (chartAlgInf N ℓ) ⟶ CommRingCat.of S.K =>
      f (jInvChartInf N ℓ)) hWi
  have hone : algebraMap S.R S.K (G₁ (jChartFin N ℓ) * G₂ (jInvChartInf N ℓ)) =
      algebraMap S.R S.K 1 := by
    rw [map_mul, map_one, ← k₁, ← k₂, ← map_mul, inclFin_j_mul_inclInf_jInv, map_one]
  have hone' := IsFractionRing.injective S.R S.K hone
  exact (maximalIdeal S.R).ne_top_iff_one.mp (maximalIdeal.isMaximal S.R).ne_top
    (hone' ▸ Ideal.mul_mem_right _ _ ht₁)

variable (N ℓ) in

theorem valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness (igusaTo N ℓ) := by
  intro S
  refine ⟨fun l₁ l₂ => ?_⟩
  by_cases a₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιFin N ℓ).base <;>
    by_cases a₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιFin N ℓ).base
  · exact liftStruct_eq_of_mem_range (ιFin N ℓ) S l₁ l₂ a₁ a₂
  · have b₂ := mem_range_ιInf_of_not_mem_range_ιFin N ℓ a₂
    by_cases b₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιInf N ℓ).base
    · exact liftStruct_eq_of_mem_range (ιInf N ℓ) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross S l₁ l₂ a₁ b₁ b₂ a₂).elim
  · have b₁ := mem_range_ιInf_of_not_mem_range_ιFin N ℓ a₁
    by_cases b₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf N ℓ).base
    · exact liftStruct_eq_of_mem_range (ιInf N ℓ) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross S l₂ l₁ a₂ b₂ b₁ a₁).elim
  · exact liftStruct_eq_of_mem_range (ιInf N ℓ) S l₁ l₂
      (mem_range_ιInf_of_not_mem_range_ιFin N ℓ a₁) (mem_range_ιInf_of_not_mem_range_ιFin N ℓ a₂)

end Uniqueness

theorem isProper_igusaTo
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)] :
    IsProper (igusaTo N ℓ) :=
  IsProper.of_valuativeCriterion (igusaTo N ℓ)
    ((ValuativeCriterion.iff).mpr
      ⟨valuativeCriterion_existence N ℓ, valuativeCriterion_uniqueness N ℓ⟩)

end Proper
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme.Proper"

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme.Proper P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme.Proper P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme.Proper P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve"

p2m_open "AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.ModularCurve.IgusaScheme"

theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)] :
    IsProper (igusaTo N ℓ) :=
  ModularCurve.IgusaScheme.Proper.isProper_igusaTo N ℓ

end S_ModularCurve_IgusaScheme_isProper_igusaTo
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo (solution)
