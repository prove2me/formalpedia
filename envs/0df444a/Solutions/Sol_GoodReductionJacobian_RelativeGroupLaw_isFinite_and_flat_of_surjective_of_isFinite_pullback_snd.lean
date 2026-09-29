-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a2b54ba0-7748-5e61-8db1-ba94cb7bb458

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mFlatIsog

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

section FinitePoints

variable {K : Type u} [Field K]

theorem finite_schemeHomOver_of_isFinite {H : Scheme.{u}} (g : H ⟶ Spec (CommRingCat.of K))
    [IsFinite g] (Ω : Type u) [Field Ω] (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K)) :
    Finite (SchemeHomOver t g) := by
  haveI : IsAffine H := isAffine_of_isAffineHom g
  have hfin : RingHom.Finite (g.appTop).hom :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance).2

  let iK : K →+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let iΩ : Γ(Spec (CommRingCat.of Ω), ⊤) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
  have hiK : Function.Surjective iK :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
  letI algH : Algebra K Γ(H, ⊤) := ((g.appTop).hom.comp iK).toAlgebra
  letI algΩ : Algebra K Ω := (iΩ.comp ((t.appTop).hom.comp iK)).toAlgebra
  haveI : Module.Finite K Γ(H, ⊤) := by
    have h : ((g.appTop).hom.comp iK).Finite := hfin.comp (RingHom.Finite.of_surjective iK hiK)
    exact h

  have hcomm : ∀ z : SchemeHomOver t g, ∀ c : K,
      iΩ ((z.1.appTop).hom ((g.appTop).hom (iK c))) = algebraMap K Ω c := by
    intro z c
    change iΩ ((g.appTop ≫ z.1.appTop).hom (iK c)) = iΩ ((t.appTop).hom (iK c))
    rw [← Scheme.Hom.comp_appTop, z.2]
  let Φ : SchemeHomOver t g → (Γ(H, ⊤) →ₐ[K] Ω) := fun z =>
    { toRingHom := iΩ.comp (z.1.appTop).hom
      commutes' := fun c => hcomm z c }
  have hΦ : Function.Injective Φ := by
    intro z w h
    have h1 : iΩ.comp (z.1.appTop).hom = iΩ.comp (w.1.appTop).hom := congrArg AlgHom.toRingHom h
    have h2 : (z.1.appTop).hom = (w.1.appTop).hom := by
      have hinj : Function.Injective iΩ :=
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.injective
      ext a
      exact hinj (RingHom.congr_fun h1 a)
    have h3 : z.1.appTop = w.1.appTop := CommRingCat.hom_ext h2
    apply Subtype.ext
    rw [← cancel_mono H.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h3]
  haveI : Finite (Γ(H, ⊤) →ₐ[K] Ω) := inferInstance
  exact Finite.of_injective Φ hΦ

end FinitePoints

section KernelPoints

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

theorem one_coe (LY : RelativeGroupLaw R fY) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (LY.one t).1 = t ≫ (LY.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [← LY.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

theorem finite_kernelPoints (LY : RelativeGroupLaw R fY) (u : SchemeHomOver fX fY) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (hfin : Finite (SchemeHomOver t (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of R)))).1))) :
    {x : SchemeHomOver t fX | x ⊚ u = LY.one t}.Finite := by
  set e := (LY.one (𝟙 (Spec (CommRingCat.of R)))).1 with he
  have hcond : ∀ x : {x : SchemeHomOver t fX | x ⊚ u = LY.one t}, x.1.1 ≫ u.1 = t ≫ e := by
    intro x
    have h := congrArg Subtype.val x.2
    rw [one_coe] at h
    exact h
  let Φ : {x : SchemeHomOver t fX | x ⊚ u = LY.one t} → SchemeHomOver t (pullback.snd u.1 e) :=
    fun x => ⟨pullback.lift x.1.1 t (hcond x), pullback.lift_snd _ _ _⟩
  have hΦ : Function.Injective Φ := by
    intro x y h
    have h1 := congrArg (fun z : SchemeHomOver t (pullback.snd u.1 e) => z.1 ≫ pullback.fst u.1 e) h
    simp only [Φ, pullback.lift_fst] at h1
    exact Subtype.ext (Subtype.ext h1)
  haveI := hfin
  exact Finite.of_injective Φ hΦ

end KernelPoints

section Finite

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of K)} {fY : Y ⟶ Spec (CommRingCat.of K)}

theorem isFinite (LX : RelativeGroupLaw K fX) (hX : AbelianSchemePropertyBundle K fX)
    (LY : RelativeGroupLaw K fY) (hY : AbelianSchemePropertyBundle K fY) (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      (LX.mul t x y) ⊚ u = LY.mul t (x ⊚ u) (y ⊚ u))
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    IsFinite u.1 := by
  haveI : Smooth fX := hX.smooth
  haveI : IsProper fX := hX.proper
  haveI : IsProper fY := hY.proper
  haveI : LocallyOfFiniteType fX := inferInstance
  haveI := hker

  haveI : LocallyQuasiFinite u.1 := by
    refine LX.locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one LY u
      (fun t x y => hu t x y) ?_
    intro Ω _ _ t
    exact finite_kernelPoints LY u t (finite_schemeHomOver_of_isFinite _ Ω t)

  haveI : IsProper (u.1 ≫ fY) := by rw [u.2]; infer_instance
  haveI : IsProper u.1 := IsProper.of_comp u.1 fY
  exact IsFinite.of_isProper_of_locallyQuasiFinite u.1

end Finite

section RingTheory

private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_ringKrullDim_eq_natCast (k : Type u) (A : Type*) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  refine ⟨s, ?_⟩
  rw [← ringKrullDim_mvPolynomial_fin k s]
  exact (ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) hinj).symm

theorem height_comap_eq (k : Type u) [Field k] {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B] [Algebra.FiniteType k A]
    [Algebra.FiniteType k B] (φ : B →+* A) (hint : φ.IsIntegral) (hinj : Function.Injective φ)
    (P : Ideal A) [hP : P.IsPrime] : (P.comap φ).height = P.height := by
  letI : Algebra B A := φ.toAlgebra
  haveI : Algebra.IsIntegral B A := ⟨hint⟩
  have hφ : algebraMap B A = φ := rfl

  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast k A
  have hB : ringKrullDim B = n :=
    (ringKrullDim_eq_of_isIntegral_of_injective (R := B) (S := A) hinj).trans hn

  haveI : Nontrivial (A ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP.ne_top
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P)
  have hBq : ringKrullDim (B ⧸ P.comap φ) = m := by
    rw [← hφ]
    haveI : Algebra.IsIntegral (B ⧸ P.comap (algebraMap B A)) (A ⧸ P) :=
      Algebra.IsIntegral.quotient
    exact (ringKrullDim_eq_of_isIntegral_of_injective (R := B ⧸ P.comap (algebraMap B A))
      (S := A ⧸ P) Ideal.algebraMap_quotient_injective).trans hm

  have h1 := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k P
  have h2 := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k (P.comap φ)
  rw [hm, hn] at h1
  rw [hBq, hB] at h2
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at h1 h2
  have hm' : (m : ℕ∞) ≠ ⊤ := ENat.coe_ne_top m
  exact WithTop.add_right_cancel hm' (h2.trans h1.symm)

end RingTheory

section StalkDim

variable {K : Type u} [Field K]

theorem exists_algebra_finiteType {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType fX] (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ _ : Algebra K Γ(X, V), Algebra.FiniteType K Γ(X, V) := by
  let iK : K →+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hiK : Function.Surjective iK :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
  have hft : (fX.appLE ⊤ V le_top).hom.FiniteType :=
    fX.finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of K))) hV le_top
  refine ⟨((fX.appLE ⊤ V le_top).hom.comp iK).toAlgebra, ?_⟩
  have h : ((fX.appLE ⊤ V le_top).hom.comp iK).FiniteType :=
    hft.comp (RingHom.FiniteType.of_surjective iK hiK)
  exact h

theorem ringKrullDim_stalk_eq {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y) [IsFinite h] [Surjective h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (h.base x)) := by

  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := h.base x) (U := ⊤) trivial
  have hU : IsAffineOpen (h ⁻¹ᵁ V) := hV.preimage h
  have hxU : x ∈ h ⁻¹ᵁ V := hyV
  haveI : Nonempty (h ⁻¹ᵁ V) := ⟨⟨x, hxU⟩⟩
  haveI : Nonempty V := ⟨⟨h.base x, hyV⟩⟩

  set φ : Γ(Y, V) ⟶ Γ(X, h ⁻¹ᵁ V) := h.appLE V (h ⁻¹ᵁ V) le_rfl with hφ
  have hφapp : φ = h.app V := (Scheme.Hom.appLE_eq_app _).symm ▸ rfl
  have hint : φ.hom.IsIntegral := by
    rw [hφapp]
    exact (h.finite_app V hV).to_isIntegral
  have hinj : Function.Injective φ.hom := by
    rw [hφapp]
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : h ⁻¹ᵁ Y.basicOpen b = ⊥ := by
      rw [Scheme.preimage_basicOpen, hb, Scheme.basicOpen_zero]
    have h2 : Y.basicOpen b = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hy
      obtain ⟨x', rfl⟩ := h.surjective y
      have : x' ∈ (h ⁻¹ᵁ Y.basicOpen b) := hy
      rw [h1] at this
      exact this
    exact (basicOpen_eq_bot_iff b).mp h2

  set px := hU.primeIdealOf ⟨x, hxU⟩ with hpx
  set py := hV.primeIdealOf ⟨h.base x, hyV⟩ with hpy
  have hcomap : px.asIdeal.comap φ.hom = py.asIdeal := by
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := h) V hV (h ⁻¹ᵁ V) hU le_rfl hxU
    rw [← hpx] at h1
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2

  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : h ⁻¹ᵁ V)
  letI := Y.presheaf.algebra_section_stalk (⟨h.base x, hyV⟩ : V)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) px.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (h.base x)) py.asIdeal :=
    hV.isLocalization_stalk ⟨h.base x, hyV⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height px.asIdeal (X.presheaf.stalk x),
    IsLocalization.AtPrime.ringKrullDim_eq_height py.asIdeal (Y.presheaf.stalk (h.base x))]

  obtain ⟨algA, hftA⟩ := exists_algebra_finiteType fX (h ⁻¹ᵁ V) hU
  obtain ⟨algB, hftB⟩ := exists_algebra_finiteType fY V hV
  letI := algA
  letI := algB
  have key := height_comap_eq K φ.hom hint hinj px.asIdeal
  rw [hcomap] at key
  rw [key]

end StalkDim

section Flatness

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of K)} {fY : Y ⟶ Spec (CommRingCat.of K)}

theorem flat_stalkMap (hX : AbelianSchemePropertyBundle K fX) (hY : AbelianSchemePropertyBundle K fY)
    (u : SchemeHomOver fX fY) [IsFinite u.1] [Surjective u.1] (x : X) : (u.1.stalkMap x).hom.Flat := by
  haveI : Smooth fX := hX.smooth
  haveI : Smooth fY := hY.smooth
  haveI : IsIntegral X := AbelianSchemePropertyBundle.isIntegral_of_field hX
  haveI : IsIntegral Y := AbelianSchemePropertyBundle.isIntegral_of_field hY
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY

  haveI hx : IsRegularLocalRing (X.presheaf.stalk x) := Smooth.isRegularLocalRing_stalk (f := fX) x
  haveI hy : IsRegularLocalRing (Y.presheaf.stalk (u.1.base x)) :=
    Smooth.isRegularLocalRing_stalk (f := fY) (u.1.base x)

  letI alg : Algebra (Y.presheaf.stalk (u.1.base x)) (X.presheaf.stalk x) :=
    (u.1.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (u.1.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (u.1.stalkMap x).hom)

  have hfib : ringKrullDim ((X.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (u.1.base x))).map
        (algebraMap (Y.presheaf.stalk (u.1.base x)) (X.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero u.1 x

  have hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (u.1.base x)) :=
    ringKrullDim_stalk_eq fX fY u.1 x

  have hflat : Module.Flat (Y.presheaf.stalk (u.1.base x)) (X.presheaf.stalk x) :=
    Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      (Y.presheaf.stalk (u.1.base x)) (X.presheaf.stalk x) hfib hdim
  exact hflat

theorem main (LX : RelativeGroupLaw K fX) (hX : AbelianSchemePropertyBundle K fX)
    (LY : RelativeGroupLaw K fY) (hY : AbelianSchemePropertyBundle K fY) (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      (LX.mul t x y) ⊚ u = LY.mul t (x ⊚ u) (y ⊚ u))
    (hsurj : Surjective u.1)
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    IsFinite u.1 ∧ Flat u.1 := by
  haveI : IsFinite u.1 := isFinite LX hX LY hY u (fun t x y => hu t x y) hker
  haveI := hsurj
  exact ⟨inferInstance, Flat.of_stalkMap u.1 (flat_stalkMap hX hY u)⟩

end Flatness

end P2mFlatIsog

theorem solution
    {K : Type u} [Field K]
    {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (LX : RelativeGroupLaw K fX)
    (hcX : LX.IsCommutative) (hX : AbelianSchemePropertyBundle K fX)
    {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of K)} (LY : RelativeGroupLaw K fY)
    (hcY : LY.IsCommutative) (hY : AbelianSchemePropertyBundle K fY)
    (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) u =
        LY.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (hsurj : Surjective u.1)
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    IsFinite u.1 ∧ Flat u.1 := by

  have _hc : LX.IsCommutative ∧ LY.IsCommutative := ⟨hcX, hcY⟩
  exact P2mFlatIsog.main LX hX LY hY u (fun t x y => hu t x y) hsurj hker

end

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd (solution)
