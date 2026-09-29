-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bdb0d27a-b3ca-5fb1-a4c8-5fc2e3e73013

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mFrobSep

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem formallyUnramified_of_forall_derivation_eq_zero [Algebra.EssFiniteType R S]
    (H : ∀ (m : Ideal S) (_ : m.IsMaximal) (δ : Derivation R S (S ⧸ m)), δ = 0) :
    Algebra.FormallyUnramified R S := by
  refine ⟨?_⟩
  rw [← Module.support_eq_empty_iff (R := S), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_of_finite] at hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top

  have hlin : ∀ ℓ : Ω[S⁄R] →ₗ[S] (S ⧸ m), ℓ = 0 := fun ℓ => by
    have h := H m hm ((KaehlerDifferential.linearMapEquivDerivation R S) ℓ)
    exact (LinearEquiv.map_eq_zero_iff _).mp h

  have key : (m • ⊤ : Submodule S Ω[S⁄R]) = ⊤ := by
    letI : Field (S ⧸ m) := Ideal.Quotient.field m
    rw [← Submodule.Quotient.subsingleton_iff]
    refine ⟨fun a b => ?_⟩
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (S ⧸ m)]
    intro φ
    obtain ⟨ω, hω⟩ := Submodule.mkQ_surjective (m • ⊤ : Submodule S Ω[S⁄R]) (a - b)
    have := hlin ((φ.restrictScalars S).comp (Submodule.mkQ (m • ⊤ : Submodule S Ω[S⁄R])))
    rw [← hω]
    exact LinearMap.congr_fun this ω
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (⊤ : Submodule S Ω[S⁄R]) Module.Finite.fg_top (by rw [key])
  have hrann : r ∈ Module.annihilator S Ω[S⁄R] :=
    Module.mem_annihilator.mpr fun n => hr n Submodule.mem_top
  have hrm : r ∈ m := hpm (hp hrann)
  have h1 : (1 : S) ∈ m := by simpa using m.sub_mem hrm hr1
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h1)

end Algebra

section Dual

variable (K : Type u) [Field K]

def π₀ : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom

def ι₀ : K →+* DualNumber K := algebraMap K (DualNumber K)

def g₀ : DualNumber K →+* DualNumber K := (ι₀ K).comp (π₀ K)

@[scoped simp] theorem π₀_apply (z : DualNumber K) : π₀ K z = z.fst := rfl

@[scoped simp] theorem ι₀_apply (c : K) : ι₀ K c = TrivSqZeroExt.inl c := rfl

theorem g₀_apply (z : DualNumber K) : g₀ K z = TrivSqZeroExt.inl z.fst := rfl

theorem g₀_eq_self_iff (z : DualNumber K) : g₀ K z = z ↔ z.snd = 0 := by
  rw [g₀_apply]
  constructor
  · intro h; rw [← h]; rfl
  · intro h; ext <;> simp [h]

theorem π₀_comp_ι₀ : (π₀ K).comp (ι₀ K) = RingHom.id K := by
  ext c; simp

theorem π₀_surjective : Function.Surjective (π₀ K) := fun c => ⟨ι₀ K c, by simp⟩

abbrev SK : Scheme.{u} := Spec (CommRingCat.of K)

abbrev SKε : Scheme.{u} := Spec (CommRingCat.of (DualNumber K))

def pε : SKε K ⟶ SK K := Spec.map (CommRingCat.ofHom (ι₀ K))

def iε : SK K ⟶ SKε K := Spec.map (CommRingCat.ofHom (π₀ K))

def ρ : SKε K ⟶ SKε K := Spec.map (CommRingCat.ofHom (g₀ K))

theorem ρ_eq : ρ K = pε K ≫ iε K := by
  rw [ρ, pε, iε, ← Spec.map_comp]; rfl

theorem iε_comp_pε : iε K ≫ pε K = 𝟙 _ := by
  rw [iε, pε, ← Spec.map_comp, ← CommRingCat.ofHom_comp, π₀_comp_ι₀]
  exact Spec.map_id _

theorem iε_comp_ρ : iε K ≫ ρ K = iε K := by
  rw [ρ_eq, ← Category.assoc, iε_comp_pε, Category.id_comp]

theorem ρ_comp_pε : ρ K ≫ pε K = pε K := by
  rw [ρ_eq, Category.assoc, iε_comp_pε, Category.comp_id]

scoped instance : IsClosedImmersion (iε K) :=
  IsClosedImmersion.spec_of_surjective _ (π₀_surjective K)

theorem isNilpotent_ker_specMap {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (h2 : ∀ a ∈ RingHom.ker φ.hom, ∀ b ∈ RingHom.ker φ.hom, a * b = 0) :
    IsNilpotent (Spec.map φ).ker := by
  refine ⟨2, ?_⟩
  change (Spec.map φ).ker ^ 2 = ⊥
  refine le_bot_iff.mp (Scheme.IdealSheafData.le_of_isAffine ?_)
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, pow_two, Ideal.mul_le]
  intro a ha b hb
  change (Spec.map φ).appTop a = 0 at ha
  change (Spec.map φ).appTop b = 0 at hb
  have hnat := Scheme.ΓSpecIso_naturality φ
  have ha' : (Scheme.ΓSpecIso R').hom a ∈ RingHom.ker φ.hom := by
    change φ ((Scheme.ΓSpecIso R').hom a) = 0
    rw [← CategoryTheory.comp_apply, ← hnat, CategoryTheory.comp_apply, ha, map_zero]
  have hb' : (Scheme.ΓSpecIso R').hom b ∈ RingHom.ker φ.hom := by
    change φ ((Scheme.ΓSpecIso R').hom b) = 0
    rw [← CategoryTheory.comp_apply, ← hnat, CategoryTheory.comp_apply, hb, map_zero]
  have hab := h2 _ ha' _ hb'
  rw [← map_mul] at hab
  have hinj : Function.Injective (Scheme.ΓSpecIso R').hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').hom).1
  change a * b ∈ (⊥ : Ideal _)
  rw [Ideal.mem_bot]
  exact hinj (by rw [hab, map_zero])

theorem isNilpotent_ker_iε : IsNilpotent (iε K).ker := by
  refine isNilpotent_ker_specMap _ fun a ha b hb => ?_
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  ext
  · simp [ha', hb']
  · rw [DualNumber.snd_mul, ha', hb']; simp

theorem not_isUnit_iff_fst_eq_zero (z : DualNumber K) : ¬ IsUnit z ↔ z.fst = 0 := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not]

end Dual

section Tangent

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

def κ (y : A) (c : K) : A.presheaf.stalk y :=
  A.presheaf.germ ⊤ y trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))

theorem stalkMap_κ (π : SchemeHomOver f f) (x : A) (c : K) :
    π.1.stalkMap x (κ f (π.1.base x) c) = κ f x c := by
  unfold κ
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h : f.appTop ≫ π.1.appTop = f.appTop := by rw [← Scheme.Hom.comp_appTop, π.2]
  have h' : π.1.app ⊤ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c) := by
    change (f.appTop ≫ π.1.appTop) _ = _
    rw [h]
  rw [h']
  rfl

theorem stalkClosedPointTo_κ (w : SKε K ⟶ A) (hw : w ≫ f = pε K) (c : K) :
    Scheme.stalkClosedPointTo w (κ f (w.base (IsLocalRing.closedPoint (DualNumber K))) c) = ι₀ K c := by
  have T : ∀ (u : SKε K ⟶ SK K) (_ : u = Spec.map (CommRingCat.ofHom (ι₀ K))),
      (SK K).presheaf.germ ⊤ (u.base (IsLocalRing.closedPoint _)) trivial ≫ Scheme.stalkClosedPointTo u =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom (ι₀ K) := by
    rintro _ rfl
    exact Scheme.germ_stalkClosedPointTo_Spec _
  have T' := T (w ≫ f) (by rw [hw]; rfl)
  rw [Scheme.stalkClosedPointTo_comp] at T'
  erw [Scheme.Hom.germ_stalkMap_assoc] at T'
  have T'' := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) T'
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at T''
  rw [Iso.inv_hom_id_apply] at T''
  exact T''

theorem stalk_ktv (π : SchemeHomOver f f)
    (hdπ : ∀ x : A, (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (w : SKε K ⟶ A) (hw : w ≫ f = pε K) :
    π.1.stalkMap (w.base (IsLocalRing.closedPoint (DualNumber K))) ≫ Scheme.stalkClosedPointTo w =
      (π.1.stalkMap (w.base (IsLocalRing.closedPoint (DualNumber K))) ≫ Scheme.stalkClosedPointTo w) ≫
        CommRingCat.ofHom (g₀ K) := by
  set x := w.base (IsLocalRing.closedPoint (DualNumber K)) with hx
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]

  set φ : A.presheaf.stalk (π.1.base x) →+* DualNumber K :=
    (Scheme.stalkClosedPointTo w).hom.comp (π.1.stalkMap x).hom with hφdef
  have hφ : ∀ t, φ t = Scheme.stalkClosedPointTo w (π.1.stalkMap x t) := fun t => rfl

  have hφκ : ∀ c : K, φ (κ f (π.1.base x) c) = ι₀ K c := fun c => by
    rw [hφ, stalkMap_κ]
    exact stalkClosedPointTo_κ f w hw c

  have hθsq : ∀ a ∈ IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2,
      Scheme.stalkClosedPointTo w a = 0 := by
    intro a ha
    rw [pow_two] at ha
    have hfst : ∀ b ∈ IsLocalRing.maximalIdeal (A.presheaf.stalk x),
        (Scheme.stalkClosedPointTo w b).fst = 0 := by
      intro b hb
      rw [← not_isUnit_iff_fst_eq_zero]
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal _).mp hb)
        ((isUnit_map_iff (Scheme.stalkClosedPointTo w).hom b).mp hu)
    refine Submodule.mul_induction_on ha (fun b hb d hd => ?_)
      (fun b d hb hd => by rw [map_add, hb, hd, add_zero])
    rw [map_mul]
    ext
    · rw [TrivSqZeroExt.fst_mul, hfst b hb, zero_mul, TrivSqZeroExt.fst_zero]
    · rw [DualNumber.snd_mul, hfst b hb, hfst d hd, zero_mul, mul_zero, add_zero,
        TrivSqZeroExt.snd_zero]

  set c := (φ s).fst with hc
  have hs₀ : s - κ f (π.1.base x) c ∈ IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (φ (s - κ f (π.1.base x) c)) := hu.map φ
    rw [map_sub, hφκ] at hu'
    revert hu'
    rw [imp_false, not_isUnit_iff_fst_eq_zero, TrivSqZeroExt.fst_sub, ι₀_apply, TrivSqZeroExt.fst_inl,
      sub_self]
  have h1 : π.1.stalkMap x (s - κ f (π.1.base x) c) ∈ IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2 :=
    hdπ x (Ideal.mem_map_of_mem _ hs₀)
  have h2 : φ s = ι₀ K c := by
    have := hθsq _ h1
    rw [← hφ, map_sub, hφκ, sub_eq_zero] at this
    exact this
  change φ s = g₀ K (φ s)
  rw [h2, g₀_apply, ι₀_apply, TrivSqZeroExt.fst_inl]

theorem comp_ktv (π : SchemeHomOver f f)
    (hdπ : ∀ x : A, (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (w : SKε K ⟶ A) (hw : w ≫ f = pε K) :
    ρ K ≫ w ≫ π.1 = w ≫ π.1 := by
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (w ≫ π.1)
  rw [Scheme.stalkClosedPointTo_comp] at e
  calc ρ K ≫ w ≫ π.1
      = ρ K ≫ Spec.map (π.1.stalkMap _ ≫ Scheme.stalkClosedPointTo w) ≫ A.fromSpecStalk _ := by erw [e]
    _ = Spec.map ((π.1.stalkMap _ ≫ Scheme.stalkClosedPointTo w) ≫ CommRingCat.ofHom (g₀ K)) ≫
          A.fromSpecStalk _ := by
        rw [Spec.map_comp _ (CommRingCat.ofHom (g₀ K)), Category.assoc]; rfl
    _ = Spec.map (π.1.stalkMap _ ≫ Scheme.stalkClosedPointTo w) ≫ A.fromSpecStalk _ := by
        rw [← stalk_ktv f π hdπ w hw]
    _ = w ≫ π.1 := e

end Tangent

section Group

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

def fixSub {M : Type*} [Group M] (F : M →* M) : Subgroup M where
  carrier := {u | F u = u}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one F
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

def pullHom (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') :
    letI := L.pointCommGroup hc t
    letI := L.pointCommGroup hc t'
    SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := L.pointCommGroup hc t
  letI := L.pointCommGroup hc t'
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := L.one_natural t t' ψ hψ
    map_mul' := L.mul_natural t t' ψ hψ }

theorem pullHom_apply_coe (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (φ : SchemeHomOver t f) :
    (pullHom L hc ψ hψ φ).1 = ψ ≫ φ.1 := rfl

theorem pow_eq_nsmul (L : RelativeGroupLaw K f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (n : ℕ) :
    (letI := L.pointCommGroup hc t; x ^ n) = L.nsmul t n x := by
  letI := L.pointCommGroup hc t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih]; rfl

theorem ρ_comp_eq_of_endAeval (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (π : SchemeHomOver f f)
    (hπ : ∀ w : SchemeHomOver (pε K) f, ρ K ≫ w.1 ≫ π.1 = w.1 ≫ π.1)
    (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) (v : SchemeHomOver (pε K) f)
    (hv : ρ K ≫ v.1 ≫ (L.endAeval hc π G).1 = v.1 ≫ (L.endAeval hc π G).1) :
    ρ K ≫ v.1 = v.1 := by
  letI instE : CommGroup (SchemeHomOver f f) := L.pointCommGroup hc f
  letI instP : CommGroup (SchemeHomOver (pε K) f) := L.pointCommGroup hc (pε K)
  let ev : SchemeHomOver f f →* SchemeHomOver (pε K) f := pullHom L hc v.1 v.2
  let Fρ : SchemeHomOver (pε K) f →* SchemeHomOver (pε K) f := pullHom L hc (ρ K) (ρ_comp_pε K)
  let H : Subgroup (SchemeHomOver (pε K) f) := fixSub Fρ
  have memH : ∀ u : SchemeHomOver (pε K) f, u ∈ H ↔ ρ K ≫ u.1 = u.1 := fun u => by
    change Fρ u = u ↔ _
    rw [Subtype.ext_iff]
    rfl
  have hev1 : ∀ φ, (ev φ).1 = v.1 ≫ φ.1 := fun _ => rfl

  have hpow : ∀ i, ev (schemeHomOverNpow π (i + 1)) ∈ H := fun i => by
    rw [memH, hev1]
    have := hπ (ev (schemeHomOverNpow π i))
    rw [hev1, Category.assoc] at this
    simpa only [NeronModelInfra.schemeHomOverNpow_succ, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc] using this
  have hβ : ev (L.endAeval hc π G) ∈ H := by rw [memH, hev1]; exact hv

  have hev0 : ev (schemeHomOverNpow π 0) = v := by
    apply Subtype.ext
    rw [hev1, NeronModelInfra.schemeHomOverNpow_zero, NeronModelInfra.schemeHomOverId_coe,
      Category.comp_id]
  have hdec : ev (L.endAeval hc π G) =
      (∏ i ∈ Finset.range G.natDegree, ev (schemeHomOverNpow π (i + 1)) ^ G.coeff (i + 1)) *
        v ^ G.coeff 0 := by
    rw [RelativeGroupLaw.endAeval, map_prod, Finset.prod_range_succ']
    simp only [map_zpow, hev0]
  have h1 : (∏ i ∈ Finset.range G.natDegree, ev (schemeHomOverNpow π (i + 1)) ^ G.coeff (i + 1)) ∈ H :=
    prod_mem fun i _ => H.zpow_mem (hpow i) _
  have h2 : v ^ G.coeff 0 ∈ H := by
    have := hβ
    rw [hdec] at this
    exact (Subgroup.mul_mem_cancel_left H h1).mp this

  set n : ℕ := (G.coeff 0).natAbs with hn'
  have h3 : v ^ n ∈ H := by
    have e : v ^ n = (v ^ G.coeff 0) ^ (G.coeff 0).sign := by
      rw [← zpow_natCast, ← zpow_mul, ← Int.sign_mul_self_eq_natAbs, mul_comm]
    rw [e]
    exact H.zpow_mem h2 _
  have hn : IsUnit (n : K) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hG
    have : (G.coeff 0 : ℤ) = (G.coeff 0).sign * (n : ℤ) := (Int.sign_mul_natAbs _).symm
    rw [this]
    push_cast
    rw [h0, mul_zero]

  have hvn : (v ^ n).1 = v.1 ≫ L.schemeNsmul n := by
    have : v ^ n = ev (schemeHomOverNpow π 0 ^ n) := by rw [map_pow, hev0]
    rw [this, hev1, pow_eq_nsmul]
    rfl
  have h4 : ρ K ≫ v.1 ≫ L.schemeNsmul n = v.1 ≫ L.schemeNsmul n := by
    have := (memH _).mp h3
    rwa [hvn] at this

  haveI : FormallyUnramified (L.schemeNsmul n) :=
    RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing L
      (fun t x y => hc t x y) n hn
  exact FormallyUnramified.hom_ext (iε K) (isNilpotent_ker_iε K) (L.schemeNsmul n)
    (g₁ := ρ K ≫ v.1) (g₂ := v.1) (by rw [← Category.assoc, iε_comp_ρ])
    (by simpa only [Category.assoc] using h4)

end Group

section Assembly

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem appLE_congrHom {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V e' := by
  subst h; rfl

def ιop (V : A.Opens) : CommRingCat.of K ⟶ Γ(A, V) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    f.appLE ⊤ V ((le_top : V ≤ ⊤).trans (TopologicalSpace.Opens.map_top f.base).ge)

theorem fromSpec_comp_eq (V : A.Opens) (hV : IsAffineOpen V) :
    hV.fromSpec ≫ f = Spec.map (ιop f V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV
    ((le_top : V ≤ ⊤).trans (TopologicalSpace.Opens.map_top f.base).ge)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

theorem ιop_finiteType [LocallyOfFiniteType f] (V : A.Opens) (hV : IsAffineOpen V) :
    (ιop f V).hom.FiniteType := by
  have h := f.finiteType_appLE (isAffineOpen_top _) hV
    ((le_top : V ≤ ⊤).trans (TopologicalSpace.Opens.map_top f.base).ge)
  rw [ιop, CommRingCat.hom_comp]
  exact h.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)

theorem ιop_comp_appLE (β : SchemeHomOver f f) (U V : A.Opens) (hVU : V ≤ β.1 ⁻¹ᵁ U) :
    ιop f U ≫ β.1.appLE U V hVU = ιop f V := by
  rw [ιop, ιop, Category.assoc, Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact appLE_congrHom β.2 _ _ _ _

theorem formallyUnramified_endAeval [IsAlgClosed K] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (π : SchemeHomOver f f)
    (hdπ : ∀ x : A, (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    FormallyUnramified (L.endAeval hc π G).1 := by
  set β := L.endAeval hc π G with hβdef
  haveI : LocallyOfFiniteType β.1 := by
    have : LocallyOfFiniteType (β.1 ≫ f) := by rw [β.2]; infer_instance
    exact locallyOfFiniteType_of_comp β.1 f
  refine ⟨fun {U} hU {V} hV hVU ↦ ?_⟩
  letI algUV := (β.1.appLE U V hVU).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(A, U) Γ(A, V) := β.1.finiteType_appLE hU hV hVU
  change Algebra.FormallyUnramified Γ(A, U) Γ(A, V)
  refine formallyUnramified_of_forall_derivation_eq_zero (fun m hm δ => ?_)

  letI algKV : Algebra K Γ(A, V) := (ιop f V).hom.toAlgebra
  haveI : Algebra.FiniteType K Γ(A, V) := ιop_finiteType f V hV
  haveI := hm
  letI : Field (Γ(A, V) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (Γ(A, V) ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := Γ(A, V) ⧸ m)
  let e : K ≃+* Γ(A, V) ⧸ m := RingEquiv.ofBijective _ hbij
  have he : ∀ c : K, e c = algebraMap K (Γ(A, V) ⧸ m) c := fun _ => rfl
  let χ : Γ(A, V) →+* K := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have hχ : ∀ s, χ s = e.symm (Ideal.Quotient.mk m s) := fun _ => rfl
  have hχK : ∀ c : K, χ (algebraMap K Γ(A, V) c) = c := fun c => by
    rw [hχ, Ideal.Quotient.mk_algebraMap, ← he, RingEquiv.symm_apply_apply]

  have hKU : ∀ c : K, algebraMap Γ(A, U) Γ(A, V) ((ιop f U).hom c) = algebraMap K Γ(A, V) c :=
    fun c => by
    change (ιop f U ≫ β.1.appLE U V hVU).hom c = (ιop f V).hom c
    rw [ιop_comp_appLE]
  have hδK : ∀ c : K, δ (algebraMap K Γ(A, V) c) = 0 := fun c => by
    rw [← hKU]; exact δ.map_algebraMap _

  let δK : Γ(A, V) → K := fun s => e.symm (δ s)
  have hδK_def : ∀ s, δK s = e.symm (δ s) := fun _ => rfl
  have hδK_add : ∀ a b, δK (a + b) = δK a + δK b := fun a b => by
    rw [hδK_def, map_add, map_add]
  have hδK_mul : ∀ a b, δK (a * b) = χ a * δK b + δK a * χ b := fun a b => by
    rw [hδK_def, hδK_def, hδK_def, hχ, hχ, Derivation.leibniz, map_add, Algebra.smul_def,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul, map_mul, mul_comm (e.symm (δ a))]
  have hδK_one : δK 1 = 0 := by rw [hδK_def, Derivation.map_one_eq_zero, map_zero]
  let η : Γ(A, V) →+* DualNumber K :=
    { toFun := fun s => TrivSqZeroExt.inl (χ s) + TrivSqZeroExt.inr (δK s)
      map_one' := by
        ext
        · simp
        · simp [hδK_one]
      map_mul' := fun a b => by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
            DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
            add_zero, hδK_mul]
      map_zero' := by
        ext
        · simp
        · simp [hδK_def]
      map_add' := fun a b => by
        ext
        · simp
        · simp [hδK_add] }
  have hηapp : ∀ s, η s = TrivSqZeroExt.inl (χ s) + TrivSqZeroExt.inr (δK s) := fun _ => rfl
  have hηsnd : ∀ s, (η s).snd = δK s := fun s => by rw [hηapp]; simp
  have hηK : ∀ c : K, η (algebraMap K Γ(A, V) c) = ι₀ K c := fun c => by
    rw [hηapp, ι₀_apply]
    ext
    · simp [hχK]
    · simp [hδK_def, hδK]
  have hηU : ∀ r : Γ(A, U), (η (algebraMap Γ(A, U) Γ(A, V) r)).snd = 0 := fun r => by
    rw [hηsnd, hδK_def, δ.map_algebraMap, map_zero]

  let v₁ : SKε K ⟶ A := Spec.map (CommRingCat.ofHom η) ≫ hV.fromSpec
  have hv₁ : v₁ ≫ f = pε K := by
    change (Spec.map (CommRingCat.ofHom η) ≫ hV.fromSpec) ≫ f = Spec.map (CommRingCat.ofHom (ι₀ K))
    rw [Category.assoc, fromSpec_comp_eq f V hV, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact hηK c
  let v : SchemeHomOver (pε K) f := ⟨v₁, hv₁⟩

  have hvβ : ρ K ≫ v.1 ≫ β.1 = v.1 ≫ β.1 := by
    have eβ : v.1 ≫ β.1 = Spec.map (β.1.appLE U V hVU ≫ CommRingCat.ofHom η) ≫ hU.fromSpec := by
      rw [Spec.map_comp]
      simp only [Category.assoc]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec β.1 hU hV hVU]
      exact Category.assoc _ _ _
    rw [eβ, ρ, ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change g₀ K (η ((β.1.appLE U V hVU).hom r)) = η ((β.1.appLE U V hVU).hom r)
    rw [g₀_eq_self_iff]
    exact hηU r

  have main : ρ K ≫ v.1 = v.1 :=
    ρ_comp_eq_of_endAeval L hc π (fun w => comp_ktv f π hdπ w.1 w.2) G hG v hvβ

  have hη : CommRingCat.ofHom η ≫ CommRingCat.ofHom (g₀ K) = CommRingCat.ofHom η := by
    have h : Spec.map (CommRingCat.ofHom η ≫ CommRingCat.ofHom (g₀ K)) ≫ hV.fromSpec =
        Spec.map (CommRingCat.ofHom η) ≫ hV.fromSpec := by
      rw [Spec.map_comp, Category.assoc]
      exact main
    rw [cancel_mono] at h
    exact Spec.map_injective h
  refine Derivation.ext fun s => ?_
  have hs := congrArg (fun φ : CommRingCat.of Γ(A, V) ⟶ CommRingCat.of (DualNumber K) => (φ.hom s).snd) hη
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hs
  rw [g₀_apply, TrivSqZeroExt.snd_inl, hηsnd, hδK_def] at hs
  rw [Derivation.zero_apply]
  have := congrArg e hs
  rwa [map_zero, RingEquiv.apply_symm_apply, eq_comm] at this

end Assembly

end P2mFrobSep
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq.P2mFrobSep"

open P2mFrobSep in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (π : SchemeHomOver f f)
    (hdπ : ∀ x : A, (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (G : Polynomial ℤ) (hG : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    Etale (L.endKerStr (L.endAeval hc π G)) := by
  haveI := hA.smooth
  set β := L.endAeval hc π G with hβdef
  haveI hβlft : LocallyOfFiniteType β.1 := by
    have : LocallyOfFiniteType (β.1 ≫ f) := by rw [β.2]; infer_instance
    exact locallyOfFiniteType_of_comp β.1 f
  haveI hβfu : FormallyUnramified β.1 := formallyUnramified_endAeval f L hc π hdπ G hG
  haveI : FormallyUnramified (L.endKerStr β) :=
    MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ hβfu
  haveI : LocallyOfFiniteType (L.endKerStr β) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ hβlft
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := inferInstance
  haveI : LocallyOfFinitePresentation (L.endKerStr β) := inferInstance
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Flat (L.endKerStr β) := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

end
end S_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq (solution)
