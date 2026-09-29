-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7eeb621b-5d3f-5323-bc15-649c9df800d6

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.GoodReductionJacobian"
open scoped TensorProduct

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul pointGroup one_natural mul_one one mul_natural mk inv one_mul mul formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id x.1)

theorem nsmul_coe_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [schemeHomOverComp_idPoint] at h
  exact (congrArg Subtype.val h).symm

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.one_coe_eq_comp_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h : schemeHomOverComp t (Category.comp_id t) (G.one (𝟙 _)) = G.one t :=
    G.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one_coe_eq_comp_one"
theorem kw_rglnfu_pow_eq_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (letI := G.pointGroup t; x ^ n) = G.nsmul t n x := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, G.nsmul_succ]; rfl

abbrev KwCommRelGroupLawSqZeroKerNTorsionFree (G : RelativeGroupLaw R f) : Prop :=
  ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
    RingHom.ker φ.hom ^ 2 = ⊥ →
    ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f),
      schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) →
      ∀ n : ℕ, 0 < n → G.nsmul t n k = G.one t → k = G.one t

abbrev KwCommRelGroupLawSqZeroKerNTorsionFreeAt (G : RelativeGroupLaw R f) (n : ℕ) : Prop :=
  ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
    RingHom.ker φ.hom ^ 2 = ⊥ →
    ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f),
      schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) →
      G.nsmul t n k = G.one t → k = G.one t

end RelativeGroupLaw
end GoodReductionJacobian

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian"

namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul pointGroup one_natural mul_one one mul_natural mk inv one_mul mul formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem kw_rglcktf_axiomAnchor : True := by
  have _ := Classical.em True
  have _ := @Quot.sound ℕ (· = ·) 0 0 rfl
  have _ := @propext True True Iff.rfl
  trivial

private def _root_.GoodReductionJacobian.RelativeGroupLaw.kwUnitSection (G : RelativeGroupLaw R f) : Spec (CommRingCat.of R) ⟶ A :=
  (G.one (𝟙 (Spec (CommRingCat.of R)))).1

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "kwUnitSection"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.kwUnitSection_comp (G : RelativeGroupLaw R f) :
    G.kwUnitSection ≫ f = 𝟙 (Spec (CommRingCat.of R)) :=
  (G.one (𝟙 (Spec (CommRingCat.of R)))).2

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "kwUnitSection_comp"

theorem kw_rglcktf_specMap_base_surjective {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    Function.Surjective (Spec.map φ).base := by
  intro p
  have hkerp : RingHom.ker φ.hom ≤ p.asIdeal := fun x hx =>
    p.isPrime.mem_of_pow_mem 2 (by
      have h2 : x ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow hx 2
      rw [hker, Ideal.mem_bot] at h2
      exact h2 ▸ p.asIdeal.zero_mem)
  refine ⟨⟨p.asIdeal.map φ.hom, Ideal.map_isPrime_of_surjective hsurj hkerp⟩,
    PrimeSpectrum.ext ?_⟩
  show Ideal.comap φ.hom (Ideal.map φ.hom p.asIdeal) = p.asIdeal
  exact (Ideal.comap_map_of_surjective φ.hom hsurj p.asIdeal).trans (sup_eq_left.mpr hkerp)

theorem kw_rglcktf_range_subset_of_sqZeroKerElem (G : RelativeGroupLaw R f)
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hkred : schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t)) :
    Set.range k.1.base ⊆ Set.range G.kwUnitSection.base := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, rfl⟩ := kw_rglcktf_specMap_base_surjective φ hsurj hker p
  have hcoe : (Spec.map φ ≫ k.1).base q = ((Spec.map φ ≫ t) ≫ G.kwUnitSection).base q := by
    have h1 : Spec.map φ ≫ k.1 = (G.one (Spec.map φ ≫ t)).1 :=
      (schemeHomOverComp_coe (Spec.map φ) rfl k).symm.trans (congrArg Subtype.val hkred)
    rw [h1, G.one_coe_eq_comp_one]; rfl
  refine ⟨(Spec.map φ ≫ t).base q, ?_⟩
  exact hcoe.symm.trans rfl

section RingTheory

variable {B R' S' : Type*} [CommRing B] [CommRing R'] [CommRing S']
variable [Algebra R B] [Algebra R R']
variable (ε₀ : B →ₐ[R] R) (φ : R' →+* S')

def kwTrivLift : B →ₐ[R] R' := (Algebra.ofId R R').comp (ε₀.restrictScalars R)

theorem kw_rglcktf_trivLift_apply (x : B) :
    kwTrivLift ε₀ x = algebraMap R R' (ε₀ x) := by
  have _ := kw_rglcktf_axiomAnchor
  rfl

theorem kw_rglcktf_mem_kerφ_of_mem_augIdeal (kR : B →ₐ[R] R')
    (hk : ∀ x, φ (kR x) = φ (kwTrivLift ε₀ x))
    {a : B} (ha : a ∈ RingHom.ker ε₀) : kR a ∈ RingHom.ker φ := by
  have _ := kw_rglcktf_axiomAnchor
  rw [RingHom.mem_ker, hk a, kw_rglcktf_trivLift_apply]
  rw [RingHom.mem_ker] at ha
  rw [ha, map_zero, map_zero]

theorem kw_rglcktf_eq_zero_of_mem_sq (hkerφ : RingHom.ker φ ^ 2 = ⊥)
    (kR : B →ₐ[R] R') (hk : ∀ x, φ (kR x) = φ (kwTrivLift ε₀ x))
    {a : B} (ha : a ∈ (RingHom.ker ε₀) ^ 2) : kR a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have : kR x * kR y ∈ RingHom.ker φ ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (kw_rglcktf_mem_kerφ_of_mem_augIdeal ε₀ φ kR hk hx)
        (kw_rglcktf_mem_kerφ_of_mem_augIdeal ε₀ φ kR hk hy)
    rw [hkerφ, Ideal.mem_bot] at this
    rwa [map_mul]
  · rw [map_add, hx, hy, add_zero]

theorem kw_rglcktf_sub_algebraMap_mem_augIdeal (x : B) :
    x - algebraMap R B (ε₀ x) ∈ RingHom.ker ε₀ := by
  have _ := kw_rglcktf_axiomAnchor
  simp [RingHom.mem_ker, map_sub, AlgHom.commutes]

theorem kw_rglcktf_eq_trivLift_of_forall_augIdeal_eq_zero (kR : B →ₐ[R] R')
    (h0 : ∀ a ∈ RingHom.ker ε₀, kR a = 0) : kR = kwTrivLift ε₀ := by
  have _ := kw_rglcktf_axiomAnchor
  ext x
  have key : kR (x - algebraMap R B (ε₀ x)) = 0 :=
    h0 _ (kw_rglcktf_sub_algebraMap_mem_augIdeal ε₀ x)
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at key
  rw [key, kw_rglcktf_trivLift_apply]

end RingTheory

open CategoryTheory.Limits

abbrev kwPairingMap : Limits.pullback f f ⟶ Spec (CommRingCat.of R) :=
  Limits.pullback.fst f f ≫ f

abbrev kwPrFst : SchemeHomOver (kwPairingMap (f := f)) f :=
  ⟨Limits.pullback.fst f f, rfl⟩

abbrev kwPrSnd : SchemeHomOver (kwPairingMap (f := f)) f :=
  ⟨Limits.pullback.snd f f, Limits.pullback.condition.symm⟩

private def _root_.GoodReductionJacobian.RelativeGroupLaw.kwSchemeMul (G : RelativeGroupLaw R f) : Limits.pullback f f ⟶ A :=
  (G.mul kwPairingMap kwPrFst kwPrSnd).1

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "kwSchemeMul"

theorem kwSchemeMul_over (G : RelativeGroupLaw R f) :
    G.kwSchemeMul ≫ f = kwPairingMap (f := f) :=
  (G.mul kwPairingMap kwPrFst kwPrSnd).2

theorem kw_rglcktf_mul_coe_eq_lift_comp_schemeMul (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver t f) :
    (G.mul t x y).1 = Limits.pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ G.kwSchemeMul := by
  let ψ := Limits.pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ kwPairingMap (f := f) = t := by
    simp only [kwPairingMap, ψ, ← Category.assoc, Limits.pullback.lift_fst]; exact x.2
  have h := G.mul_natural kwPairingMap t ψ hψ kwPrFst kwPrSnd
  have hfst : schemeHomOverComp ψ hψ kwPrFst = x :=
    Subtype.ext (by rw [schemeHomOverComp_coe]; exact Limits.pullback.lift_fst _ _ _)
  have hsnd : schemeHomOverComp ψ hψ kwPrSnd = y :=
    Subtype.ext (by rw [schemeHomOverComp_coe]; exact Limits.pullback.lift_snd _ _ _)
  rw [hfst, hsnd] at h
  exact (congrArg Subtype.val h).symm

theorem kw_rglcktf_schemeMul_unitPair (G : RelativeGroupLaw R f) :
    Limits.pullback.lift G.kwUnitSection G.kwUnitSection rfl ≫ G.kwSchemeMul
      = G.kwUnitSection := by
  have h := kw_rglcktf_mul_coe_eq_lift_comp_schemeMul G
    (G.one (𝟙 _)) (G.one (𝟙 _))
  rw [G.one_mul] at h
  exact h.symm

end RelativeGroupLaw

end GoodReductionJacobian

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian"

namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul pointGroup one_natural mul_one one mul_natural mk inv one_mul mul formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem kw_rglcktfm_axiomAnchor : True := by
  have _ := Classical.em True
  have _ := @Quot.sound ℕ (· = ·) 0 0 rfl
  have _ := @propext True True Iff.rfl
  trivial

section FourTerm

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

abbrev kwTensorPair (p q : B →ₐ[R] C) : (B ⊗[R] B) →ₐ[R] C :=
  Algebra.TensorProduct.lift p q (fun _ _ => mul_comm _ _)

theorem kw_rglcktfm_fourTerm_tensorPair (ε₀ : B →ₐ[R] R) {J : Ideal C} (hJ2 : J ^ 2 = ⊥)
    (p q : B →ₐ[R] C) (hp : ∀ a ∈ RingHom.ker ε₀, p a ∈ J)
    (hq : ∀ a ∈ RingHom.ker ε₀, q a ∈ J) (z : B ⊗[R] B) :
    kwTensorPair p q z - kwTensorPair p (kwTrivLift ε₀) z
      - kwTensorPair (kwTrivLift ε₀) q z
      + kwTensorPair (kwTrivLift ε₀) (kwTrivLift ε₀) z = 0 := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add]; linear_combination hx + hy
  | tmul b c =>
    simp only [kwTensorPair, Algebra.TensorProduct.lift_tmul]
    have key : (p b - kwTrivLift ε₀ b) * (q c - kwTrivLift ε₀ c) = 0 := by
      have hmem : (p b - kwTrivLift ε₀ b) * (q c - kwTrivLift ε₀ c) ∈ J ^ 2 := by
        rw [pow_two]
        refine Ideal.mul_mem_mul ?_ ?_
        · rw [kw_rglcktf_trivLift_apply]
          have := hp _ (kw_rglcktf_sub_algebraMap_mem_augIdeal ε₀ b)
          rwa [map_sub, AlgHom.commutes] at this
        · rw [kw_rglcktf_trivLift_apply]
          have := hq _ (kw_rglcktf_sub_algebraMap_mem_augIdeal ε₀ c)
          rwa [map_sub, AlgHom.commutes] at this
      rwa [hJ2, Ideal.mem_bot] at hmem
    linear_combination key

theorem kw_rglcktfm_tensorPair_lifts_trivLift (ε₀ : B →ₐ[R] R) {S' : Type*} [CommRing S']
    (φ : C →+* S') (p q : B →ₐ[R] C)
    (hp : ∀ b, φ (p b) = φ (kwTrivLift ε₀ b)) (hq : ∀ b, φ (q b) = φ (kwTrivLift ε₀ b))
    (z : B ⊗[R] B) :
    φ (kwTensorPair p q z)
      = φ (kwTrivLift (kwTensorPair ε₀ ε₀) z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    simp only [kwTensorPair, Algebra.TensorProduct.lift_tmul, kw_rglcktf_trivLift_apply,
      map_mul, hp b, hq c, map_mul]

end FourTerm

section AffineBridge

variable (G : RelativeGroupLaw R f)
variable (B₁ : CommRingCat.{u}) (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
variable (hιe : Set.range G.kwUnitSection.base ⊆ Set.range ι.base)

variable {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
variable (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
variable (t : Spec R' ⟶ Spec (CommRingCat.of R))

def KwIsKerElt (k : SchemeHomOver t f) : Prop :=
  schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t)

theorem kw_rglcktfm_isKerElt_one : KwIsKerElt G φ t (G.one t) :=
  G.one_natural t (Spec.map φ ≫ t) (Spec.map φ) rfl

theorem kw_rglcktfm_isKerElt_mul {x y : SchemeHomOver t f}
    (hx : KwIsKerElt G φ t x) (hy : KwIsKerElt G φ t y) :
    KwIsKerElt G φ t (G.mul t x y) := by
  unfold KwIsKerElt at hx hy ⊢
  rw [G.mul_natural t (Spec.map φ ≫ t) (Spec.map φ) rfl x y, hx, hy, G.one_mul]

theorem kw_rglcktfm_isKerElt_nsmul {k : SchemeHomOver t f} (hk : KwIsKerElt G φ t k)
    (m : ℕ) : KwIsKerElt G φ t (G.nsmul t m k) := by
  induction m with
  | zero => exact kw_rglcktfm_isKerElt_one G φ t
  | succ m ih => rw [G.nsmul_succ]; exact kw_rglcktfm_isKerElt_mul G φ t ih hk

def kwKerRing (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k) : B₁ ⟶ R' :=
  Spec.preimage (IsOpenImmersion.lift ι k.1
    ((kw_rglcktf_range_subset_of_sqZeroKerElem G φ hsurj hker t k hk).trans hιe))

theorem kw_rglcktfm_map_kerRing (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k) :
    Spec.map (kwKerRing G B₁ ι hιe φ hsurj hker t k hk) ≫ ι = k.1 := by
  rw [kwKerRing, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

theorem kw_rglcktfm_eq_of_kerRing_eq {k k' : SchemeHomOver t f}
    (hk : KwIsKerElt G φ t k) (hk' : KwIsKerElt G φ t k')
    (h : kwKerRing G B₁ ι hιe φ hsurj hker t k hk
      = kwKerRing G B₁ ι hιe φ hsurj hker t k' hk') : k = k' :=
  Subtype.ext <| by
    rw [← kw_rglcktfm_map_kerRing G B₁ ι hιe φ hsurj hker t k hk,
      ← kw_rglcktfm_map_kerRing G B₁ ι hιe φ hsurj hker t k' hk', h]

theorem kw_rglcktfm_kerRing_reduces (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k) :
    ∀ b, φ.hom ((kwKerRing G B₁ ι hιe φ hsurj hker t k hk).hom b)
      = φ.hom ((kwKerRing G B₁ ι hιe φ hsurj hker t (G.one t)
          (kw_rglcktfm_isKerElt_one G φ t)).hom b) := by
  intro b
  have heq : Spec.map φ ≫ Spec.map (kwKerRing G B₁ ι hιe φ hsurj hker t k hk)
      = Spec.map φ ≫ Spec.map (kwKerRing G B₁ ι hιe φ hsurj hker t (G.one t)
          (kw_rglcktfm_isKerElt_one G φ t)) := by
    rw [← cancel_mono ι, Category.assoc, Category.assoc,
      kw_rglcktfm_map_kerRing, kw_rglcktfm_map_kerRing,
      ← schemeHomOverComp_coe (Spec.map φ) rfl k, hk,
      ← schemeHomOverComp_coe (Spec.map φ) rfl (G.one t), kw_rglcktfm_isKerElt_one]
  simp only [← Spec.map_comp] at heq
  have := Spec.map_injective heq
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) b

end AffineBridge

section TensorArgument

open Algebra.TensorProduct

variable (G : RelativeGroupLaw R f)
variable (B₁ : CommRingCat.{u}) [Algebra R B₁]
variable (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
variable (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
variable (hιe : Set.range G.kwUnitSection.base ⊆ Set.range ι.base)

include hιf

theorem kw_rglcktfm_preimage_lift_algebraMap {T : CommRingCat.{u}}
    (g : Spec T ⟶ A) (hrange : Set.range g.base ⊆ Set.range ι.base)
    (algT : CommRingCat.of R ⟶ T) (hg : g ≫ f = Spec.map algT) (r : R) :
    (Spec.preimage (IsOpenImmersion.lift ι g hrange)).hom (algebraMap R B₁ r)
      = algT.hom r := by
  have h2 : IsOpenImmersion.lift ι g hrange
      ≫ Spec.map (CommRingCat.ofHom (algebraMap R B₁)) = Spec.map algT := by
    rw [← hιf, ← Category.assoc, IsOpenImmersion.lift_fac, hg]
  have h3 := Spec.preimage_comp (IsOpenImmersion.lift ι g hrange)
    (Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
  rw [h2, Spec.preimage_map, Spec.preimage_map] at h3
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3.symm) r

def kwAug : (B₁ : Type u) →ₐ[R] R :=
  { (Spec.preimage (IsOpenImmersion.lift ι G.kwUnitSection hιe)).hom with
    commutes' := fun r => kw_rglcktfm_preimage_lift_algebraMap B₁ ι hιf
      G.kwUnitSection hιe (𝟙 (CommRingCat.of R)) (G.kwUnitSection_comp.trans
        (Spec.map_id _).symm) r }

theorem kw_rglcktfm_map_aug :
    Spec.map (CommRingCat.ofHom (kwAug G B₁ ι hιf hιe).toRingHom) ≫ ι
      = G.kwUnitSection := by
  have _ := kw_rglcktfm_axiomAnchor
  have : (CommRingCat.ofHom (kwAug G B₁ ι hιf hιe).toRingHom)
      = Spec.preimage (IsOpenImmersion.lift ι G.kwUnitSection hιe) := by
    apply CommRingCat.hom_ext; rfl
  rw [this, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

omit hιf in

def kwTensorStruct : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁))
    ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R ((B₁ : Type u) ⊗[R] B₁)))

def kwTensorPoint (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)) :
    SchemeHomOver (kwTensorStruct (R := R) B₁) f :=
  ⟨Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ι, by
    rw [Category.assoc, hιf, ← Spec.map_comp]; congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show ρ.toRingHom (algebraMap R B₁ r) = algebraMap R ((B₁ : Type u) ⊗[R] B₁) r
    exact ρ.commutes r⟩

def kwUniversalMul : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁)) ⟶ A :=
  (G.mul (kwTensorStruct (R := R) B₁)
    (kwTensorPoint B₁ ι hιf includeLeft) (kwTensorPoint B₁ ι hιf includeRight)).1

abbrev kwAugAug : ((B₁ : Type u) ⊗[R] B₁) →ₐ[R] R :=
  kwTensorPair (kwAug G B₁ ι hιf hιe) (kwAug G B₁ ι hιf hιe)

theorem kw_rglcktfm_augAug_surjective :
    Function.Surjective (kwAugAug G B₁ ι hιf hιe) := fun r =>
  ⟨algebraMap R _ r, (kwAugAug G B₁ ι hιf hιe).commutes r⟩

theorem kw_rglcktfm_universalMul_aug :
    Spec.map (CommRingCat.ofHom (kwAugAug G B₁ ι hιf hιe).toRingHom)
      ≫ kwUniversalMul G B₁ ι hιf = G.kwUnitSection := by
  set εε := kwAugAug G B₁ ι hιf hιe
  have hτ0 : Spec.map (CommRingCat.ofHom εε.toRingHom) ≫ kwTensorStruct (R := R) B₁
      = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [kwTensorStruct, ← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext εε.commutes))
  have hξ : ∀ (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)),
      εε.comp ρ = kwAug G B₁ ι hιf hιe →
      schemeHomOverComp (Spec.map (CommRingCat.ofHom εε.toRingHom)) hτ0
        (kwTensorPoint B₁ ι hιf ρ) = G.one (𝟙 _) := fun ρ hρ => Subtype.ext <| by
    simp only [schemeHomOverComp_coe, kwTensorPoint, ← Category.assoc, ← Spec.map_comp]
    rw [show (G.one (𝟙 _)).1 = G.kwUnitSection from rfl,
      ← kw_rglcktfm_map_aug G B₁ ι hιf hιe]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun b =>
      (DFunLike.congr_fun (congrArg AlgHom.toRingHom hρ) b :))
  have h := G.mul_natural (kwTensorStruct (R := R) B₁) (𝟙 _)
    (Spec.map (CommRingCat.ofHom εε.toRingHom)) hτ0
    (kwTensorPoint B₁ ι hιf includeLeft) (kwTensorPoint B₁ ι hιf includeRight)
  rw [hξ includeLeft (Algebra.TensorProduct.lift_comp_includeLeft _ _ _),
    hξ includeRight (Algebra.TensorProduct.lift_comp_includeRight' _ _ _), G.one_mul] at h
  exact congrArg Subtype.val h

theorem kw_rglcktfm_range_truncMul_subset :
    Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (RingHom.ker (kwAugAug G B₁ ι hιf hιe).toRingHom ^ 2)))
      ≫ kwUniversalMul G B₁ ι hιf).base ⊆ Set.range ι.base := by
  set εε := kwAugAug G B₁ ι hιf hιe
  set 𝔐 := RingHom.ker εε.toRingHom
  rintro _ ⟨p, rfl⟩
  set P := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔐 ^ 2)))).base p with hPdef
  have h𝔐P : 𝔐 ≤ P.asIdeal := by
    intro x hx
    refine P.isPrime.mem_of_pow_mem 2 ?_
    have hx2 : Ideal.Quotient.mk (𝔐 ^ 2) (x ^ 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hx 2)
    show Ideal.Quotient.mk (𝔐 ^ 2) (x ^ 2) ∈ p.asIdeal
    rw [hx2]; exact p.asIdeal.zero_mem

  let q : PrimeSpectrum R := ⟨P.asIdeal.map εε.toRingHom,
    Ideal.map_isPrime_of_surjective (kw_rglcktfm_augAug_surjective G B₁ ι hιf hιe) h𝔐P⟩
  have hqP : (Spec.map (CommRingCat.ofHom εε.toRingHom)).base q = P := PrimeSpectrum.ext <| by
    show Ideal.comap εε.toRingHom (P.asIdeal.map εε.toRingHom) = P.asIdeal
    exact (Ideal.comap_map_of_surjective _
      (kw_rglcktfm_augAug_surjective G B₁ ι hιf hιe) P.asIdeal).trans (sup_eq_left.mpr h𝔐P)
  refine hιe ⟨q, ?_⟩
  show G.kwUnitSection.base q = (kwUniversalMul G B₁ ι hιf).base P
  rw [← hqP, ← kw_rglcktfm_universalMul_aug G B₁ ι hιf hιe]
  rfl

def kwMBar : B₁ ⟶ CommRingCat.of
    (((B₁ : Type u) ⊗[R] B₁) ⧸ RingHom.ker (kwAugAug G B₁ ι hιf hιe).toRingHom ^ 2) :=
  Spec.preimage (IsOpenImmersion.lift ι _ (kw_rglcktfm_range_truncMul_subset G B₁ ι hιf hιe))

theorem kw_rglcktfm_map_mBar :
    Spec.map (kwMBar G B₁ ι hιf hιe) ≫ ι
      = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (RingHom.ker (kwAugAug G B₁ ι hιf hιe).toRingHom ^ 2)))
        ≫ kwUniversalMul G B₁ ι hιf := by
  rw [kwMBar, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

variable {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
variable (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
variable (t : Spec R' ⟶ Spec (CommRingCat.of R))

variable [Algebra R R'] (htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom)

include hιe htR' in

def kwKerAlg (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k) :
    (B₁ : Type u) →ₐ[R] R' :=
  { (kwKerRing G B₁ ι hιe φ hsurj hker t k hk).hom with
    commutes' := fun r => (kw_rglcktfm_preimage_lift_algebraMap B₁ ι hιf k.1 _
      (Spec.preimage t) (k.2.trans (Spec.map_preimage t).symm) r).trans
      (DFunLike.congr_fun htR'.symm r) }

include htR' in
theorem kw_rglcktfm_kerAlg_apply (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k)
    (b : B₁) :
    kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = (kwKerRing G B₁ ι hιe φ hsurj hker t k hk).hom b := by
  have _ := kw_rglcktfm_axiomAnchor; have _ := hιf; have _ := htR'; rfl

include htR' in

theorem kw_rglcktfm_kerAlg_one :
    kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t) (kw_rglcktfm_isKerElt_one G φ t)
      = kwTrivLift (kwAug G B₁ ι hιf hιe) := by
  apply AlgHom.ext; intro b
  rw [kw_rglcktfm_kerAlg_apply, kw_rglcktf_trivLift_apply]
  have heq : Spec.map (kwKerRing G B₁ ι hιe φ hsurj hker t (G.one t)
      (kw_rglcktfm_isKerElt_one G φ t))
      = t ≫ Spec.map (CommRingCat.ofHom (kwAug G B₁ ι hιf hιe).toRingHom) := by
    rw [← cancel_mono ι, kw_rglcktfm_map_kerRing, Category.assoc, kw_rglcktfm_map_aug,
      G.one_coe_eq_comp_one]; rfl
  have hmap : kwKerRing G B₁ ι hιe φ hsurj hker t (G.one t)
      (kw_rglcktfm_isKerElt_one G φ t)
      = CommRingCat.ofHom (kwAug G B₁ ι hιf hιe).toRingHom ≫ Spec.preimage t :=
    Spec.map_injective (heq.trans (by rw [Spec.map_comp, Spec.map_preimage]))
  refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmap) b).trans ?_
  exact DFunLike.congr_fun htR'.symm _

include htR' in

theorem kw_rglcktfm_mul_eq_tensorPair_universalMul
    (x y : SchemeHomOver t f) (hx : KwIsKerElt G φ t x) (hy : KwIsKerElt G φ t y) :
    (G.mul t x y).1
      = Spec.map (CommRingCat.ofHom (kwTensorPair
          (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' x hx)
          (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' y hy)).toRingHom)
        ≫ kwUniversalMul G B₁ ι hιf := by
  set ψ := kwTensorPair (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' x hx)
    (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' y hy)
  have hτ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ kwTensorStruct (R := R) B₁ = t := by
    rw [kwTensorStruct, ← Spec.map_comp, ← Spec.map_preimage t]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (ψ.commutes r).trans (DFunLike.congr_fun htR' r)
  have hξ : ∀ (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)) (z : SchemeHomOver t f)
      (hz : KwIsKerElt G φ t z),
      ψ.comp ρ = kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' z hz →
      schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hτ
        (kwTensorPoint B₁ ι hιf ρ) = z := fun ρ z hz hρ => by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, kwTensorPoint, ← Category.assoc, ← Spec.map_comp]
    rw [← kw_rglcktfm_map_kerRing G B₁ ι hιe φ hsurj hker t z hz]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun b =>
      (DFunLike.congr_fun hρ b).trans rfl)
  have h := G.mul_natural (kwTensorStruct (R := R) B₁) t
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hτ
    (kwTensorPoint B₁ ι hιf includeLeft) (kwTensorPoint B₁ ι hιf includeRight)
  rw [hξ includeLeft x hx (Algebra.TensorProduct.lift_comp_includeLeft _ _ _),
    hξ includeRight y hy (Algebra.TensorProduct.lift_comp_includeRight' _ _ _)] at h
  exact (congrArg Subtype.val h).symm

include htR' in
theorem kw_rglcktfm_kerAlg_val_eq {k k' : SchemeHomOver t f}
    (hk : KwIsKerElt G φ t k) (hk' : KwIsKerElt G φ t k') (h : k = k') (b : B₁) :
    kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k' hk' b := by
  have _ := kw_rglcktfm_axiomAnchor; subst h; rfl

include htR' in

theorem kw_rglcktfm_kerAlg_reduces (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k)
    (b : B₁) :
    φ.hom (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b)
      = φ.hom (kwTrivLift (kwAug G B₁ ι hιf hιe) b) := by
  rw [kw_rglcktfm_kerAlg_apply, kw_rglcktfm_kerRing_reduces G B₁ ι hιe φ hsurj hker t k hk,
    ← kw_rglcktfm_kerAlg_apply G B₁ ι hιf hιe φ hsurj hker t htR',
    kw_rglcktfm_kerAlg_one]

include htR' in

theorem kw_rglcktfm_kerAlg_mul_fourTerm (x y : SchemeHomOver t f)
    (hx : KwIsKerElt G φ t x) (hy : KwIsKerElt G φ t y) (b : B₁) :
    kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.mul t x y)
        (kw_rglcktfm_isKerElt_mul G φ t hx hy) b
      - kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' x hx b
      - kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' y hy b
      + kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (kw_rglcktfm_isKerElt_one G φ t) b = 0 := by
  set ε₀ := kwAug G B₁ ι hιf hιe
  set εε := kwAugAug G B₁ ι hιf hιe
  set 𝔐 := RingHom.ker εε.toRingHom
  have he := kw_rglcktfm_isKerElt_one G φ t

  have hψ2 : ∀ (p q : SchemeHomOver t f) (hp : KwIsKerElt G φ t p)
      (hq : KwIsKerElt G φ t q), ∀ a ∈ 𝔐 ^ 2,
      (kwTensorPair (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
        (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' q hq)).toRingHom a = 0 :=
    fun p q hp hq a ha => kw_rglcktf_eq_zero_of_mem_sq εε φ.hom hker _
      (kw_rglcktfm_tensorPair_lifts_trivLift ε₀ φ.hom _ _
        (kw_rglcktfm_kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
        (kw_rglcktfm_kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' q hq)) ha

  have hfac : ∀ (p q : SchemeHomOver t f) (hp : KwIsKerElt G φ t p)
      (hq : KwIsKerElt G φ t q),
      kwKerRing G B₁ ι hιe φ hsurj hker t (G.mul t p q)
          (kw_rglcktfm_isKerElt_mul G φ t hp hq)
        = kwMBar G B₁ ι hιf hιe ≫ CommRingCat.ofHom (Ideal.Quotient.lift (𝔐 ^ 2)
            (kwTensorPair (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
              (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' q hq)).toRingHom
            (hψ2 p q hp hq)) := fun p q hp hq => by
    apply Spec.map_injective
    rw [← cancel_mono ι, kw_rglcktfm_map_kerRing, Spec.map_comp, Category.assoc,
      kw_rglcktfm_map_mBar, ← Category.assoc, ← Spec.map_comp,
      kw_rglcktfm_mul_eq_tensorPair_universalMul G B₁ ι hιf hιe φ hsurj hker t htR' p q hp hq]
    exact congrArg (· ≫ kwUniversalMul G B₁ ι hιf) (congrArg Spec.map
      (CommRingCat.hom_ext (RingHom.ext fun a =>
        (Ideal.Quotient.lift_mk (𝔐 ^ 2) _ (hψ2 p q hp hq) (a := a)).symm)))

  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((kwMBar G B₁ ι hιf hιe).hom b)
  have h4 : ∀ (p q : SchemeHomOver t f) (hp : KwIsKerElt G φ t p)
      (hq : KwIsKerElt G φ t q),
      kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.mul t p q)
          (kw_rglcktfm_isKerElt_mul G φ t hp hq) b
        = kwTensorPair (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
            (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' q hq) z := fun p q hp hq => by
    have step : (kwKerRing G B₁ ι hιe φ hsurj hker t (G.mul t p q)
          (kw_rglcktfm_isKerElt_mul G φ t hp hq)).hom b
        = Ideal.Quotient.lift (𝔐 ^ 2) _ (hψ2 p q hp hq) ((kwMBar G B₁ ι hιf hιe).hom b) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hfac p q hp hq)) b
    rw [kw_rglcktfm_kerAlg_apply, step, ← hz]
    exact Ideal.Quotient.lift_mk _ _ _

  rw [h4 x y hx hy,
    kw_rglcktfm_kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR' hx
      (kw_rglcktfm_isKerElt_mul G φ t hx he) (G.mul_one t x).symm b,
    h4 x (G.one t) hx he,
    kw_rglcktfm_kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR' hy
      (kw_rglcktfm_isKerElt_mul G φ t he hy) (G.one_mul t y).symm b,
    h4 (G.one t) y he hy,
    kw_rglcktfm_kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR' he
      (kw_rglcktfm_isKerElt_mul G φ t he he) (G.one_mul t (G.one t)).symm b,
    h4 (G.one t) (G.one t) he he, kw_rglcktfm_kerAlg_one]
  exact kw_rglcktfm_fourTerm_tensorPair ε₀ hker _ _
    (fun a ha => kw_rglcktf_mem_kerφ_of_mem_augIdeal ε₀ φ.hom _
      (kw_rglcktfm_kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' x hx) ha)
    (fun a ha => kw_rglcktf_mem_kerφ_of_mem_augIdeal ε₀ φ.hom _
      (kw_rglcktfm_kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' y hy) ha) z

include htR' in
theorem kw_rglcktfm_kerAlg_nsmul_sub (k : SchemeHomOver t f) (hk : KwIsKerElt G φ t k)
    (m : ℕ) (b : B₁) :
    kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.nsmul t m k)
        (kw_rglcktfm_isKerElt_nsmul G φ t hk m) b
      - kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (kw_rglcktfm_isKerElt_one G φ t) b
    = m • (kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      - kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (kw_rglcktfm_isKerElt_one G φ t) b) := by
  induction m with
  | zero =>
    rw [zero_smul,
      kw_rglcktfm_kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR'
        (kw_rglcktfm_isKerElt_nsmul G φ t hk 0) (kw_rglcktfm_isKerElt_one G φ t)
        (G.nsmul_zero t k) b,
      sub_self]
  | succ m ih =>
    have h4 := kw_rglcktfm_kerAlg_mul_fourTerm G B₁ ι hιf hιe φ hsurj hker t htR'
      (G.nsmul t m k) k (kw_rglcktfm_isKerElt_nsmul G φ t hk m) hk b
    rw [kw_rglcktfm_kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR'
        (kw_rglcktfm_isKerElt_nsmul G φ t hk (m + 1))
        (kw_rglcktfm_isKerElt_mul G φ t (kw_rglcktfm_isKerElt_nsmul G φ t hk m) hk)
        (G.nsmul_succ t m k) b,
      succ_nsmul, ← ih]
    linear_combination h4

end TensorArgument

end RelativeGroupLaw

end GoodReductionJacobian

section IsUnitDischarge

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian"

namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul pointGroup one_natural mul_one one mul_natural mk inv one_mul mul formallyUnramified_schemeNsmul_of_forall_sqZero"
p2m_open "GoodReductionJacobian.RelativeGroupLaw"

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem kw_rglckf_sqZeroKerNTorsionFreeAt_of_isUnit (G : RelativeGroupLaw R f)
    {n : ℕ} (hn : IsUnit (n : R)) :
    KwCommRelGroupLawSqZeroKerNTorsionFreeAt G n := by
  intro R' S' φ hsurj hker t k hk hnk

  let pt : (Spec (CommRingCat.of R) : Scheme.{u}) := IsLocalRing.closedPoint R
  let j := A.affineCover.idx (G.kwUnitSection.base pt)
  let B₁ : CommRingCat.{u} := CommRingCat.of Γ(A.affineCover.X j, ⊤)
  haveI : IsAffine (A.affineCover.X j) := inferInstance
  let ι : Spec B₁ ⟶ A := (A.affineCover.X j).isoSpec.inv ≫ A.affineCover.f j
  haveI : IsOpenImmersion ι := inferInstance
  letI : Algebra R B₁ := (Spec.preimage (ι ≫ f)).hom.toAlgebra
  have hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)) :=
    (Spec.map_preimage (ι ≫ f)).symm.trans (congrArg Spec.map (CommRingCat.hom_ext rfl))
  have hιe : Set.range G.kwUnitSection.base ⊆ Set.range ι.base := by
    have hpt : G.kwUnitSection.base pt ∈ Set.range ι.base := by
      obtain ⟨q, hq⟩ := A.affineCover.covers (G.kwUnitSection.base pt)
      exact ⟨(A.affineCover.X j).isoSpec.hom.base q, by
        show (((A.affineCover.X j).isoSpec.hom ≫ (A.affineCover.X j).isoSpec.inv)
          ≫ A.affineCover.f j).base q = _
        rw [Iso.hom_inv_id, Category.id_comp]; exact hq⟩
    have hopen : IsOpen (G.kwUnitSection.base ⁻¹' Set.range ι.base) :=
      ι.isOpenEmbedding.isOpen_range.preimage G.kwUnitSection.base.hom.continuous
    rintro _ ⟨p, rfl⟩
    exact (IsLocalRing.specializes_closedPoint p).mem_open hopen hpt
  letI : Algebra R R' := (Spec.preimage t).hom.toAlgebra
  have htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom := rfl

  have hδ := kw_rglcktfm_kerAlg_nsmul_sub G B₁ ι hιf hιe φ hsurj hker t htR' k hk n
  simp only [kw_rglcktfm_kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR'
    (kw_rglcktfm_isKerElt_nsmul G φ t hk n) (kw_rglcktfm_isKerElt_one G φ t) hnk,
    sub_self, nsmul_eq_mul] at hδ
  have hun : IsUnit (n : R') := by
    have := hn.map (algebraMap R R'); rwa [map_natCast] at this
  have hkR0 : ∀ b, kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = kwKerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (kw_rglcktfm_isKerElt_one G φ t) b := fun b =>
    sub_eq_zero.mp (hun.mul_left_cancel ((hδ b).symm.trans (mul_zero _).symm))
  refine kw_rglcktfm_eq_of_kerRing_eq G B₁ ι hιe φ hsurj hker t hk
    (kw_rglcktfm_isKerElt_one G φ t) (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
  rw [← kw_rglcktfm_kerAlg_apply G B₁ ι hιf hιe φ hsurj hker t htR',
    ← kw_rglcktfm_kerAlg_apply G B₁ ι hιf hιe φ hsurj hker t htR', hkR0]

end RelativeGroupLaw

end GoodReductionJacobian

end IsUnitDischarge

end

namespace GoodReductionJacobian p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero" namespace RelativeGroupLaw p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul pointGroup one_natural mul_one one mul_natural mk inv one_mul mul formallyUnramified_schemeNsmul_of_forall_sqZero" end GoodReductionJacobian.RelativeGroupLaw
p2m_open_scoped "GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw" in
open CategoryTheory AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.GoodReductionJacobian in
theorem GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) (hn : IsUnit (n : R))
    (R' S' : CommRingCat.{u}) (φ : R' ⟶ S') (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hk : schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t))
    (hnk : G.nsmul t n k = G.one t) :
    k = G.one t :=
  GoodReductionJacobian.RelativeGroupLaw.kw_rglckf_sqZeroKerNTorsionFreeAt_of_isUnit G hn R' S' φ hφ hker t k hk hnk

open CategoryTheory AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.GoodReductionJacobian in
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) :=
  GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero G hcomm n
    (fun R' S' φ hφ hker t k hk hnk ↦
      GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit_of_isLocalRing
        G n hn R' S' φ hφ hker t k hk hnk)

end S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing (solution)
