-- Prove2me | solution 1 for HeckeEis.exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/370af123-7853-5a25-8301-c46e4ad47f28

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import Definitions.Def_GroupCohomology_DClassCoeff
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1

set_option autoImplicit false

open groupCohomology

namespace D1Chi

universe u

variable {K G V : Type u} [CommRing K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V)

theorem mem_cocycles₁_iff_mem_coeffCocycles (z : G → V) :
    z ∈ cocycles₁ (Rep.of ρ) ↔ z ∈ HeckeEis.coeffCocycles ρ := by
  rw [mem_cocycles₁_iff, HeckeEis.mem_coeffCocycles_iff]
  simp only [Rep.of_ρ]
  exact forall₂_congr fun g h => by rw [add_comm]

theorem mem_coboundaries₁_iff_mem_coeffCoboundaries (z : G → V) :
    z ∈ coboundaries₁ (Rep.of ρ) ↔ z ∈ HeckeEis.coeffCoboundaries ρ := by
  rw [HeckeEis.mem_coeffCoboundaries_iff, coboundaries₁, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

def cocyclesEquiv : HeckeEis.coeffCocycles ρ ≃ₗ[K] cocycles₁ (Rep.of ρ) where
  toFun z := ⟨(z : G → V), (mem_cocycles₁_iff_mem_coeffCocycles ρ _).mpr z.2⟩
  invFun f := ⟨(f : G → V), (mem_cocycles₁_iff_mem_coeffCocycles ρ _).mp f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[scoped simp] theorem coe_cocyclesEquiv (z : HeckeEis.coeffCocycles ρ) : ((cocyclesEquiv ρ z : cocycles₁ (Rep.of ρ)) : G → V) = z := rfl
@[scoped simp] theorem coe_cocyclesEquiv_symm (f : cocycles₁ (Rep.of ρ)) :
    (((cocyclesEquiv ρ).symm f : HeckeEis.coeffCocycles ρ) : G → V) = f := rfl

noncomputable def toH1 : HeckeEis.coeffH1 ρ →ₗ[K] H1 (Rep.of ρ) :=
  ((HeckeEis.coeffCoboundaries ρ).comap (HeckeEis.coeffCocycles ρ).subtype).liftQ
    ((H1π (Rep.of ρ)).hom ∘ₗ (cocyclesEquiv ρ).toLinearMap) (by
      intro z hz
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      show H1π (Rep.of ρ) (cocyclesEquiv ρ z) = 0
      rw [H1π_eq_zero_iff, coe_cocyclesEquiv, mem_coboundaries₁_iff_mem_coeffCoboundaries]
      exact hz)

theorem toH1_coeffH1Mk (z : HeckeEis.coeffCocycles ρ) :
    toH1 ρ (HeckeEis.coeffH1Mk ρ z) = H1π (Rep.of ρ) (cocyclesEquiv ρ z) := rfl

theorem toH1_injective : Function.Injective (toH1 ρ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective ρ x
  rw [LinearMap.mem_ker, toH1_coeffH1Mk, H1π_eq_zero_iff, coe_cocyclesEquiv,
    mem_coboundaries₁_iff_mem_coeffCoboundaries] at hx
  exact (HeckeEis.coeffH1Mk_eq_zero_iff ρ z).mpr hx

theorem toH1_surjective : Function.Surjective (toH1 ρ) := by
  intro y
  induction y using H1_induction_on with
  | h f => exact ⟨HeckeEis.coeffH1Mk ρ ((cocyclesEquiv ρ).symm f), by
      rw [toH1_coeffH1Mk, LinearEquiv.apply_symm_apply]⟩

noncomputable def H1Equiv : HeckeEis.coeffH1 ρ ≃ₗ[K] H1 (Rep.of ρ) :=
  LinearEquiv.ofBijective (toH1 ρ) ⟨toH1_injective ρ, toH1_surjective ρ⟩

theorem H1Equiv_coeffH1Mk (z : HeckeEis.coeffCocycles ρ) :
    H1Equiv ρ (HeckeEis.coeffH1Mk ρ z) = H1π (Rep.of ρ) (cocyclesEquiv ρ z) := rfl

theorem H1Equiv_symm_H1π (f : cocycles₁ (Rep.of ρ)) :
    (H1Equiv ρ).symm (H1π (Rep.of ρ) f) = HeckeEis.coeffH1Mk ρ ((cocyclesEquiv ρ).symm f) := by
  rw [LinearEquiv.symm_apply_eq, H1Equiv_coeffH1Mk, LinearEquiv.apply_symm_apply]

section Res

variable {H : Type u} [Group H] (f : H →* G)

def coeffResCocycles : HeckeEis.coeffCocycles ρ →ₗ[K] HeckeEis.coeffCocycles (ρ.comp f) where
  toFun z := ⟨fun h => (z : G → V) (f h), fun h h' => by
    show (z : G → V) (f (h * h')) = (z : G → V) (f h) + (ρ.comp f) h ((z : G → V) (f h'))
    rw [map_mul, z.2]; rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem coe_coeffResCocycles (z : HeckeEis.coeffCocycles ρ) (h : H) :
    (coeffResCocycles ρ f z : H → V) h = (z : G → V) (f h) := rfl

def coeffRes : HeckeEis.coeffH1 ρ →ₗ[K] HeckeEis.coeffH1 (ρ.comp f) :=
  ((HeckeEis.coeffCoboundaries ρ).comap (HeckeEis.coeffCocycles ρ).subtype).mapQ
    ((HeckeEis.coeffCoboundaries (ρ.comp f)).comap (HeckeEis.coeffCocycles (ρ.comp f)).subtype)
    (coeffResCocycles ρ f) (by
      intro z hz
      rw [Submodule.mem_comap, Submodule.coe_subtype, HeckeEis.mem_coeffCoboundaries_iff] at hz
      show ((coeffResCocycles ρ f z : HeckeEis.coeffCocycles (ρ.comp f)) : H → V) ∈ HeckeEis.coeffCoboundaries (ρ.comp f)
      rw [HeckeEis.mem_coeffCoboundaries_iff]
      obtain ⟨v, hv⟩ := hz
      refine ⟨v, ?_⟩
      ext h
      show (ρ.comp f) h v - v = (z : G → V) (f h)
      rw [← hv]; rfl)

theorem coeffRes_coeffH1Mk (z : HeckeEis.coeffCocycles ρ) :
    coeffRes ρ f (HeckeEis.coeffH1Mk ρ z) = HeckeEis.coeffH1Mk (ρ.comp f) (coeffResCocycles ρ f z) := rfl

noncomputable def resH1 : H1 (Rep.of ρ) →ₗ[K] H1 (Rep.of (ρ.comp f)) :=
  (H1Equiv (ρ.comp f)).toLinearMap ∘ₗ coeffRes ρ f ∘ₗ (H1Equiv ρ).symm.toLinearMap

def resCocycles : cocycles₁ (Rep.of ρ) →ₗ[K] cocycles₁ (Rep.of (ρ.comp f)) :=
  (cocyclesEquiv (ρ.comp f)).toLinearMap ∘ₗ coeffResCocycles ρ f ∘ₗ (cocyclesEquiv ρ).symm.toLinearMap

@[scoped simp] theorem coe_resCocycles (z : cocycles₁ (Rep.of ρ)) (h : H) : (resCocycles ρ f z : H → V) h = (z : G → V) (f h) := rfl

theorem resH1_H1π (z : cocycles₁ (Rep.of ρ)) : resH1 ρ f (H1π (Rep.of ρ) z) = H1π (Rep.of (ρ.comp f)) (resCocycles ρ f z) := by
  rw [resH1, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  erw [H1Equiv_symm_H1π]
  rw [coeffRes_coeffH1Mk, H1Equiv_coeffH1Mk]
  rfl

theorem coeffRes_injective_of_normal (N : Subgroup G) [N.Normal]
    (hinv : ∀ v : V, (∀ n ∈ N, ρ n v = v) → v = 0) :
    Function.Injective (coeffRes ρ N.subtype) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective ρ x
  rw [LinearMap.mem_ker, coeffRes_coeffH1Mk, HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff] at hx
  obtain ⟨v, hv⟩ := hx

  set w : G → V := fun g => (z : G → V) g - (ρ g v - v) with hw
  have hwN : ∀ n ∈ N, w n = 0 := by
    intro n hn
    have := congrFun hv ⟨n, hn⟩
    simp only [coe_coeffResCocycles, Subgroup.coe_subtype] at this
    show (z : G → V) n - (ρ n v - v) = 0
    rw [← this]; exact sub_self _
  have hwc : ∀ g h : G, w (g * h) = w g + ρ g (w h) := by
    intro g h
    simp only [hw, z.2 g h, map_sub, map_mul, Module.End.mul_apply]
    abel

  have hw0 : ∀ g : G, w g = 0 := by
    intro g
    apply hinv
    intro n hn

    set m := g⁻¹ * n * g with hm
    have hmN : m ∈ N := by
      have := Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
      simpa [hm, mul_assoc] using this
    have h1 : w (g * m) = w g := by rw [hwc, hwN m hmN, map_zero, add_zero]
    have h2 : w (n * g) = ρ n (w g) := by rw [hwc, hwN n hn, zero_add]
    have hgm : g * m = n * g := by rw [hm]; group
    rw [← h2, ← hgm, h1]

  rw [HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff]
  refine ⟨v, ?_⟩
  ext g
  have := hw0 g
  simp only [hw, sub_eq_zero] at this
  exact this.symm

theorem resH1_injective_of_normal (N : Subgroup G) [N.Normal]
    (hinv : ∀ v : V, (∀ n ∈ N, ρ n v = v) → v = 0) :
    Function.Injective (resH1 ρ N.subtype) := by
  intro x y hxy
  simp only [resH1, LinearMap.comp_apply, LinearEquiv.coe_coe] at hxy
  have := (H1Equiv (ρ.comp N.subtype)).injective hxy
  have := coeffRes_injective_of_normal ρ N hinv this
  exact (H1Equiv ρ).symm.injective this

end Res

end D1Chi
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi"

set_option autoImplicit false

open groupCohomology

namespace D1Chi

section Transversal

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (K : Subgroup G) (φ : K →* G) (a : V →ₗ[k] V)

abbrev RQ : Type := Quotient (QuotientGroup.rightRel K)

structure Transversal where
  R : RQ K → G
  hR : ∀ q : RQ K, (Quotient.mk'' (R q) : RQ K) = q

variable {K}

theorem rho_rho (x y : G) (v : V) : ρ x (ρ y v) = ρ (x * y) v := by
  rw [map_mul, Module.End.mul_apply]

namespace Transversal

variable (T : Transversal K)

theorem slip_mem (q : RQ K) (γ : G) : T.R q * γ * (T.R (HeckeCohomology.mulRight K γ q))⁻¹ ∈ K := by
  have h1 : HeckeCohomology.mulRight K γ q = HeckeCohomology.cls K (T.R q * γ) := by
    conv_lhs => rw [← T.hR q]
    rfl
  have h2 : (Quotient.mk'' (T.R (HeckeCohomology.mulRight K γ q)) : RQ K) = Quotient.mk'' (T.R q * γ) := by
    rw [T.hR, h1]
  have h3 : QuotientGroup.rightRel K (T.R (HeckeCohomology.mulRight K γ q)) (T.R q * γ) := Quotient.exact' h2
  rw [QuotientGroup.rightRel_apply] at h3
  simpa [mul_assoc] using h3

noncomputable def slip (q : RQ K) (γ : G) : K := ⟨T.R q * γ * (T.R (HeckeCohomology.mulRight K γ q))⁻¹, T.slip_mem q γ⟩

@[scoped simp] theorem coe_slip (q : RQ K) (γ : G) : (T.slip q γ : G) = T.R q * γ * (T.R (HeckeCohomology.mulRight K γ q))⁻¹ := rfl

theorem mulRight_mul (γ δ : G) (q : RQ K) :
    HeckeCohomology.mulRight K (γ * δ) q = HeckeCohomology.mulRight K δ (HeckeCohomology.mulRight K γ q) := by
  induction q using Quotient.inductionOn' with
  | h x => exact congrArg (fun y : G => (Quotient.mk'' y : RQ K)) (mul_assoc x γ δ).symm

theorem slip_mul (q : RQ K) (γ δ : G) :
    T.slip q (γ * δ) = T.slip q γ * T.slip (HeckeCohomology.mulRight K γ q) δ := by
  apply Subtype.ext
  simp only [coe_slip, Subgroup.coe_mul, mulRight_mul, mul_assoc, inv_mul_cancel_left]

variable (K) in

noncomputable def out : Transversal K where
  R := HeckeCohomology.rep K
  hR q := Quotient.out_eq' q

end Transversal
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

variable [K.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def TR (T : Transversal K) (f : G → V) (γ : G) : V :=
  ∑ q : RQ K, ρ (T.R q)⁻¹ (a (f (φ (T.slip q γ))))

theorem heckeZ1_eq_TR (ha : HeckeCohomology.IsTwist ⊤ K (φ.codRestrict ⊤ fun _ => Subgroup.mem_top _) (Rep.of ρ) a)
    (f : cocycles₁ (Rep.of ρ)) (γ : G) :
    (HeckeCohomology.heckeZ1 ⊤ K (φ.codRestrict ⊤ fun _ => Subgroup.mem_top _) (Rep.of ρ) a ha f : G → V) γ =
      TR ρ φ a (Transversal.out K) f γ := by
  rw [HeckeCohomology.heckeZ1_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hs : (HeckeCohomology.slip K q γ : G) = ((Transversal.out K).slip q γ : G) := by
    simp only [HeckeCohomology.slip, Transversal.coe_slip, Transversal.out, HeckeCohomology.mulRight_apply]
  have hs' : HeckeCohomology.slip K q γ = (Transversal.out K).slip q γ := Subtype.ext hs
  rw [hs']
  rfl

variable {ρ φ a}

theorem TR_sub_TR (ha : ∀ (s : K) (v : V), a (ρ (φ s) v) = ρ s (a v))
    (f : G → V) (hf : ∀ x y : G, f (x * y) = f x + ρ x (f y))
    (T T' : Transversal K) :
    ∃ b : V, ∀ γ : G, TR ρ φ a T' f γ - TR ρ φ a T f γ = b - ρ γ b := by

  have hk : ∀ q : RQ K, T'.R q * (T.R q)⁻¹ ∈ K := fun q => by
    have h3 : QuotientGroup.rightRel K (T.R q) (T'.R q) := Quotient.exact' ((T.hR q).trans (T'.hR q).symm)
    rwa [QuotientGroup.rightRel_apply] at h3
  let kq : RQ K → K := fun q => ⟨T'.R q * (T.R q)⁻¹, hk q⟩
  have hkq : ∀ q, (kq q : G) = T'.R q * (T.R q)⁻¹ := fun q => rfl
  have hR' : ∀ q, T'.R q = (kq q : G) * T.R q := fun q => by rw [hkq, inv_mul_cancel_right]

  have hf1 : f 1 = 0 := by have := hf 1 1; simp at this; exact this
  have hfinv : ∀ x : G, f x⁻¹ = - ρ x⁻¹ (f x) := fun x => by
    have := hf x⁻¹ x
    rw [inv_mul_cancel, hf1] at this
    exact eq_neg_of_add_eq_zero_left this.symm

  have hainv : ∀ (s : K) (v : V), a (ρ (φ s)⁻¹ v) = ρ (s : G)⁻¹ (a v) := fun s v => by
    have h0 : ρ (φ s) (ρ (φ s)⁻¹ v) = v := by rw [rho_rho, mul_inv_cancel, map_one, Module.End.one_apply]
    have := ha s (ρ (φ s)⁻¹ v)
    rw [h0] at this
    rw [this, rho_rho, inv_mul_cancel, map_one, Module.End.one_apply]

  let e : RQ K → V := fun q => ρ (T.R q)⁻¹ (ρ ((kq q : G))⁻¹ (a (f (φ (kq q)))))
  refine ⟨∑ q, e q, fun γ => ?_⟩

  have hslip : ∀ q, T'.slip q γ = kq q * T.slip q γ * (kq (HeckeCohomology.mulRight K γ q))⁻¹ := fun q => by
    apply Subtype.ext
    simp only [Transversal.coe_slip, Subgroup.coe_mul, Subgroup.coe_inv, hR', mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel_left]

  have hterm : ∀ q, ρ (T'.R q)⁻¹ (a (f (φ (T'.slip q γ)))) =
      e q + ρ (T.R q)⁻¹ (a (f (φ (T.slip q γ)))) - ρ γ (e (HeckeCohomology.mulRight K γ q)) := by
    intro q

    have hfs : f (φ (T'.slip q γ)) =
        f (φ (kq q)) + ρ (φ (kq q)) (f (φ (T.slip q γ))) - ρ (φ (kq q)) (ρ (φ (T.slip q γ)) (ρ (φ (kq (HeckeCohomology.mulRight K γ q)))⁻¹ (f (φ (kq (HeckeCohomology.mulRight K γ q)))))) := by
      rw [hslip, map_mul, map_mul, map_inv, hf, hf, hfinv, map_neg, ← rho_rho]
      abel

    have hRinv : ∀ v : V, ρ (T'.R q)⁻¹ v = ρ (T.R q)⁻¹ (ρ ((kq q : G))⁻¹ v) := fun v => by
      rw [rho_rho, ← mul_inv_rev, ← hR']

    have hY : ρ ((kq q : G))⁻¹ (a (ρ (φ (kq q)) (f (φ (T.slip q γ))))) = a (f (φ (T.slip q γ))) := by
      rw [ha, rho_rho, inv_mul_cancel, map_one, Module.End.one_apply]
    have hZ : ρ (T.R q)⁻¹ (ρ ((kq q : G))⁻¹ (a (ρ (φ (kq q)) (ρ (φ (T.slip q γ)) (ρ (φ (kq (HeckeCohomology.mulRight K γ q)))⁻¹ (f (φ (kq (HeckeCohomology.mulRight K γ q))))))))) =
        ρ γ (e (HeckeCohomology.mulRight K γ q)) := by
      rw [ha, rho_rho ρ ((kq q : G))⁻¹, inv_mul_cancel, map_one, Module.End.one_apply, ha (T.slip q γ), hainv, rho_rho, rho_rho]
      show ρ ((T.R q)⁻¹ * (T.slip q γ : G) * ((kq (HeckeCohomology.mulRight K γ q) : G))⁻¹) (a (f (φ (kq (HeckeCohomology.mulRight K γ q))))) = ρ γ (e (HeckeCohomology.mulRight K γ q))
      simp only [e]
      rw [rho_rho, rho_rho]
      congr 2
      rw [Transversal.coe_slip]
      group
    rw [hfs, map_sub, map_add, hRinv, map_sub, map_add, map_sub, map_add, hY, hZ]
  simp only [TR, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum]
  rw [show ∑ q, ρ γ (e (HeckeCohomology.mulRight K γ q)) = ∑ q, ρ γ (e q) from
    Fintype.sum_equiv (HeckeCohomology.mulRight K γ) _ _ fun _ => rfl]
  abel

omit [K.FiniteIndex] in

theorem iota_mulRight (g : G) (q : RQ K) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel K (HeckeCohomology.mulRight K g q) =
      g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel K q := by
  induction q using Quotient.inductionOn' with
  | h x =>
    show (QuotientGroup.mk ((x * g)⁻¹) : G ⧸ K) = g⁻¹ • (QuotientGroup.mk x⁻¹ : G ⧸ K)
    rw [mul_inv_rev]
    rfl

variable (K) in

noncomputable def invOut : Transversal K where
  R q := ((QuotientGroup.quotientRightRelEquivQuotientLeftRel K q).out)⁻¹
  hR q := by
    set ι := QuotientGroup.quotientRightRelEquivQuotientLeftRel K
    have h1 : ∀ y : G, ι.symm (Quotient.mk'' y : G ⧸ K) = (Quotient.mk'' y⁻¹ : RQ K) := fun y => rfl
    have : (Quotient.mk'' ((ι q).out)⁻¹ : RQ K) = ι.symm (Quotient.mk'' (ι q).out : G ⧸ K) := (h1 _).symm
    rw [this, Quotient.out_eq', Equiv.symm_apply_apply]

theorem invOut_R (q : RQ K) : (invOut K).R q = ((QuotientGroup.quotientRightRelEquivQuotientLeftRel K q).out)⁻¹ := rfl

theorem sum_left_eq_TR (f : G → V) (g : G) :
    (letI := K.fintypeQuotientOfFiniteIndex
     ∑ p : G ⧸ K, ρ (g • p).out (a (f (φ ⟨(g • p).out⁻¹ * (g * p.out), by
        refine QuotientGroup.eq.mp ?_
        rw [QuotientGroup.out_eq']
        show g • p = ((g * p.out : G) : G ⧸ K)
        rw [show ((g * p.out : G) : G ⧸ K) = g • ((p.out : G) : G ⧸ K) from rfl, QuotientGroup.out_eq']⟩)))) =
      TR ρ φ a (invOut K) f g := by
  letI := K.fintypeQuotientOfFiniteIndex
  set ι := QuotientGroup.quotientRightRelEquivQuotientLeftRel K with hι

  let e : (G ⧸ K) ≃ RQ K := (MulAction.toPerm g).trans ι.symm
  unfold TR
  refine (Fintype.sum_equiv e _ _ fun p => ?_)
  have he : ι (e p) = g • p := by simp [e]
  have hR : (invOut K).R (e p) = ((g • p).out)⁻¹ := by rw [invOut_R, ← hι, he]
  have hR2 : (invOut K).R (HeckeCohomology.mulRight K g (e p)) = (p.out)⁻¹ := by
    rw [invOut_R, ← hι, iota_mulRight, he, inv_smul_smul]
  rw [hR, inv_inv]
  congr 3
  apply congrArg φ
  apply Subtype.ext
  rw [Transversal.coe_slip, hR, hR2, inv_inv, mul_assoc]

end Transversal
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

section CC

variable (N ℓ : ℕ) [NeZero ℓ] {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
  (ρ : Representation K ↥(CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem coeffHeckeFun_eq_TR (z : ↥(CongruenceSubgroup.Gamma0 N) → V) (g : ↥(CongruenceSubgroup.Gamma0 N)) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z g = TR ρ (HeckeEis.heckeConj N ℓ) a (invOut (HeckeEis.heckeUpper N ℓ)) z g := by
  rw [HeckeEis.coeffHeckeFun_apply]
  exact sum_left_eq_TR (ρ := ρ) (φ := HeckeEis.heckeConj N ℓ) (a := a) z g

end CC
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

section Restrict

variable {k G G' V : Type} [CommRing k] [Group G] [Group G'] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (a : V →ₗ[k] V)
variable {K : Subgroup G} {K' : Subgroup G'} (φ : K →* G) (φ' : K' →* G') (j : G' →* G)
variable (hK : ∀ x : G', x ∈ K' ↔ j x ∈ K)

def betaQ (hK : ∀ x : G', x ∈ K' ↔ j x ∈ K) : RQ K' → RQ K :=
  Quotient.map' j fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact (hK _).mp h

theorem betaQ_mk (x : G') : betaQ j hK (Quotient.mk'' x) = Quotient.mk'' (j x) := rfl

theorem betaQ_mulRight (γ : G') (q : RQ K') :
    betaQ j hK (HeckeCohomology.mulRight K' γ q) = HeckeCohomology.mulRight K (j γ) (betaQ j hK q) := by
  induction q using Quotient.inductionOn' with
  | h x =>
    show (Quotient.mk'' (j (x * γ)) : RQ K) = Quotient.mk'' (j x * j γ)
    rw [map_mul]

variable (β : RQ K' ≃ RQ K) (hβ : ∀ q, β q = betaQ j hK q)

noncomputable def Transversal.push (T' : Transversal K') : Transversal K where
  R Q := j (T'.R (β.symm Q))
  hR Q := by
    have : (Quotient.mk'' (j (T'.R (β.symm Q))) : RQ K) = betaQ j hK (Quotient.mk'' (T'.R (β.symm Q))) := rfl
    rw [this, T'.hR, ← hβ, Equiv.apply_symm_apply]

variable [K.FiniteIndex] [K'.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem TR_push (hφ : ∀ s : K', j (φ' s) = φ ⟨j s, (hK s).mp s.2⟩) (T' : Transversal K') (f : G → V) (γ : G') :
    TR ρ φ a (Transversal.push j hK β hβ T') f (j γ) = TR (ρ.comp j) φ' a T' (f ∘ j) γ := by
  unfold TR
  rw [← Fintype.sum_equiv β (fun q => ρ (j (T'.R q))⁻¹ (a (f (φ ((Transversal.push j hK β hβ T').slip (β q) (j γ))))))
    _ (fun q => by simp only [Transversal.push, Equiv.symm_apply_apply])]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [MonoidHom.comp_apply, map_inv j, Function.comp_apply, hφ]
    congr 3
    apply congrArg φ
    apply Subtype.ext
    show j (T'.R (β.symm (β q))) * j γ * (j (T'.R (β.symm (HeckeCohomology.mulRight K (j γ) (β q)))))⁻¹ =
      j (T'.R q * γ * (T'.R (HeckeCohomology.mulRight K' γ q))⁻¹)
    rw [Equiv.symm_apply_apply, hβ, ← betaQ_mulRight, ← hβ, Equiv.symm_apply_apply, map_mul, map_mul, map_inv]

end Restrict
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

end D1Chi
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

set_option autoImplicit false

open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

namespace D1Chi

section Setup

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

abbrev red : ↥(Gamma0 N) →* CuspidalType.GL2 q :=
  ((Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)

abbrev incl : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) →* ↥(Gamma0 N) :=
  Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))

variable {κ : Type} [Field κ] {V : Type} [AddCommGroup V] [Module κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)

noncomputable abbrev adj (ℓ : ℕ) : V →ₗ[κ] V :=
  if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id

theorem diag_mul_conjUpperMat (ℓ : ℕ) (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    !![(ℓ : ℤ), 0; 0, 1] * ((CohCarrier.conjUpperMat ℓ A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (A : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by
  have h01 : (ℓ : ℤ) * (A 0 1 / (ℓ : ℤ)) = A 0 1 := Int.mul_ediv_cancel' h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, h01, mul_comm]

theorem isTwist_adj (ℓ : ℕ) (hℓ : ((ℓ : ZMod q) ≠ 0)) :
    HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
      (Rep.of (((ρ.comp (red N q)).comp (incl N)))) (adj q ρ ℓ) := by

  set D : CuspidalType.GL2 q := CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) hℓ) with hD
  have key : ∀ s : ↥(CohCarrier.GammaHUpper N ⊥ ℓ),
      D * red N q (incl N ((HeckeCohomology.cTop N ⊥ ℓ s : (⊤ : Subgroup _)) : ↥(CohCarrier.GammaH N ⊥))) =
        red N q (incl N (s : ↥(CohCarrier.GammaH N ⊥))) * D := by
    intro s
    apply Units.ext
    have hint := diag_mul_conjUpperMat ℓ ((s : ↥(CohCarrier.GammaH N ⊥)) : SL(2, ℤ))
      (CohCarrier.dvd_of_mem_GammaHUpper N ⊥ ℓ s)
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom (ZMod q))) hint
    rw [Matrix.map_mul, Matrix.map_mul] at this
    have hDm : ((D : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        (!![(ℓ : ℤ), 0; 0, 1]).map (Int.castRingHom (ZMod q)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hD, CuspidalType.diagElem]
    have h1 : ∀ x : ↥(CohCarrier.GammaH N ⊥), ((red N q (incl N x) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod q)) := fun x => rfl
    rw [Units.val_mul, Units.val_mul, hDm, h1, h1]
    exact this
  intro s a
  simp only [adj, dif_pos hℓ]
  change ρ D (ρ (red N q (incl N _)) a) = ρ (red N q (incl N _)) (ρ D a)
  rw [← Module.End.mul_apply, ← map_mul, key s, map_mul, Module.End.mul_apply]

theorem exists_gammaH_bot_map_eq (hqN : ¬ q ∣ N) (g : SL(2, ZMod q)) :
    ∃ γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) (γ : SL(2, ℤ)) = g := by
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
  haveI : NeZero (q * N) := ⟨Nat.mul_ne_zero hq.ne_zero (NeZero.ne N)⟩

  let e : ZMod (q * N) ≃+* ZMod q × ZMod N := ZMod.chineseRemainder hcop
  let πq : ZMod (q * N) →+* ZMod q := (RingHom.fst _ _).comp e.toRingHom
  let πN : ZMod (q * N) →+* ZMod N := (RingHom.snd _ _).comp e.toRingHom

  let Mm : Matrix (Fin 2) (Fin 2) (ZMod (q * N)) := fun i j => e.symm ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) i j, (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) i j)
  have hMq : Mm.map πq = (g : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    ext i j; simp [Mm, πq, Matrix.map_apply]
  have hMN : Mm.map πN = 1 := by
    ext i j; simp [Mm, πN, Matrix.map_apply]
  have hdet : Mm.det = 1 := by
    have hg : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 1 := by
      have := g.prop; rwa [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two]
    simp only [Mm]
    rw [← map_mul, ← map_mul, ← map_sub]
    have : (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0, (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) *
        ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1, (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1) -
        ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1, (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1) *
        ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0, (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0) : ZMod q × ZMod N) = 1 := by
      ext
      · simpa using hg
      · simp [Matrix.one_apply]
    rw [this, map_one]
  let M : SL(2, ZMod (q * N)) := ⟨Mm, hdet⟩

  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod (q * N) M

  have hγN : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ = 1 := by
    have : (Int.castRingHom (ZMod N)) = πN.comp (Int.castRingHom (ZMod (q * N))) := RingHom.ext_int _ _
    apply Matrix.SpecialLinearGroup.ext; intro i j
    have h2 := congrArg (fun A : SL(2, ZMod (q * N)) => ((A : Matrix (Fin 2) (Fin 2) (ZMod (q * N))).map πN) i j) hγ
    simp only [M, hMN] at h2
    rw [this]
    simpa [Matrix.SpecialLinearGroup.map, Matrix.map_apply] using h2
  have hγq : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ = g := by
    have : (Int.castRingHom (ZMod q)) = πq.comp (Int.castRingHom (ZMod (q * N))) := RingHom.ext_int _ _
    apply Matrix.SpecialLinearGroup.ext; intro i j
    have h2 := congrArg (fun A : SL(2, ZMod (q * N)) => ((A : Matrix (Fin 2) (Fin 2) (ZMod (q * N))).map πq) i j) hγ
    simp only [M, hMq] at h2
    rw [this]
    simpa [Matrix.SpecialLinearGroup.map, Matrix.map_apply] using h2
  have hγΓ : γ ∈ Gamma N := by
    rw [Gamma_mem']
    exact hγN
  have hγH : γ ∈ CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ) := by
    rw [Gamma_mem] at hγΓ
    obtain ⟨h00, h01, h10, h11⟩ := hγΓ
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [Subgroup.mem_bot]
    apply Units.ext
    rw [CohCarrier.val_gamma0Units]
    exact h11
  exact ⟨⟨γ, hγH⟩, hγq⟩

theorem eq_zero_of_forall_gammaH (hqN : ¬ q ∣ N)
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0)
    (v : V) (hv : ∀ γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)), ρ (red N q (incl N γ)) v = v) : v = 0 := by
  refine hV v fun g => ?_
  obtain ⟨γ, hγ⟩ := exists_gammaH_bot_map_eq N q hqN g
  rw [← hγ]
  exact hv γ

theorem coeffRes_injective_of_conj {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module κ W]
    (τ : Representation κ G W) (f : H →* G)
    (hconj : ∀ (g : G) (h : H), ∃ h' : H, f h' = g * f h * g⁻¹)
    (hinv : ∀ w : W, (∀ h : H, τ (f h) w = w) → w = 0) :
    Function.Injective (coeffRes τ f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective τ x
  rw [LinearMap.mem_ker, coeffRes_coeffH1Mk, HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff] at hx
  obtain ⟨v, hv⟩ := hx
  set u : G → W := fun g => (z : G → W) g - (τ g v - v) with hu
  have huH : ∀ h : H, u (f h) = 0 := by
    intro h
    have := congrFun hv h
    simp only [coe_coeffResCocycles] at this
    show (z : G → W) (f h) - (τ (f h) v - v) = 0
    rw [← this]; exact sub_self _
  have huc : ∀ g g' : G, u (g * g') = u g + τ g (u g') := by
    intro g g'
    simp only [hu, z.2 g g', map_sub, map_mul, Module.End.mul_apply]
    abel
  have hu0 : ∀ g : G, u g = 0 := by
    intro g
    apply hinv
    intro h
    obtain ⟨h', hh'⟩ := hconj g⁻¹ h

    have h1 : u (g * f h') = u g := by rw [huc, huH, map_zero, add_zero]
    have h2 : u (f h * g) = τ (f h) (u g) := by rw [huc, huH, zero_add]
    have hgm : g * f h' = f h * g := by rw [hh']; group
    rw [← h2, ← hgm, h1]
  rw [HeckeEis.coeffH1Mk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff]
  refine ⟨v, ?_⟩
  ext g
  have := hu0 g
  simp only [hu, sub_eq_zero] at this
  exact this.symm

theorem resH1_injective (hqN : ¬ q ∣ N)
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0) :
    Function.Injective (resH1 (ρ.comp (red N q)) (incl N)) := by
  intro x y hxy
  simp only [resH1, LinearMap.comp_apply, LinearEquiv.coe_coe] at hxy
  have h1 := (H1Equiv ((ρ.comp (red N q)).comp (incl N))).injective hxy
  have h2 := coeffRes_injective_of_conj (ρ.comp (red N q)) (incl N) (fun g h =>
    ⟨⟨(g : SL(2, ℤ)) * (h : SL(2, ℤ)) * (g : SL(2, ℤ))⁻¹, CohCarrier.conj_mem_GammaH N ⊥ g h⟩, rfl⟩)
    (fun w hw => eq_zero_of_forall_gammaH N q ρ hqN hV w hw) h1
  exact (H1Equiv (ρ.comp (red N q))).symm.injective h2

end Setup
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

end D1Chi
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

set_option autoImplicit false

open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

namespace D1Chi

section Main

variable (N q : ℕ) [NeZero N] [Fact q.Prime]
variable {κ : Type} [Field κ] {V : Type} [AddCommGroup V] [Module κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)

theorem inclusion_mem_heckeUpper_iff (ℓ : ℕ) [NeZero ℓ] (x : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :
    x ∈ CohCarrier.GammaHUpper N ⊥ ℓ ↔ incl N x ∈ HeckeEis.heckeUpper N ℓ := by
  rw [HeckeEis.mem_heckeUpper, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

theorem inclusion_conjL (ℓ : ℕ) [NeZero ℓ] (s : ↥(CohCarrier.GammaHUpper N ⊥ ℓ)) :
    incl N (CohCarrier.conjL N ⊥ ℓ s) =
      HeckeEis.heckeConj N ℓ ⟨incl N (s : ↥(CohCarrier.GammaH N ⊥)), (inclusion_mem_heckeUpper_iff N ℓ _).mp s.2⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem betaQ_surjective (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Surjective (betaQ (K := HeckeEis.heckeUpper N ℓ) (K' := CohCarrier.GammaHUpper N ⊥ ℓ) (incl N)
      (fun x => inclusion_mem_heckeUpper_iff N ℓ x)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro Q
  induction Q using Quotient.inductionOn' with
  | h g =>

    obtain ⟨y, hy⟩ := exists_gammaH_bot_map_eq N ℓ hℓN
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) ((g : SL(2, ℤ)))⁻¹)
    refine ⟨Quotient.mk'' y⁻¹, ?_⟩
    rw [betaQ_mk]
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply, map_inv, inv_inv, HeckeEis.mem_heckeUpper]

    have hgy : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) ((g : SL(2, ℤ)) * (y : SL(2, ℤ))) = 1 := by
      rw [map_mul, hy, map_inv, mul_inv_cancel]
    have h01 := congrArg (fun A : SL(2, ZMod ℓ) => A 0 1) hgy
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast] at h01
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    convert h01 using 1 <;> first | rfl | simp

theorem betaQ_injective (ℓ : ℕ) [NeZero ℓ] :
    Function.Injective (betaQ (K := HeckeEis.heckeUpper N ℓ) (K' := CohCarrier.GammaHUpper N ⊥ ℓ) (incl N)
      (fun x => inclusion_mem_heckeUpper_iff N ℓ x)) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn' with
  | h x₁ =>
    induction q₂ using Quotient.inductionOn' with
    | h x₂ =>
      rw [betaQ_mk, betaQ_mk] at h
      apply Quotient.sound'
      have h' : QuotientGroup.rightRel (HeckeEis.heckeUpper N ℓ) (incl N x₁) (incl N x₂) := Quotient.exact' h
      rw [QuotientGroup.rightRel_apply] at h' ⊢
      rw [inclusion_mem_heckeUpper_iff, map_mul, map_inv]
      exact h'

theorem isTwist_adj₀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ((ℓ : ZMod q) ≠ 0)) (s : ↥(HeckeEis.heckeUpper N ℓ)) (v : V) :
    adj q ρ ℓ (ρ (red N q (HeckeEis.heckeConj N ℓ s)) v) = ρ (red N q (s : ↥(Gamma0 N))) (adj q ρ ℓ v) := by
  set D : CuspidalType.GL2 q := CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) hℓ) with hD
  have hint : !![(ℓ : ℤ), 0; 0, 1] * (((HeckeEis.heckeConj N ℓ s : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((s : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by
    have h01 : (ℓ : ℤ) * ((((s : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1) / (ℓ : ℤ)) = ((s : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 :=
      Int.mul_ediv_cancel' ((HeckeEis.mem_heckeUpper N ℓ).mp s.2)
    rw [HeckeEis.coe_heckeConj]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HeckeEis.heckeConjMat, Matrix.mul_apply, Fin.sum_univ_two, h01, mul_comm]
  have key : D * red N q (HeckeEis.heckeConj N ℓ s) = red N q (s : ↥(Gamma0 N)) * D := by
    apply Units.ext
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom (ZMod q))) hint
    rw [Matrix.map_mul, Matrix.map_mul] at this
    have hDm : ((D : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        (!![(ℓ : ℤ), 0; 0, 1]).map (Int.castRingHom (ZMod q)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hD, CuspidalType.diagElem]
    have h1 : ∀ x : ↥(Gamma0 N), ((red N q x : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod q)) := fun x => rfl
    rw [Units.val_mul, Units.val_mul, hDm, h1, h1]
    exact this
  simp only [adj, dif_pos hℓ]
  rw [← Module.End.mul_apply, ← map_mul, key, map_mul, Module.End.mul_apply]

theorem key (ℓ : ℕ) [NeZero ℓ] (hℓp : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ : ((ℓ : ZMod q) ≠ 0))
    (z w : HeckeEis.coeffCocycles (ρ.comp (red N q)))
    (hw : (w : ↥(Gamma0 N) → V) = HeckeEis.coeffHeckeFun N ℓ (ρ.comp (red N q)) (adj q ρ ℓ) z) :
    H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
        (HeckeCohomology.heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
          (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ ℓ) (isTwist_adj N q ρ ℓ hℓ)
          (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) z))) =
      H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
        (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) w)) := by

  let Γ₁ := ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))
  let K := HeckeEis.heckeUpper N ℓ
  let K' := CohCarrier.GammaHUpper N ⊥ ℓ
  let ρ₀ := ρ.comp (red N q)
  have hK : ∀ x : Γ₁, x ∈ K' ↔ incl N x ∈ K := fun x => inclusion_mem_heckeUpper_iff N ℓ x
  let β : RQ K' ≃ RQ K := Equiv.ofBijective (betaQ (incl N) hK) ⟨betaQ_injective N ℓ, betaQ_surjective N ℓ hℓp hℓN⟩
  have hβ : ∀ q, β q = betaQ (incl N) hK q := fun q => rfl

  have hC : ∀ g : ↥(Gamma0 N), (w : ↥(Gamma0 N) → V) g = TR ρ₀ (HeckeEis.heckeConj N ℓ) (adj q ρ ℓ) (invOut K) z g := by
    intro g; rw [hw]; exact coeffHeckeFun_eq_TR N ℓ ρ₀ (adj q ρ ℓ) z g
  have hD : ∀ γ : Γ₁,
      (HeckeCohomology.heckeZ1 ⊤ K' (HeckeCohomology.cTop N ⊥ ℓ) (Rep.of (ρ₀.comp (incl N))) (adj q ρ ℓ)
          (isTwist_adj N q ρ ℓ hℓ) (resCocycles ρ₀ (incl N) (cocyclesEquiv ρ₀ z)) : Γ₁ → V) γ =
        TR ρ₀ (HeckeEis.heckeConj N ℓ) (adj q ρ ℓ) (Transversal.push (incl N) hK β hβ (Transversal.out K')) z (incl N γ) := by
    intro γ
    have e1 := heckeZ1_eq_TR (ρ₀.comp (incl N)) (CohCarrier.conjL N ⊥ ℓ) (adj q ρ ℓ) (isTwist_adj N q ρ ℓ hℓ)
      (resCocycles ρ₀ (incl N) (cocyclesEquiv ρ₀ z)) γ
    refine e1.trans ?_
    rw [TR_push ρ₀ (adj q ρ ℓ) (HeckeEis.heckeConj N ℓ) (CohCarrier.conjL N ⊥ ℓ) (incl N) hK β hβ
      (fun s' => inclusion_conjL N ℓ s') (Transversal.out K') z γ]
    rfl

  obtain ⟨b, hb⟩ := TR_sub_TR (ρ := ρ₀) (φ := HeckeEis.heckeConj N ℓ) (a := adj q ρ ℓ) (K := K)
    (fun s' v => isTwist_adj₀ N q ρ ℓ hℓ s' v) z (fun x y => z.2 x y) (invOut K) (Transversal.push (incl N) hK β hβ (Transversal.out K'))

  rw [H1π_eq_iff]
  refine ⟨-b, funext fun γ => ?_⟩
  show (Rep.of (ρ₀.comp (incl N))).ρ γ (-b) - (-b) =
    (HeckeCohomology.heckeZ1 ⊤ K' (HeckeCohomology.cTop N ⊥ ℓ) (Rep.of (ρ₀.comp (incl N))) (adj q ρ ℓ)
          (isTwist_adj N q ρ ℓ hℓ) (resCocycles ρ₀ (incl N) (cocyclesEquiv ρ₀ z)) : Γ₁ → V) γ -
      (w : ↥(Gamma0 N) → V) (incl N γ)
  rw [Rep.of_ρ, hD, hC, hb, map_neg, MonoidHom.comp_apply]
  abel

theorem main (hqN : ¬ q ∣ N) (S₀ : Set ℕ) [FiniteDimensional κ V]
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp (red N q)) (fun ℓ : ℕ => adj q ρ ℓ) (insert q S₀) lam) :
    ∃ hφ : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
        HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
          (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ i.1),
      ∃ y : groupCohomology.H1 (Rep.of ((ρ.comp (red N q)).comp (incl N))),
        y ≠ 0 ∧
        ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
          haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
          HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
            (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ i.1) (hφ i) y = lam i.1 • y := by

  have hι : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀}, ((i.1 : ℕ) : ZMod q) ≠ 0 := by
    intro i h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hq : q.Prime := Fact.out
    have : i.1 = q := ((Nat.prime_dvd_prime_iff_eq hq i.2.1).mp h).symm
    apply i.2.2.2
    rw [this]
    exact Set.mem_insert q S₀
  refine ⟨fun i => isTwist_adj N q ρ i.1 (hι i), ?_⟩
  obtain ⟨x, hx, hT⟩ := hocc
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective (ρ.comp (red N q)) x
  refine ⟨resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)), ?_, ?_⟩
  · intro h
    apply hx
    have h' : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) =
        resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) 0) := by rw [h, map_zero, map_zero]
    exact (H1Equiv (ρ.comp (red N q))).injective (resH1_injective N q ρ hqN hV h')
  · intro i
    haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
    obtain ⟨T, hTdef, hTx⟩ := hT i.1 i.2.1 i.2.2.1 i.2.2.2
    obtain ⟨w, hw, hTz⟩ := hTdef z

    have hwz : HeckeEis.coeffH1Mk (ρ.comp (red N q)) w = lam i.1 • HeckeEis.coeffH1Mk (ρ.comp (red N q)) z := by
      rw [← hTz, hTx]

    have step1 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) =
        H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
          (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) z)) := by
      rw [H1Equiv_coeffH1Mk, resH1_H1π]
    have step2 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) w)) =
        H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
          (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) w)) := by
      rw [H1Equiv_coeffH1Mk, resH1_H1π]
    have step3 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) w)) =
        lam i.1 • resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) := by
      rw [hwz, map_smul, map_smul]
    have hk := key N q ρ i.1 i.2.1 i.2.2.1 (hι i) z w hw
    show HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
        (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ i.1) (isTwist_adj N q ρ i.1 (hι i))
        (resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z))) = _
    rw [step1, HeckeCohomology.heckeH1_H1π]
    refine hk.trans ?_
    rw [← step1]
    exact step2.symm.trans step3

end Main
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

end D1Chi
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

set_option autoImplicit false

open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

namespace D1Chi

section Diamond

variable (N q : ℕ) [NeZero N] [Fact q.Prime]
variable {κ : Type} [Field κ] {V : Type} [AddCommGroup V] [Module κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)

theorem map_conjHom_res (σ : ↥(Gamma0 N))
    (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) (Rep.of ((ρ.comp (red N q)).comp (incl N))) ⟶
      Rep.of ((ρ.comp (red N q)).comp (incl N)))
    (hc : ∀ v : V, c.hom v = ρ (red N q σ)⁻¹ v)
    (z : HeckeEis.coeffCocycles (ρ.comp (red N q))) :
    groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) c 1
        (H1π (Rep.of ((ρ.comp (red N q)).comp (incl N))) (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) z))) =
      H1π (Rep.of ((ρ.comp (red N q)).comp (incl N))) (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) z)) := by
  rw [H1π_comp_map_apply, H1π_eq_iff]

  have hz : ∀ x y : ↥(Gamma0 N), (z : ↥(Gamma0 N) → V) (x * y) = (z : _ → V) x + (ρ.comp (red N q)) x ((z : _ → V) y) :=
    fun x y => z.2 x y
  have hz1 : (z : ↥(Gamma0 N) → V) 1 = 0 := by have := hz 1 1; simp at this; exact this
  have hzinv : ∀ x : ↥(Gamma0 N), (z : ↥(Gamma0 N) → V) x⁻¹ = - (ρ.comp (red N q)) x⁻¹ ((z : _ → V) x) := fun x => by
    have := hz x⁻¹ x
    rw [inv_mul_cancel, hz1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  set v : V := (ρ.comp (red N q)) σ⁻¹ ((z : ↥(Gamma0 N) → V) σ) with hv
  refine ⟨-v, funext fun γ => ?_⟩
  have hincl : incl N (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ γ) = σ * incl N γ * σ⁻¹ := rfl
  have hred : ((red N q) σ)⁻¹ = red N q σ⁻¹ := (map_inv (red N q) σ).symm
  have hc' : ∀ w : V, c.hom w = (ρ.comp (red N q)) σ⁻¹ w := fun w => by
    rw [hc, hred]
    rfl
  show (Rep.of ((ρ.comp (red N q)).comp (incl N))).ρ γ (-v) - (-v) =
    c.hom ((z : ↥(Gamma0 N) → V) (incl N (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ γ))) - (z : ↥(Gamma0 N) → V) (incl N γ)
  rw [hc', hincl, hz, hz, hzinv, Rep.of_ρ]
  simp only [map_add, map_neg, rho_rho, inv_mul_cancel, map_one, Module.End.one_apply]
  have : σ⁻¹ * (σ * incl N γ * σ⁻¹) = incl N γ * σ⁻¹ := by group
  rw [this, ← rho_rho, ← hv]
  show -((ρ.comp (red N q)) (incl N γ) v) - -v =
    v + (z : ↥(Gamma0 N) → V) (incl N γ) + -((ρ.comp (red N q)) (incl N γ) v) - (z : ↥(Gamma0 N) → V) (incl N γ)
  abel

theorem eigen_branch (ℓ : ℕ) [NeZero ℓ] (hℓp : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ : ((ℓ : ZMod q) ≠ 0)) (lamℓ : κ)
    (z w : HeckeEis.coeffCocycles (ρ.comp (red N q)))
    (hw : (w : ↥(Gamma0 N) → V) = HeckeEis.coeffHeckeFun N ℓ (ρ.comp (red N q)) (adj q ρ ℓ) z)
    (hwz : HeckeEis.coeffH1Mk (ρ.comp (red N q)) w = lamℓ • HeckeEis.coeffH1Mk (ρ.comp (red N q)) z) :
    HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
        (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ ℓ) (isTwist_adj N q ρ ℓ hℓ)
        (resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z))) =
      lamℓ • resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) := by
  have step1 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) =
      H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
        (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) z)) := by
    rw [H1Equiv_coeffH1Mk, resH1_H1π]
  have step2 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) w)) =
      H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
        (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) w)) := by
    rw [H1Equiv_coeffH1Mk, resH1_H1π]
  have step3 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) w)) =
      lamℓ • resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) := by
    rw [hwz, map_smul, map_smul]
  have hk := key N q ρ ℓ hℓp hℓN hℓ z w hw
  rw [step1, HeckeCohomology.heckeH1_H1π]
  refine hk.trans ?_
  rw [← step1]
  exact step2.symm.trans step3

theorem main2 (hqN : ¬ q ∣ N) (S₀ : Set ℕ) [FiniteDimensional κ V]
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp (red N q)) (fun ℓ : ℕ => adj q ρ ℓ) (insert q S₀) lam) :
    ∃ hφ : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
        HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
          (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ i.1),
      ∃ y : groupCohomology.H1 (Rep.of ((ρ.comp (red N q)).comp (incl N))),
        y ≠ 0 ∧
        (∀ (σ : ↥(Gamma0 N))
            (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) (Rep.of ((ρ.comp (red N q)).comp (incl N))) ⟶
              Rep.of ((ρ.comp (red N q)).comp (incl N))),
            (∀ v : V, c.hom v = ρ (red N q σ)⁻¹ v) →
            groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) c 1 y = y) ∧
        ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
          haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
          HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
            (Rep.of ((ρ.comp (red N q)).comp (incl N))) (adj q ρ i.1) (hφ i) y = lam i.1 • y := by

  have hι : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀}, ((i.1 : ℕ) : ZMod q) ≠ 0 := by
    intro i h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hq : q.Prime := Fact.out
    have : i.1 = q := ((Nat.prime_dvd_prime_iff_eq hq i.2.1).mp h).symm
    apply i.2.2.2
    rw [this]
    exact Set.mem_insert q S₀
  refine ⟨fun i => isTwist_adj N q ρ i.1 (hι i), ?_⟩
  obtain ⟨x, hx, hT⟩ := hocc
  obtain ⟨z, rfl⟩ := HeckeEis.coeffH1Mk_surjective (ρ.comp (red N q)) x
  refine ⟨resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)), ?_, ?_, ?_⟩
  · intro h
    apply hx
    have h' : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) =
        resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) 0) := by rw [h, map_zero, map_zero]
    exact (H1Equiv (ρ.comp (red N q))).injective (resH1_injective N q ρ hqN hV h')
  · intro σ c hc
    have step0 : resH1 (ρ.comp (red N q)) (incl N) (H1Equiv (ρ.comp (red N q)) (HeckeEis.coeffH1Mk (ρ.comp (red N q)) z)) =
        H1π (Rep.of ((ρ.comp (red N q)).comp (incl N)))
          (resCocycles (ρ.comp (red N q)) (incl N) (cocyclesEquiv (ρ.comp (red N q)) z)) := by
      rw [H1Equiv_coeffH1Mk, resH1_H1π]
    rw [step0]
    exact map_conjHom_res N q ρ σ c hc z
  · intro i
    haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
    obtain ⟨T, hTdef, hTx⟩ := hT i.1 i.2.1 i.2.2.1 i.2.2.2
    obtain ⟨w, hw, hTz⟩ := hTdef z
    have hwz : HeckeEis.coeffH1Mk (ρ.comp (red N q)) w = lam i.1 • HeckeEis.coeffH1Mk (ρ.comp (red N q)) z := by
      rw [← hTz, hTx]
    exact eigen_branch N q ρ i.1 i.2.1 i.2.2.1 (hι i) (lam i.1) z w hw hwz

end Diamond
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

end D1Chi
p2m_reactivate "P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.D1Chi.Transversal"

theorem solution
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (κ : Type) [Field κ]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    ∃ hφ : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
        HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
          (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))
          (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h))
            else LinearMap.id),
      ∃ y : groupCohomology.H1
          (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))))),
        y ≠ 0 ∧
        (∀ (σ : ↥(Gamma0 N))
            (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ)
              (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))))) ⟶
              (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))),
            (∀ v : V, c.hom v = ρ (((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) σ)⁻¹ v) →
            groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) c 1 y = y) ∧
        ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
          haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
          HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
            (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))
            (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h))
            else LinearMap.id)
            (hφ i) y = lam i.1 • y :=
  D1Chi.main2 N q ρ hqN S₀ hV lam hocc

end S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
end P2MW
export P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1 (solution)
