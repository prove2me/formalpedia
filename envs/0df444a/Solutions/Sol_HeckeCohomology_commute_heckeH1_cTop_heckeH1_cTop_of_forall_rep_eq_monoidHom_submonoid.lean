-- Prove2me | solution 1 for HeckeCohomology.commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/92ff81cc-792b-53ff-a4c9-131b443c6001

import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Theorems.Thm_HeckeCohomology_heckeH1_eq_of_section
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid

set_option autoImplicit false

open groupCohomology HeckeCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace MackeyH1

variable {k Γ : Type} [CommRing k] [Group Γ] (A : Rep k Γ)
variable (K K' : Subgroup Γ) [K.FiniteIndex] [K'.FiniteIndex]
variable (c : K →* (⊤ : Subgroup Γ)) (c' : K' →* (⊤ : Subgroup Γ))
variable (φ φ' : A →ₗ[k] A)

def Kpp : Subgroup Γ := (K'.comap ((⊤ : Subgroup Γ).subtype.comp c)).map K.subtype

theorem mem_Kpp_iff {x : Γ} : x ∈ Kpp K K' c ↔ ∃ hx : x ∈ K, ((c ⟨x, hx⟩ : (⊤ : Subgroup Γ)) : Γ) ∈ K' := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, by simpa using hs⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, by simpa using h, rfl⟩

theorem Kpp_le : Kpp K K' c ≤ K := by
  rintro _ ⟨s, _, rfl⟩; exact s.2

noncomputable def cRes : ↥(Kpp K K' c) →* K' :=
  ((((⊤ : Subgroup Γ).subtype.comp c).comp (Subgroup.inclusion (Kpp_le K K' c))).codRestrict K'
    fun s => ((mem_Kpp_iff K K' c).mp s.2).2)

theorem coe_cRes (s : ↥(Kpp K K' c)) :
    ((cRes K K' c s : K') : Γ) = ((c ⟨(s : Γ), Kpp_le K K' c s.2⟩ : (⊤ : Subgroup Γ)) : Γ) := rfl

noncomputable def cpp : ↥(Kpp K K' c) →* (⊤ : Subgroup Γ) := c'.comp (cRes K K' c)

theorem coe_cpp (s : ↥(Kpp K K' c)) :
    ((cpp K K' c c' s : (⊤ : Subgroup Γ)) : Γ) = ((c' (cRes K K' c s) : (⊤ : Subgroup Γ)) : Γ) := rfl

end MackeyH1

namespace MackeyH1

variable {k Γ : Type} [CommRing k] [Group Γ] (A : Rep k Γ)
variable (K K' : Subgroup Γ) [K.FiniteIndex] [K'.FiniteIndex]
variable (c : K →* (⊤ : Subgroup Γ)) (c' : K' →* (⊤ : Subgroup Γ))

theorem isTwist_comp (φ φ' : A →ₗ[k] A) (hφ : IsTwist ⊤ K c A φ) (hφ' : IsTwist ⊤ K' c' A φ') :
    IsTwist ⊤ (Kpp K K' c) (cpp K K' c c') A (φ ∘ₗ φ') := by
  intro s a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coe_cpp, hφ' (cRes K K' c s) a, coe_cRes]
  exact hφ ⟨(s : Γ), Kpp_le K K' c s.2⟩ (φ' a)

variable (r : Quotient (QuotientGroup.rightRel K) → Γ) (hr : ∀ q, cls K (r q) = q)
variable (s : Quotient (QuotientGroup.rightRel K') → K) (hs : ∀ q', cls K' ((c (s q') : (⊤ : Subgroup Γ)) : Γ) = q')

def R (p : Quotient (QuotientGroup.rightRel K) × Quotient (QuotientGroup.rightRel K')) : Γ := (s p.2 : Γ) * r p.1

def e (p : Quotient (QuotientGroup.rightRel K) × Quotient (QuotientGroup.rightRel K')) :
    Quotient (QuotientGroup.rightRel (Kpp K K' c)) :=
  cls (Kpp K K' c) (R K K' r s p)

theorem rel_of_cls_eq (S : Subgroup Γ) {x y : Γ} (h : cls S x = cls S y) : y * x⁻¹ ∈ S := by
  have := Quotient.exact' h
  rwa [QuotientGroup.rightRel_apply] at this

theorem cls_eq_of_rel (S : Subgroup Γ) {x y : Γ} (h : y * x⁻¹ ∈ S) : cls S x = cls S y :=
  Quotient.sound' (by rwa [QuotientGroup.rightRel_apply])

include hr in

theorem mul_r_inv_mem (x : Γ) : x * (r (cls K x))⁻¹ ∈ K :=
  rel_of_cls_eq K (hr (cls K x))

include hs in

theorem mul_cs_inv_mem (y : Γ) : y * (((c (s (cls K' y)) : (⊤ : Subgroup Γ)) : Γ))⁻¹ ∈ K' :=
  rel_of_cls_eq K' (hs (cls K' y))

include hr hs in
theorem e_injective : Function.Injective (e K K' c r s) := by
  rintro ⟨q₁, q₁'⟩ ⟨q₂, q₂'⟩ h
  have h1 : (s q₂' : Γ) * r q₂ * ((s q₁' : Γ) * r q₁)⁻¹ ∈ Kpp K K' c := rel_of_cls_eq _ h

  have hK : r q₂ * (r q₁)⁻¹ ∈ K := by
    have h2 : (s q₂' : Γ)⁻¹ * ((s q₂' : Γ) * r q₂ * ((s q₁' : Γ) * r q₁)⁻¹) * (s q₁' : Γ) ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem (s q₂').2) (Kpp_le K K' c h1)) (s q₁').2
    convert h2 using 1
    group
  have hq : q₁ = q₂ := by rw [← hr q₁, ← hr q₂]; exact cls_eq_of_rel K hK
  subst hq

  have h3 : (s q₂' : Γ) * (s q₁' : Γ)⁻¹ ∈ Kpp K K' c := by
    convert h1 using 1
    group
  obtain ⟨hx, h4⟩ := (mem_Kpp_iff K K' c).mp h3
  have h5 : ((c (s q₂') : (⊤ : Subgroup Γ)) : Γ) * (((c (s q₁') : (⊤ : Subgroup Γ)) : Γ))⁻¹ ∈ K' := by
    have : (⟨(s q₂' : Γ) * (s q₁' : Γ)⁻¹, hx⟩ : K) = s q₂' * (s q₁')⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h4
    exact h4
  have hq' : q₁' = q₂' := by rw [← hs q₁', ← hs q₂']; exact cls_eq_of_rel K' h5
  rw [hq']

include hr hs in
theorem e_surjective : Function.Surjective (e K K' c r s) := by
  intro q''
  induction q'' using Quotient.inductionOn' with
  | h x =>
    set q := cls K x with hq
    let kx : K := ⟨x * (r q)⁻¹, mul_r_inv_mem K r hr x⟩
    set y : Γ := ((c kx : (⊤ : Subgroup Γ)) : Γ) with hy
    set q' := cls K' y with hq'
    refine ⟨(q, q'), ?_⟩
    show cls (Kpp K K' c) ((s q' : Γ) * r q) = cls (Kpp K K' c) x
    apply cls_eq_of_rel

    have hmem : (kx : Γ) * (s q' : Γ)⁻¹ ∈ Kpp K K' c := by
      rw [mem_Kpp_iff]
      refine ⟨K.mul_mem kx.2 (K.inv_mem (s q').2), ?_⟩
      have : (⟨(kx : Γ) * (s q' : Γ)⁻¹, K.mul_mem kx.2 (K.inv_mem (s q').2)⟩ : K) = kx * (s q')⁻¹ := Subtype.ext rfl
      rw [this, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, ← hy]
      exact mul_cs_inv_mem K K' c s hs y
    convert hmem using 1
    show x * ((s q' : Γ) * r q)⁻¹ = x * (r q)⁻¹ * (s q' : Γ)⁻¹
    group

include hr hs in

theorem finiteIndex_Kpp : (Kpp K K' c).FiniteIndex := by
  haveI : Finite (Quotient (QuotientGroup.rightRel (Kpp K K' c))) :=
    Finite.of_surjective _ (e_surjective K K' c r hr s hs)
  haveI : Finite (Γ ⧸ Kpp K K' c) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Kpp K K' c))
  exact Subgroup.finiteIndex_of_finite_quotient

end MackeyH1

namespace MackeyH1

variable {k Γ : Type} [CommRing k] [Group Γ] (A : Rep k Γ)

section AnySection
variable (S : Subgroup Γ) [S.FiniteIndex] (c : S →* (⊤ : Subgroup Γ)) (φ : A →ₗ[k] A)
variable (r : Quotient (QuotientGroup.rightRel S) → Γ) (hr : ∀ q, cls S (r q) = q)

include hr in
theorem sec_mem (q : Quotient (QuotientGroup.rightRel S)) (γ : Γ) : r q * γ * (r (cls S (r q * γ)))⁻¹ ∈ S := by
  have := rel_of_cls_eq S (hr (cls S (r q * γ)))
  simpa [mul_assoc] using this

def sec (q : Quotient (QuotientGroup.rightRel S)) (γ : Γ) : S := ⟨r q * γ * (r (cls S (r q * γ)))⁻¹, sec_mem S r hr q γ⟩

theorem coe_sec (q : Quotient (QuotientGroup.rightRel S)) (γ : Γ) : (sec S r hr q γ : Γ) = r q * γ * (r (cls S (r q * γ)))⁻¹ := rfl

include hr in

theorem cls_r_mul (q : Quotient (QuotientGroup.rightRel S)) (γ : Γ) : cls S (r q * γ) = mulRight S γ q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  show cls S (r (cls S x) * γ) = mulRight S γ (cls S x)
  rw [mulRight_apply, cls_rep_mul]
  apply cls_eq_of_rel
  have h := rel_of_cls_eq S (hr (cls S x))
  have : x * γ * (r (cls S x) * γ)⁻¹ = x * (r (cls S x))⁻¹ := by group
  rw [this]; exact h

include hr in
theorem mulRight_mulRight (q : Quotient (QuotientGroup.rightRel S)) (γ δ : Γ) :
    mulRight S δ (mulRight S γ q) = mulRight S (γ * δ) q := by
  rw [← cls_r_mul S r hr q γ, ← cls_r_mul S r hr q (γ * δ), mulRight_apply, cls_rep_mul, mul_assoc]

theorem sec_mul (q : Quotient (QuotientGroup.rightRel S)) (γ δ : Γ) :
    sec S r hr q (γ * δ) = sec S r hr q γ * sec S r hr (mulRight S γ q) δ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_sec, coe_sec, coe_sec]
  have e1 : cls S (r q * γ) = mulRight S γ q := cls_r_mul S r hr q γ
  have e2 : cls S (r (mulRight S γ q) * δ) = cls S (r q * (γ * δ)) := by
    rw [cls_r_mul S r hr, cls_r_mul S r hr, mulRight_mulRight S r hr]
  rw [e1, e2]
  group

noncomputable def trFun (f : Γ → A) (γ : Γ) : A :=
  ∑ q : Quotient (QuotientGroup.rightRel S), A.ρ (r q)⁻¹ (φ (f (c (sec S r hr q γ) : Γ)))

theorem trFun_mem_cocycles₁ (hφ : IsTwist ⊤ S c A φ) (f : cocycles₁ A) : trFun A S c φ r hr f ∈ cocycles₁ A := by
  rw [mem_cocycles₁_iff]
  intro γ δ
  simp only [trFun]
  have key : ∀ q : Quotient (QuotientGroup.rightRel S),
      A.ρ (r q)⁻¹ (φ (f (c (sec S r hr q (γ * δ)) : Γ))) =
        A.ρ γ (A.ρ (r (mulRight S γ q))⁻¹ (φ (f (c (sec S r hr (mulRight S γ q) δ) : Γ)))) +
          A.ρ (r q)⁻¹ (φ (f (c (sec S r hr q γ) : Γ))) := fun q => by
    rw [sec_mul, map_mul, Subgroup.coe_mul, (mem_cocycles₁_iff f).1 f.2, map_add, map_add, hφ]
    congr 1

    show A.ρ (r q)⁻¹ (A.ρ (sec S r hr q γ : Γ) _) = A.ρ γ (A.ρ (r (mulRight S γ q))⁻¹ _)
    rw [← Module.End.mul_apply (A.ρ _) (A.ρ _), ← map_mul, ← Module.End.mul_apply (A.ρ γ) (A.ρ _), ← map_mul]
    congr 2
    rw [coe_sec, cls_r_mul S r hr]
    group
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, map_sum]
  congr 1
  exact Fintype.sum_equiv (mulRight S γ) _ _ fun _ => rfl

noncomputable def trZ (hφ : IsTwist ⊤ S c A φ) (f : cocycles₁ A) : cocycles₁ A :=
  ⟨trFun A S c φ r hr f, trFun_mem_cocycles₁ A S c φ r hr hφ f⟩

theorem trZ_apply (hφ : IsTwist ⊤ S c A φ) (f : cocycles₁ A) (γ : Γ) :
    trZ A S c φ r hr hφ f γ = ∑ q : Quotient (QuotientGroup.rightRel S), A.ρ (r q)⁻¹ (φ (f (c (sec S r hr q γ) : Γ))) := rfl

theorem heckeH1_eq_trZ (hφ : IsTwist ⊤ S c A φ) (f : cocycles₁ A) :
    heckeH1 ⊤ S c A φ hφ (H1π A f) = H1π A (trZ A S c φ r hr hφ f) :=
  (HeckeCohomology.heckeH1_eq_of_section ⊤ S c A φ hφ r (sec S r hr) (fun _ _ => rfl) f _ (fun _ => rfl)).symm

end AnySection

end MackeyH1

namespace MackeyH1

variable {k Γ : Type} [CommRing k] [Group Γ] (A : Rep k Γ)
variable (K K' : Subgroup Γ) [K.FiniteIndex] [K'.FiniteIndex]
variable (c : K →* (⊤ : Subgroup Γ)) (c' : K' →* (⊤ : Subgroup Γ))
variable (r : Quotient (QuotientGroup.rightRel K) → Γ) (hr : ∀ q, cls K (r q) = q)
variable (s : Quotient (QuotientGroup.rightRel K') → K) (hs : ∀ q', cls K' ((c (s q') : (⊤ : Subgroup Γ)) : Γ) = q')

noncomputable def E : Quotient (QuotientGroup.rightRel K) × Quotient (QuotientGroup.rightRel K') ≃
    Quotient (QuotientGroup.rightRel (Kpp K K' c)) :=
  Equiv.ofBijective (e K K' c r s) ⟨e_injective K K' c r hr s hs, e_surjective K K' c r hr s hs⟩

theorem E_apply (p : Quotient (QuotientGroup.rightRel K) × Quotient (QuotientGroup.rightRel K')) :
    E K K' c r hr s hs p = cls (Kpp K K' c) (R K K' r s p) := rfl

noncomputable def rpp (q'' : Quotient (QuotientGroup.rightRel (Kpp K K' c))) : Γ := R K K' r s ((E K K' c r hr s hs).symm q'')

theorem hrpp (q'' : Quotient (QuotientGroup.rightRel (Kpp K K' c))) : cls (Kpp K K' c) (rpp K K' c r hr s hs q'') = q'' := by
  rw [rpp, ← E_apply K K' c r hr s hs, Equiv.apply_symm_apply]

theorem rpp_E (p : Quotient (QuotientGroup.rightRel K) × Quotient (QuotientGroup.rightRel K')) :
    rpp K K' c r hr s hs (E K K' c r hr s hs p) = R K K' r s p := by
  rw [rpp, Equiv.symm_apply_apply]

include hr hs in

theorem mackey (φ φ' : A →ₗ[k] A) (hφ : IsTwist ⊤ K c A φ) (hφ' : IsTwist ⊤ K' c' A φ')
    [hfi : (Kpp K K' c).FiniteIndex] :
    heckeH1 ⊤ K c A φ hφ ∘ₗ heckeH1 ⊤ K' c' A φ' hφ' =
      heckeH1 ⊤ (Kpp K K' c) (cpp K K' c c') A (φ ∘ₗ φ') (isTwist_comp A K K' c c' φ φ' hφ hφ') := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := H1π_surjective A x
  rw [LinearMap.comp_apply]

  set r' : Quotient (QuotientGroup.rightRel K') → Γ := fun q' => ((c (s q') : (⊤ : Subgroup Γ)) : Γ) with hr'def
  have hr' : ∀ q', cls K' (r' q') = q' := hs
  rw [heckeH1_eq_trZ A K' c' φ' r' hr' hφ' f, heckeH1_eq_trZ A K c φ r hr hφ _,
    heckeH1_eq_trZ A (Kpp K K' c) (cpp K K' c c') (φ ∘ₗ φ') (rpp K K' c r hr s hs) (hrpp K K' c r hr s hs)
      (isTwist_comp A K K' c c' φ φ' hφ hφ') f]
  congr 1
  apply Subtype.ext
  funext γ
  show trFun A K c φ r hr (trZ A K' c' φ' r' hr' hφ' f) γ =
    trFun A (Kpp K K' c) (cpp K K' c c') (φ ∘ₗ φ') (rpp K K' c r hr s hs) (hrpp K K' c r hr s hs) f γ
  simp only [trFun]

  have inner : ∀ q : Quotient (QuotientGroup.rightRel K),
      A.ρ (r q)⁻¹ (φ ((trZ A K' c' φ' r' hr' hφ' f) (c (sec K r hr q γ) : Γ))) =
        ∑ q' : Quotient (QuotientGroup.rightRel K'),
          A.ρ (R K K' r s (q, q'))⁻¹ (φ (φ' (f (c' (sec K' r' hr' q' ((c (sec K r hr q γ) : Γ))) : Γ)))) := by
    intro q
    rw [trZ_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_

    have htw : φ (A.ρ (r' q')⁻¹ (φ' (f (c' (sec K' r' hr' q' ((c (sec K r hr q γ) : Γ))) : Γ)))) =
        A.ρ ((s q' : Γ))⁻¹ (φ (φ' (f (c' (sec K' r' hr' q' ((c (sec K r hr q γ) : Γ))) : Γ)))) := by
      have : (r' q')⁻¹ = ((c (s q')⁻¹ : (⊤ : Subgroup Γ)) : Γ) := by
        rw [map_inv, Subgroup.coe_inv]
      rw [this, hφ]
      rfl
    rw [htw, ← Module.End.mul_apply, ← map_mul]
    congr 2
    show (r q)⁻¹ * (s q' : Γ)⁻¹ = ((s q' : Γ) * r q)⁻¹
    rw [mul_inv_rev]
  rw [Finset.sum_congr rfl fun q _ => inner q, ← Finset.sum_product', Finset.univ_product_univ]

  refine Fintype.sum_equiv (E K K' c r hr s hs) _ _ fun p => ?_
  obtain ⟨q, q'⟩ := p
  rw [rpp_E]
  simp only [LinearMap.comp_apply]

  set y : Γ := ((c (sec K r hr q γ) : (⊤ : Subgroup Γ)) : Γ) with hy
  set q₁ : Quotient (QuotientGroup.rightRel K) := cls K (r q * γ) with hq₁
  set q₁' : Quotient (QuotientGroup.rightRel K') := cls K' (r' q' * y) with hq₁'

  have hKmem : (s q' : Γ) * (sec K r hr q γ : Γ) * (s q₁' : Γ)⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (s q').2 (sec K r hr q γ).2) (K.inv_mem (s q₁').2)
  have hKelt : (⟨(s q' : Γ) * (sec K r hr q γ : Γ) * (s q₁' : Γ)⁻¹, hKmem⟩ : K) = s q' * sec K r hr q γ * (s q₁')⁻¹ :=
    Subtype.ext rfl
  have hcimg : ((c ⟨(s q' : Γ) * (sec K r hr q γ : Γ) * (s q₁' : Γ)⁻¹, hKmem⟩ : (⊤ : Subgroup Γ)) : Γ) =
      r' q' * y * (r' q₁')⁻¹ := by
    rw [hKelt, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hgrp : R K K' r s (q, q') * γ * (R K K' r s (q₁, q₁'))⁻¹ = (s q' : Γ) * (sec K r hr q γ : Γ) * (s q₁' : Γ)⁻¹ := by
    simp only [R, coe_sec, ← hq₁]
    group

  have hnext : cls (Kpp K K' c) (R K K' r s (q, q') * γ) = E K K' c r hr s hs (q₁, q₁') := by
    rw [E_apply]
    symm
    apply cls_eq_of_rel
    rw [hgrp, mem_Kpp_iff]
    refine ⟨hKmem, ?_⟩
    rw [hcimg]
    exact sec_mem K' r' hr' q' y

  have hslip : sec K' r' hr' q' y =
      cRes K K' c (sec (Kpp K K' c) (rpp K K' c r hr s hs) (hrpp K K' c r hr s hs) (E K K' c r hr s hs (q, q')) γ) := by
    apply Subtype.ext
    rw [coe_sec, coe_cRes]

    have : ((sec (Kpp K K' c) (rpp K K' c r hr s hs) (hrpp K K' c r hr s hs) (E K K' c r hr s hs (q, q')) γ :
        ↥(Kpp K K' c)) : Γ) = (s q' : Γ) * (sec K r hr q γ : Γ) * (s q₁' : Γ)⁻¹ := by
      rw [coe_sec, rpp_E, hnext, rpp_E, hgrp]
    have helt : (⟨((sec (Kpp K K' c) (rpp K K' c r hr s hs) (hrpp K K' c r hr s hs) (E K K' c r hr s hs (q, q')) γ :
        ↥(Kpp K K' c)) : Γ), Kpp_le K K' c (sec (Kpp K K' c) (rpp K K' c r hr s hs) (hrpp K K' c r hr s hs)
          (E K K' c r hr s hs (q, q')) γ).2⟩ : K) =
        ⟨(s q' : Γ) * (sec K r hr q γ : Γ) * (s q₁' : Γ)⁻¹, hKmem⟩ := Subtype.ext this
    rw [helt, hcimg]
  rw [hslip]
  rfl

end MackeyH1

namespace TTAssembly

open CongruenceSubgroup
open scoped MatrixGroups

theorem exists_sl2_map_eq_map_eq (m n : ℕ) [NeZero m] [NeZero n] (hcop : Nat.Coprime m n)
    (gm : SL(2, ZMod m)) (gn : SL(2, ZMod n)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = gm ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) γ = gn := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  let πm : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let πn : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  let Mm : Matrix (Fin 2) (Fin 2) (ZMod (m * n)) := fun i j =>
    e.symm ((gm : Matrix (Fin 2) (Fin 2) (ZMod m)) i j, (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) i j)
  have hMm : Mm.map πm = (gm : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    ext i j; simp [Mm, πm, Matrix.map_apply]
  have hMn : Mm.map πn = (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    ext i j; simp [Mm, πn, Matrix.map_apply]
  have hdet : Mm.det = 1 := by
    have hgm : (gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 * (gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
        (gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 * (gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
      have := gm.prop; rwa [Matrix.det_fin_two] at this
    have hgn : (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0 * (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 1 -
        (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 1 * (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 0 = 1 := by
      have := gn.prop; rwa [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two]
    simp only [Mm]
    rw [← map_mul, ← map_mul, ← map_sub]
    have : (((gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0, (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0) *
        ((gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1, (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 1) -
        ((gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1, (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 1) *
        ((gm : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0, (gn : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 0) : ZMod m × ZMod n) = 1 := by
      ext
      · simpa using hgm
      · simpa using hgn
    rw [this, map_one]
  let Msl : SL(2, ZMod (m * n)) := ⟨Mm, hdet⟩
  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod (m * n) Msl
  refine ⟨γ, ?_, ?_⟩
  · have : (Int.castRingHom (ZMod m)) = πm.comp (Int.castRingHom (ZMod (m * n))) := RingHom.ext_int _ _
    apply Matrix.SpecialLinearGroup.ext; intro i j
    have h2 := congrArg (fun A : SL(2, ZMod (m * n)) => ((A : Matrix (Fin 2) (Fin 2) (ZMod (m * n))).map πm) i j) hγ
    simp only [Msl, hMm] at h2
    rw [this]
    simpa [Matrix.SpecialLinearGroup.map, Matrix.map_apply] using h2
  · have : (Int.castRingHom (ZMod n)) = πn.comp (Int.castRingHom (ZMod (m * n))) := RingHom.ext_int _ _
    apply Matrix.SpecialLinearGroup.ext; intro i j
    have h2 := congrArg (fun A : SL(2, ZMod (m * n)) => ((A : Matrix (Fin 2) (Fin 2) (ZMod (m * n))).map πn) i j) hγ
    simp only [Msl, hMn] at h2
    rw [this]
    simpa [Matrix.SpecialLinearGroup.map, Matrix.map_apply] using h2

theorem exists_gammaH_bot_map_eq₂ (N ℓ ℓ' : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ']
    (hℓℓ' : Nat.Coprime ℓ ℓ') (hℓN : Nat.Coprime ℓ N) (hℓ'N : Nat.Coprime ℓ' N)
    (g : SL(2, ZMod ℓ)) (g' : SL(2, ZMod ℓ')) :
    ∃ γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)),
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) (γ : SL(2, ℤ)) = g ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ')) (γ : SL(2, ℤ)) = g' := by
  haveI : NeZero (ℓ * ℓ') := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  obtain ⟨γ₀, h₀, h₀'⟩ := exists_sl2_map_eq_map_eq ℓ ℓ' hℓℓ' g g'
  obtain ⟨γ, h1, h2⟩ := exists_sl2_map_eq_map_eq (ℓ * ℓ') N (Nat.Coprime.mul_left hℓN hℓ'N)
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (ℓ * ℓ'))) γ₀) 1

  have hγΓ : γ ∈ Gamma N := by rw [Gamma_mem']; exact h2
  have hγH : γ ∈ CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ) := by
    rw [Gamma_mem] at hγΓ
    obtain ⟨h00, h01, h10, h11⟩ := hγΓ
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [Subgroup.mem_bot]
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11

  have hent : ∀ i j, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (ℓ * ℓ')) = (((γ₀ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (ℓ * ℓ')) := by
    intro i j
    have := congrArg (fun A : SL(2, ZMod (ℓ * ℓ')) => (A : Matrix (Fin 2) (Fin 2) (ZMod (ℓ * ℓ'))) i j) h1
    simpa [Matrix.SpecialLinearGroup.map] using this
  have hdown : ∀ (d : ℕ) (hd : d ∣ ℓ * ℓ') (i j : Fin 2),
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) = (((γ₀ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) := by
    intro d hd i j
    have := congrArg (ZMod.castHom hd (ZMod d)) (hent i j)
    rwa [map_intCast, map_intCast] at this
  refine ⟨⟨γ, hγH⟩, ?_, ?_⟩
  · rw [← h₀]
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simpa [Matrix.SpecialLinearGroup.map] using hdown ℓ (dvd_mul_right ℓ ℓ') i j
  · rw [← h₀']
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simpa [Matrix.SpecialLinearGroup.map] using hdown ℓ' (dvd_mul_left ℓ' ℓ) i j

end TTAssembly

namespace TTAssembly

open CongruenceSubgroup
open scoped MatrixGroups

abbrev G1 (N : ℕ) : Type := ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))

variable (N : ℕ)

theorem mem_GammaHUpper_iff (ℓ : ℕ) (x : G1 N) :
    x ∈ CohCarrier.GammaHUpper N ⊥ ℓ ↔ (ℓ : ℤ) ∣ ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
  rw [CohCarrier.GammaHUpper, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem cTop_apply (ℓ : ℕ) (x : ↥(CohCarrier.GammaHUpper N ⊥ ℓ)) (i j : Fin 2) :
    ((((HeckeCohomology.cTop N ⊥ ℓ x : (⊤ : Subgroup (G1 N))) : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j =
      (!![((x : G1 N) : SL(2, ℤ)) 0 0, ((x : G1 N) : SL(2, ℤ)) 0 1 / ℓ; ((x : G1 N) : SL(2, ℤ)) 1 0 * ℓ, ((x : G1 N) : SL(2, ℤ)) 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) i j :=
  rfl

theorem cTop_apply_01 (ℓ : ℕ) (x : ↥(CohCarrier.GammaHUpper N ⊥ ℓ)) :
    ((((HeckeCohomology.cTop N ⊥ ℓ x : (⊤ : Subgroup (G1 N))) : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
      (((x : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / ℓ :=
  rfl

theorem Kpp_eq (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ ≠ 0) :
    MackeyH1.Kpp (CohCarrier.GammaHUpper N ⊥ ℓ) (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ) =
      CohCarrier.GammaHUpper N ⊥ (ℓ * ℓ') := by
  ext x
  rw [MackeyH1.mem_Kpp_iff]
  constructor
  · rintro ⟨hx, h⟩
    rw [mem_GammaHUpper_iff, cTop_apply_01] at h
    rw [mem_GammaHUpper_iff]
    have hx' := (mem_GammaHUpper_iff N ℓ x).mp hx
    obtain ⟨m, hm⟩ := hx'
    change (ℓ' : ℤ) ∣ (((x : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / ℓ at h
    rw [hm, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hℓ)] at h
    rw [hm]
    push_cast
    exact mul_dvd_mul_left _ h
  · intro h
    rw [mem_GammaHUpper_iff] at h
    push_cast at h
    have hx : (ℓ : ℤ) ∣ ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := (Dvd.intro _ rfl).trans h
    refine ⟨(mem_GammaHUpper_iff N ℓ x).mpr hx, ?_⟩
    rw [mem_GammaHUpper_iff, cTop_apply_01]
    change (ℓ' : ℤ) ∣ (((x : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / ℓ
    obtain ⟨m, hm⟩ := h
    rw [hm, mul_assoc, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hℓ)]
    exact Dvd.intro _ rfl

theorem cpp_apply (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (x : ↥(MackeyH1.Kpp (CohCarrier.GammaHUpper N ⊥ ℓ) (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ)))
    (i j : Fin 2) :
    ((((MackeyH1.cpp (CohCarrier.GammaHUpper N ⊥ ℓ) (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ)
        (HeckeCohomology.cTop N ⊥ ℓ') x : (⊤ : Subgroup (G1 N))) : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j =
      (!![((x : G1 N) : SL(2, ℤ)) 0 0, ((x : G1 N) : SL(2, ℤ)) 0 1 / (ℓ * ℓ'); ((x : G1 N) : SL(2, ℤ)) 1 0 * (ℓ * ℓ'),
        ((x : G1 N) : SL(2, ℤ)) 1 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  show ((((HeckeCohomology.cTop N ⊥ ℓ' (MackeyH1.cRes _ _ _ x) : (⊤ : Subgroup (G1 N))) : G1 N) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [cTop_apply]
  have e : ∀ i' j', ((((MackeyH1.cRes (CohCarrier.GammaHUpper N ⊥ ℓ) (CohCarrier.GammaHUpper N ⊥ ℓ')
      (HeckeCohomology.cTop N ⊥ ℓ) x : ↥(CohCarrier.GammaHUpper N ⊥ ℓ')) : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i' j' =
      (!![((x : G1 N) : SL(2, ℤ)) 0 0, ((x : G1 N) : SL(2, ℤ)) 0 1 / ℓ; ((x : G1 N) : SL(2, ℤ)) 1 0 * ℓ, ((x : G1 N) : SL(2, ℤ)) 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) i' j' :=
    fun i' j' => cTop_apply N ℓ ⟨(x : G1 N), MackeyH1.Kpp_le _ _ _ x.2⟩ i' j'
  fin_cases i <;> fin_cases j
  · simp [e]
  · simp [e, Int.ediv_ediv_of_nonneg (Int.natCast_nonneg ℓ)]
  · simp [e, mul_assoc]
  · simp [e]

theorem heckeH1_congr {k G : Type} [CommRing k] [Group G] (A : Rep k G) {S₂ S₂' : Subgroup G}
    [S₂.FiniteIndex] [S₂'.FiniteIndex] (h : S₂ = S₂')
    (c : S₂ →* (⊤ : Subgroup G)) (c' : S₂' →* (⊤ : Subgroup G))
    (hc : ∀ (x : G) (hx : x ∈ S₂) (hx' : x ∈ S₂'), ((c ⟨x, hx⟩ : (⊤ : Subgroup G)) : G) = ((c' ⟨x, hx'⟩ : (⊤ : Subgroup G)) : G))
    {φ φ' : A →ₗ[k] A} (hφφ' : φ = φ') (hφ : HeckeCohomology.IsTwist ⊤ S₂ c A φ) (hφ' : HeckeCohomology.IsTwist ⊤ S₂' c' A φ') :
    HeckeCohomology.heckeH1 ⊤ S₂ c A φ hφ = HeckeCohomology.heckeH1 ⊤ S₂' c' A φ' hφ' := by
  subst h
  subst hφφ'
  have hcc : c = c' := MonoidHom.ext fun x => Subtype.ext (hc x x.2 x.2)
  subst hcc
  rfl

end TTAssembly

namespace TTAssembly

open CongruenceSubgroup
open scoped MatrixGroups

theorem exists_mul_cTop_inv_mem (N ℓ ℓ' : ℕ) [NeZero N] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (x : G1 N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ k : ↥(CohCarrier.GammaHUpper N ⊥ ℓ),
      x * (((HeckeCohomology.cTop N ⊥ ℓ k : (⊤ : Subgroup (G1 N))) : G1 N))⁻¹ ∈ CohCarrier.GammaHUpper N ⊥ ℓ' := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  have hcop : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne

  set u : (ZMod ℓ')ˣ := ZMod.unitOfCoprime ℓ hcop with hu
  have huval : (u : ZMod ℓ') = (ℓ : ZMod ℓ') := ZMod.coe_unitOfCoprime ℓ hcop

  set a : ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set cc : ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hcc
  set d : ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hdet : a * d - b * cc = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe (x : SL(2, ℤ))
    rwa [Matrix.det_fin_two] at this

  let g' : SL(2, ZMod ℓ') := ⟨!![(a : ZMod ℓ'), (b : ZMod ℓ') * (u : ZMod ℓ'); (cc : ZMod ℓ') * ((u⁻¹ : (ZMod ℓ')ˣ) : ZMod ℓ'), (d : ZMod ℓ')], by
    rw [Matrix.det_fin_two_of]
    have h1 : ((b : ZMod ℓ') * (u : ZMod ℓ')) * ((cc : ZMod ℓ') * ((u⁻¹ : (ZMod ℓ')ˣ) : ZMod ℓ')) = (b : ZMod ℓ') * cc := by
      rw [mul_mul_mul_comm, Units.mul_inv, mul_one]
    rw [h1]
    have := congrArg (fun z : ℤ => (z : ZMod ℓ')) hdet
    push_cast at this
    exact this⟩
  obtain ⟨k, hk1, hk'⟩ := exists_gammaH_bot_map_eq₂ N ℓ ℓ' hcop
    ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN) ((Nat.Prime.coprime_iff_not_dvd hℓ').mpr hℓ'N) 1 g'

  have hkent : ∀ i j, ((((k : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod ℓ) = (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i j := by
    intro i j
    have := congrArg (fun A : SL(2, ZMod ℓ) => (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i j) hk1
    simpa [Matrix.SpecialLinearGroup.map] using this
  have hkent' : ∀ i j, ((((k : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod ℓ') = (g' : Matrix (Fin 2) (Fin 2) (ZMod ℓ')) i j := by
    intro i j
    have := congrArg (fun A : SL(2, ZMod ℓ') => (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ')) i j) hk'
    simpa [Matrix.SpecialLinearGroup.map] using this

  have hk01 : (ℓ : ℤ) ∣ (((k : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hkent 0 1]
    simp
  refine ⟨⟨(k : G1 N), (mem_GammaHUpper_iff N ℓ _).mpr hk01⟩, ?_⟩
  rw [mem_GammaHUpper_iff]

  obtain ⟨β, hβ⟩ := hk01
  have hβ' : (β : ZMod ℓ') = (b : ZMod ℓ') := by
    have h := hkent' 0 1
    rw [hβ] at h
    push_cast at h
    change (ℓ : ZMod ℓ') * (β : ZMod ℓ') = (b : ZMod ℓ') * (u : ZMod ℓ') at h
    rw [← huval, mul_comm] at h
    exact (Units.mul_left_inj u).mp h

  have hent : (((x * (((HeckeCohomology.cTop N ⊥ ℓ ⟨(k : G1 N), (mem_GammaHUpper_iff N ℓ _).mpr ⟨β, hβ⟩⟩ :
      (⊤ : Subgroup (G1 N))) : G1 N))⁻¹ : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
      a * (-((((k : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / ℓ)) + b * (((k : G1 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [cTop_apply N ℓ _ 0 1, cTop_apply N ℓ _ 0 0]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rfl
  rw [hent, hβ, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hℓ.ne_zero), ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hβ', hkent' 0 0]
  simp only [g', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem exists_section (N ℓ ℓ' : ℕ) [NeZero N] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ s : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper N ⊥ ℓ')) → ↥(CohCarrier.GammaHUpper N ⊥ ℓ),
      ∀ q', cls (CohCarrier.GammaHUpper N ⊥ ℓ')
        (((HeckeCohomology.cTop N ⊥ ℓ (s q') : (⊤ : Subgroup (G1 N))) : G1 N)) = q' := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have h := fun q' : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper N ⊥ ℓ')) =>
    exists_mul_cTop_inv_mem N ℓ ℓ' hℓ hℓ' hne hℓN hℓ'N q'.out
  choose s hs using h
  refine ⟨s, fun q' => ?_⟩
  rw [MackeyH1.cls_eq_of_rel _ (hs q')]
  exact q'.out_eq'

theorem diag_mem_comm (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ)) (ℓ ℓ' : ℕ)
    (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M) (hℓM' : !![(ℓ' : ℤ), 0; 0, 1] ∈ M) :
    (⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩ : M) * ⟨!![(ℓ' : ℤ), 0; 0, 1], hℓM'⟩ = ⟨!![(ℓ' : ℤ), 0; 0, 1], hℓM'⟩ * ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩ := by
  apply Subtype.ext
  show !![(ℓ : ℤ), 0; 0, 1] * !![(ℓ' : ℤ), 0; 0, 1] = !![(ℓ' : ℤ), 0; 0, 1] * !![(ℓ : ℤ), 0; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end TTAssembly

open TTAssembly in
theorem solution
    (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M)
    (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓN' : ¬ ℓ' ∣ N) (hℓM' : !![(ℓ' : ℤ), 0; 0, 1] ∈ M)
    (hφ : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X
        (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩))
    (hφ' : haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
      HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ') X
        (ρ' ⟨!![(ℓ' : ℤ), 0; 0, 1], hℓM'⟩)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
    Commute (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X _ hφ) (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ') X _ hφ') := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exact absurd (hN0 ▸ dvd_zero ℓ) hℓN
  haveI : NeZero N := ⟨hNpos.ne'⟩
  by_cases hne : ℓ = ℓ'
  · subst hne
    exact Commute.refl _
  ·
    have hr : ∀ q : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper N ⊥ ℓ)),
        cls (CohCarrier.GammaHUpper N ⊥ ℓ) (rep (CohCarrier.GammaHUpper N ⊥ ℓ) q) = q := fun q => q.out_eq'
    have hr' : ∀ q : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper N ⊥ ℓ')),
        cls (CohCarrier.GammaHUpper N ⊥ ℓ') (rep (CohCarrier.GammaHUpper N ⊥ ℓ') q) = q := fun q => q.out_eq'
    obtain ⟨s, hs⟩ := exists_section N ℓ ℓ' hℓ hℓ' hne hℓN hℓN'
    obtain ⟨s', hs'⟩ := exists_section N ℓ' ℓ hℓ' hℓ (Ne.symm hne) hℓN' hℓN
    haveI i1 := MackeyH1.finiteIndex_Kpp (CohCarrier.GammaHUpper N ⊥ ℓ) (CohCarrier.GammaHUpper N ⊥ ℓ')
      (HeckeCohomology.cTop N ⊥ ℓ) (rep _) hr s hs
    haveI i2 := MackeyH1.finiteIndex_Kpp (CohCarrier.GammaHUpper N ⊥ ℓ') (CohCarrier.GammaHUpper N ⊥ ℓ)
      (HeckeCohomology.cTop N ⊥ ℓ') (rep _) hr' s' hs'
    have M1 := MackeyH1.mackey X (CohCarrier.GammaHUpper N ⊥ ℓ) (CohCarrier.GammaHUpper N ⊥ ℓ')
      (HeckeCohomology.cTop N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ') (rep _) hr s hs _ _ hφ hφ'
    have M2 := MackeyH1.mackey X (CohCarrier.GammaHUpper N ⊥ ℓ') (CohCarrier.GammaHUpper N ⊥ ℓ)
      (HeckeCohomology.cTop N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ) (rep _) hr' s' hs' _ _ hφ' hφ
    show _ * _ = _ * _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, M1, M2]
    refine heckeH1_congr X (by rw [Kpp_eq N ℓ ℓ' hℓ.ne_zero, Kpp_eq N ℓ' ℓ hℓ'.ne_zero, mul_comm]) _ _ ?_ ?_ _ _
    · intro x hx hx'
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [cpp_apply N ℓ ℓ' ⟨x, hx⟩ i j, cpp_apply N ℓ' ℓ ⟨x, hx'⟩ i j, mul_comm (ℓ : ℤ) ℓ']
    · rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, diag_mem_comm]

end S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid
end P2MW
export P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid (solution)
