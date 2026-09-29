-- Prove2me | solution 1 for HeckeEis.degeneracyTransferZero_heckeOperatorHom_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c10e6f69-b4d8-53c1-b638-b52c9aa759d5

import Definitions.Def_HeckeEis_DegeneracyTransfers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm

set_option autoImplicit false
set_option Elab.async false
open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

namespace INHHBZ

section Generic
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

theorem section_cocycle_mem (H : Subgroup G) (R : G ⧸ H → G) (hR : ∀ q, (R q : G ⧸ H) = q)
    (g : G) (q : G ⧸ H) : (R (g • q))⁻¹ * (g * R q) ∈ H := by
  refine QuotientGroup.eq.mp ?_
  rw [hR (g • q)]
  show g • q = ((g * R q : G) : G ⧸ H)
  rw [show ((g * R q : G) : G ⧸ H) = g • ((R q : G) : G ⧸ H) from rfl, hR q]

theorem coresHom_apply_section (H : Subgroup G) [H.FiniteIndex] (φ : Additive ↥H →+ A)
    (R : G ⧸ H → G) (hR : ∀ q, (R q : G ⧸ H) = q) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    coresHom H φ (Additive.ofMul g) =
      ∑ q : G ⧸ H, φ (Additive.ofMul
        (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  have hmem : ∀ q : G ⧸ H, (Quotient.out q)⁻¹ * R q ∈ H := fun q => by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq', hR q]
  have hsplit : ∀ q : G ⧸ H,
      φ (Additive.ofMul (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H))
        = φ (Additive.ofMul (transferAux H g q))
          + (φ (Additive.ofMul (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H))
             - φ (Additive.ofMul (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H))) := by
    intro q
    have hdec : (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H)
        = (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H)⁻¹
            * transferAux H g q * (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H) := by
      ext
      show (R (g • q))⁻¹ * (g * R q)
          = ((Quotient.out (g • q))⁻¹ * R (g • q))⁻¹
              * ((g • q).out⁻¹ * (g * Quotient.out q)) * ((Quotient.out q)⁻¹ * R q)
      group
    rw [hdec, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel
  have hre : ∑ q : G ⧸ H,
      φ (Additive.ofMul (⟨(Quotient.out (g • q))⁻¹ * R (g • q), hmem (g • q)⟩ : ↥H))
        = ∑ q : G ⧸ H, φ (Additive.ofMul (⟨(Quotient.out q)⁻¹ * R q, hmem q⟩ : ↥H)) :=
    Fintype.sum_equiv
      (⟨fun q => g • q, fun q => g⁻¹ • q, fun q => inv_smul_smul g q,
        fun q => smul_inv_smul g q⟩ : (G ⧸ H) ≃ (G ⧸ H))
      _ _ (fun q => rfl)
  have hsec : ∑ q : G ⧸ H, φ (Additive.ofMul
      (⟨(R (g • q))⁻¹ * (g * R q), section_cocycle_mem H R hR g q⟩ : ↥H))
        = ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) := by
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hre]
    simp
  rw [coresHom_apply, hsec]

end Generic

section Transport
variable {K G' : Type*} [Group K] [Group G'] {A : Type*} [AddCommGroup A]

def quotMap (H' : Subgroup G') (σ : K →* G') : K ⧸ (H'.comap σ) → G' ⧸ H' :=
  Quotient.map' σ (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [map_mul, map_inv] using hab)

@[scoped simp] theorem quotMap_mk (H' : Subgroup G') (σ : K →* G') (k : K) :
    quotMap H' σ ((k : K ⧸ (H'.comap σ))) = ((σ k : G') : G' ⧸ H') := rfl

theorem quotMap_injective (H' : Subgroup G') (σ : K →* G') :
    Function.Injective (quotMap H' σ) := by
  intro a b
  refine Quotient.inductionOn₂' a b (fun x y h => ?_)
  have hxy : (σ x)⁻¹ * σ y ∈ H' := QuotientGroup.eq.mp h
  refine QuotientGroup.eq.mpr ?_
  show x⁻¹ * y ∈ H'.comap σ
  rw [Subgroup.mem_comap, map_mul, map_inv]
  exact hxy

theorem surj_quotMap_of_surjective {K G' : Type*} [Group K] [Group G'] (H' : Subgroup G')
    (σ : K →* G') (hσ : Function.Surjective σ) : Function.Surjective (quotMap H' σ) := by
  intro s
  refine Quotient.inductionOn' s (fun g' => ?_)
  obtain ⟨k, rfl⟩ := hσ g'
  exact ⟨((k : K) : K ⧸ (H'.comap σ)), rfl⟩

theorem finiteIndex_comap_of_surjQuot {K G' : Type*} [Group K] [Group G']
    (H' : Subgroup G') [H'.FiniteIndex] (σ : K →* G')
    (hsurj : Function.Surjective (quotMap H' σ)) : (H'.comap σ).FiniteIndex := by
  constructor
  have hcard : Nat.card (K ⧸ (H'.comap σ)) = Nat.card (G' ⧸ H') :=
    Nat.card_eq_of_bijective _ ⟨quotMap_injective H' σ, hsurj⟩
  show (H'.comap σ).index ≠ 0
  rw [Subgroup.index, hcard]
  exact Subgroup.FiniteIndex.index_ne_zero

set_option maxHeartbeats 6400000 in

theorem coresHom_comp_apply (H' : Subgroup G') [H'.FiniteIndex] (σ : K →* G')
    [(H'.comap σ).FiniteIndex]
    (hsurj : Function.Surjective (quotMap H' σ))
    (ψ : Additive ↥H' →+ A) (k : K) :
    coresHom H' ψ (Additive.ofMul (σ k)) =
      coresHom (H'.comap σ) (ψ.comp (AddMonoidHom.mk'
        (fun j => Additive.ofMul (⟨σ (Additive.toMul j : ↥(H'.comap σ)), (Additive.toMul j).2⟩ : ↥H'))
        (fun a b => by simp [map_mul]; rfl)))
        (Additive.ofMul k) := by
  classical
  letI := H'.fintypeQuotientOfFiniteIndex
  letI := (H'.comap σ).fintypeQuotientOfFiniteIndex
  have hbij : Function.Bijective (quotMap H' σ) := ⟨quotMap_injective H' σ, hsurj⟩
  set e : (K ⧸ (H'.comap σ)) ≃ (G' ⧸ H') := Equiv.ofBijective _ hbij with hedef
  have happ : ∀ w, e w = quotMap H' σ w := fun _ => rfl
  set R : G' ⧸ H' → G' := fun s => σ (Quotient.out (e.symm s)) with hRdef
  have hR : ∀ s, ((R s : G') : G' ⧸ H') = s := by
    intro s
    show ((σ (Quotient.out (e.symm s)) : G') : G' ⧸ H') = s
    have h1 : ((σ (Quotient.out (e.symm s)) : G') : G' ⧸ H')
        = quotMap H' σ ((Quotient.out (e.symm s) : K) : K ⧸ (H'.comap σ)) := rfl
    rw [h1, QuotientGroup.out_eq']
    rw [← happ (e.symm s)]
    exact e.apply_symm_apply s
  rw [coresHom_apply_section H' ψ R hR (σ k), coresHom_apply]
  refine (Fintype.sum_equiv e _ _ ?_).symm
  intro w
  have hsmul : (σ k) • (e w) = e (k • w) := by
    refine Quotient.inductionOn' w (fun a => ?_)
    show ((σ k * σ a : G') : G' ⧸ H') = quotMap H' σ ((k * a : K) : K ⧸ (H'.comap σ))
    rw [quotMap_mk, map_mul]
  have hRew : R (e w) = σ (Quotient.out w) := by
    show σ (Quotient.out (e.symm (e w))) = σ (Quotient.out w)
    rw [e.symm_apply_apply]
  have hRsmul : R ((σ k) • (e w)) = σ (Quotient.out (k • w)) := by
    rw [hsmul]
    show σ (Quotient.out (e.symm (e (k • w)))) = σ (Quotient.out (k • w))
    rw [e.symm_apply_apply]
  refine congrArg ψ (congrArg Additive.ofMul (Subtype.ext ?_))
  show σ ((transferAux (H'.comap σ) k w : ↥(H'.comap σ)) : K)
      = (R ((σ k) • (e w)))⁻¹ * (σ k * R (e w))
  rw [hRew, hRsmul, coe_transferAux]
  rw [map_mul, map_mul, map_inv]

end Transport

section Trans
variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

def mapDown (K : Subgroup G) (J : Subgroup ↥K) : ↥(J.map K.subtype) →* ↥J where
  toFun x := ⟨⟨x.1, Subgroup.map_subtype_le J x.2⟩, by
    obtain ⟨j, hjJ, hjval⟩ := x.2
    have hj : (⟨x.1, Subgroup.map_subtype_le J x.2⟩ : ↥K) = j := Subtype.ext hjval.symm
    rw [hj]; exact hjJ⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

@[scoped simp] theorem coe_coe_mapDown (K : Subgroup G) (J : Subgroup ↥K) (x : ↥(J.map K.subtype)) :
    (((mapDown K J x : ↥J) : ↥K) : G) = (x : G) := rfl

def projQuot (K : Subgroup G) (J : Subgroup ↥K) : G ⧸ (J.map K.subtype) → G ⧸ K :=
  Quotient.map' id (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact Subgroup.map_subtype_le J hab)

@[scoped simp] theorem projQuot_mk (K : Subgroup G) (J : Subgroup ↥K) (x : G) :
    projQuot K J ((x : G) : G ⧸ (J.map K.subtype)) = ((x : G) : G ⧸ K) := rfl

theorem coresHom_trans (K : Subgroup G) [K.FiniteIndex] (J : Subgroup ↥K) [J.FiniteIndex]
    [(J.map K.subtype).FiniteIndex] (χ : Additive ↥J →+ A) (g : G) :
    coresHom K (coresHom J χ) (Additive.ofMul g) =
      coresHom (J.map K.subtype) (pullbackHom (mapDown K J) χ) (Additive.ofMul g) := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  letI := J.fintypeQuotientOfFiniteIndex
  set Ĵ := J.map K.subtype with hJhat
  letI := Ĵ.fintypeQuotientOfFiniteIndex

  have hfib_mem : ∀ v : G ⧸ Ĵ, (Quotient.out (projQuot K J v))⁻¹ * Quotient.out v ∈ K := by
    intro v
    refine QuotientGroup.eq.mp ?_
    have h1 : projQuot K J ((Quotient.out v : G) : G ⧸ Ĵ) = ((Quotient.out v : G) : G ⧸ K) := rfl
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' v]
    rw [h1]
  set fib : (v : G ⧸ Ĵ) → ↥K ⧸ J := fun v =>
    ((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) : ↥K ⧸ J)
    with hfibdef

  set unpair : (G ⧸ K) × (↥K ⧸ J) → G ⧸ Ĵ := fun p =>
    ((Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G) : G) : G ⧸ Ĵ) with hunpairdef
  have hround1 : ∀ v : G ⧸ Ĵ, unpair (projQuot K J v, fib v) = v := by
    intro v
    show ((Quotient.out (projQuot K J v) * ((Quotient.out (fib v) : ↥K) : G) : G) : G ⧸ Ĵ) = v
    conv_rhs => rw [← QuotientGroup.out_eq' v]
    refine (QuotientGroup.eq.mpr ?_).symm

    have hj : (Quotient.out (fib v))⁻¹
        * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) ∈ J := by
      refine QuotientGroup.eq.mp ?_
      rw [QuotientGroup.out_eq']
    have hval : (Quotient.out v)⁻¹
        * (Quotient.out (projQuot K J v) * ((Quotient.out (fib v) : ↥K) : G))
        = ((((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹
            * Quotient.out (fib v) : ↥K) : G) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [hval]
    refine ⟨((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹
        * Quotient.out (fib v), ?_, rfl⟩
    have hflip : ((⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹
        * Quotient.out (fib v)
        = ((Quotient.out (fib v))⁻¹
            * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K))⁻¹ := by
      group
    rw [hflip]
    exact J.inv_mem hj
  have hmem_of_val : ∀ (x : ↥K), (x : G) ∈ Ĵ → x ∈ J := by
    intro x hx
    obtain ⟨j, hjJ, hjval⟩ := hx
    have hxj : x = j := Subtype.ext hjval.symm
    rw [hxj]; exact hjJ
  have hround2a : ∀ p : (G ⧸ K) × (↥K ⧸ J), projQuot K J (unpair p) = p.1 := by
    intro p
    show ((Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G) : G) : G ⧸ K) = p.1
    conv_rhs => rw [← QuotientGroup.out_eq' p.1]
    refine (QuotientGroup.eq.mpr ?_).symm
    rw [inv_mul_cancel_left]
    exact (Quotient.out p.2).2

  have hfib_smul : ∀ (x : G) (v : G ⧸ Ĵ),
      fib (x • v) = transferAux K x (projQuot K J v) • fib v := by
    intro x v
    have hproj : projQuot K J (x • v) = x • projQuot K J v := by
      refine Quotient.inductionOn' v (fun a => ?_)
      rfl
    show ((⟨(Quotient.out (projQuot K J (x • v)))⁻¹ * Quotient.out (x • v),
        hfib_mem (x • v)⟩ : ↥K) : ↥K ⧸ J) = _
    conv_rhs => rw [← QuotientGroup.out_eq' (fib v)]
    show _ = ((transferAux K x (projQuot K J v) * Quotient.out (fib v) : ↥K) : ↥K ⧸ J)
    refine (QuotientGroup.eq.mpr ?_).symm
    refine hmem_of_val _ ?_

    have hĵ1 : (Quotient.out v)⁻¹ * x⁻¹ * Quotient.out (x • v) ∈ Ĵ := by
      have h1 : ((x * Quotient.out v : G) : G ⧸ Ĵ) = ((Quotient.out (x • v) : G) : G ⧸ Ĵ) := by
        rw [QuotientGroup.out_eq']
        show x • ((Quotient.out v : G) : G ⧸ Ĵ) = x • v
        rw [QuotientGroup.out_eq']
      have h2 := QuotientGroup.eq.mp h1
      simpa [mul_assoc] using h2
    have hj0 : (Quotient.out (fib v))⁻¹
        * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) ∈ J := by
      refine QuotientGroup.eq.mp ?_
      rw [QuotientGroup.out_eq']

    have hval : ((((transferAux K x (projQuot K J v) * Quotient.out (fib v) : ↥K))⁻¹
          * (⟨(Quotient.out (projQuot K J (x • v)))⁻¹ * Quotient.out (x • v),
              hfib_mem (x • v)⟩ : ↥K) : ↥K) : G)
        = (((Quotient.out (fib v))⁻¹
            * (⟨(Quotient.out (projQuot K J v))⁻¹ * Quotient.out v, hfib_mem v⟩ : ↥K) : ↥K) : G)
          * ((Quotient.out v)⁻¹ * x⁻¹ * Quotient.out (x • v)) := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_transferAux, hproj]
      group
    rw [hval]
    exact Subgroup.mul_mem _ ⟨_, hj0, rfl⟩ hĵ1

  set R : G ⧸ Ĵ → G := fun v =>
    Quotient.out (projQuot K J v) * ((Quotient.out (fib v) : ↥K) : G) with hRdef
  have hR : ∀ v, ((R v : G) : G ⧸ Ĵ) = v := fun v => hround1 v

  have hRg : ∀ v : G ⧸ Ĵ, R (g • v)
      = Quotient.out (g • projQuot K J v)
        * ((Quotient.out (transferAux K g (projQuot K J v) • fib v) : ↥K) : G) := by
    intro v
    show Quotient.out (projQuot K J (g • v)) * ((Quotient.out (fib (g • v)) : ↥K) : G) = _
    rw [hfib_smul g v]
    congr 2
    refine Quotient.inductionOn' v (fun a => ?_)
    rfl

  have hL : coresHom K (coresHom J χ) (Additive.ofMul g)
      = ∑ t : G ⧸ K, ∑ w : ↥K ⧸ J,
          χ (Additive.ofMul (transferAux J (transferAux K g t) w)) := by
    rw [coresHom_apply]
    exact Finset.sum_congr rfl (fun t _ => coresHom_apply J χ (transferAux K g t))
  rw [hL, coresHom_apply_section Ĵ (pullbackHom (mapDown K J) χ) R hR g]

  have hpair : ∀ v : G ⧸ Ĵ,
      (pullbackHom (mapDown K J) χ) (Additive.ofMul
        (⟨(R (g • v))⁻¹ * (g * R v), section_cocycle_mem Ĵ R hR g v⟩ : ↥Ĵ))
        = χ (Additive.ofMul (transferAux J (transferAux K g (projQuot K J v)) (fib v))) := by
    intro v
    rw [pullbackHom_apply]
    refine (congrArg χ (congrArg Additive.ofMul (Subtype.ext (Subtype.ext ?_)))).symm
    show ((((transferAux J (transferAux K g (projQuot K J v)) (fib v) : ↥J) : ↥K)) : G)
        = (R (g • v))⁻¹ * (g * R v)
    rw [coe_transferAux, hRg v]
    simp only [hRdef, Subgroup.coe_mul, InvMemClass.coe_inv, coe_transferAux]
    group
  rw [Finset.sum_congr rfl (fun v _ => hpair v)]

  have hsum : ∑ v : G ⧸ Ĵ,
      χ (Additive.ofMul (transferAux J (transferAux K g (projQuot K J v)) (fib v)))
        = ∑ p : (G ⧸ K) × (↥K ⧸ J),
            χ (Additive.ofMul (transferAux J (transferAux K g p.1) p.2)) := by
    refine Fintype.sum_equiv
      (⟨fun v => (projQuot K J v, fib v), unpair, hround1, fun p => ?_⟩ :
        (G ⧸ Ĵ) ≃ ((G ⧸ K) × (↥K ⧸ J)))
      _ _ (fun v => rfl)

    have h2b : fib (unpair p) = p.2 := by
      show ((⟨(Quotient.out (projQuot K J (unpair p)))⁻¹ * Quotient.out (unpair p),
          hfib_mem (unpair p)⟩ : ↥K) : ↥K ⧸ J) = p.2
      conv_rhs => rw [← QuotientGroup.out_eq' p.2]
      refine (QuotientGroup.eq.mpr ?_).symm
      refine hmem_of_val _ ?_
      have hĵ : ((Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G))⁻¹
          * Quotient.out (unpair p)) ∈ Ĵ := by
        refine QuotientGroup.eq.mp ?_
        rw [QuotientGroup.out_eq']
      have hval2 : (((Quotient.out p.2)⁻¹
            * (⟨(Quotient.out (projQuot K J (unpair p)))⁻¹ * Quotient.out (unpair p),
                hfib_mem (unpair p)⟩ : ↥K) : ↥K) : G)
          = (Quotient.out p.1 * ((Quotient.out p.2 : ↥K) : G))⁻¹
              * Quotient.out (unpair p) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hround2a]
        group
      rw [hval2]
      exact hĵ
    exact Prod.ext (hround2a p) h2b
  exact
    calc ∑ t : G ⧸ K, ∑ w : ↥K ⧸ J, χ (Additive.ofMul (transferAux J (transferAux K g t) w))
        = ∑ p : (G ⧸ K) × (↥K ⧸ J),
            χ (Additive.ofMul (transferAux J (transferAux K g p.1) p.2)) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ v : G ⧸ Ĵ,
            χ (Additive.ofMul (transferAux J (transferAux K g (projQuot K J v)) (fib v))) :=
          hsum.symm

theorem coresHom_congr {G : Type*} [Group G] {K₁ K₂ : Subgroup G} (h : K₁ = K₂)
    [K₁.FiniteIndex] [K₂.FiniteIndex]
    (f₁ : Additive ↥K₁ →+ A) (f₂ : Additive ↥K₂ →+ A)
    (hf : ∀ (g : G) (h₁ : g ∈ K₁), f₁ (Additive.ofMul (⟨g, h₁⟩ : ↥K₁))
        = f₂ (Additive.ofMul (⟨g, h ▸ h₁⟩ : ↥K₂)))
    (x : Additive G) :
    coresHom K₁ f₁ x = coresHom K₂ f₂ x := by
  subst h
  have hext : f₁ = f₂ := AddMonoidHom.ext fun y => by
    have h := hf (Additive.toMul y : ↥K₁) (Additive.toMul y).2
    simpa using h
  rw [hext]

end Trans

section Gamma0Side

variable (N q' : ℕ) [NeZero N] [NeZero q']

omit [NeZero N] [NeZero q'] in

theorem range_iota0_eq_subgroupOf :
    (Ihara.ι₀ N q').range = (Gamma0 (N * q')).subgroupOf (Gamma0 N) :=
  Subgroup.inclusion_range (Ihara.Gamma0_mul_le N q')

def iotaChar (φ : Additive (Gamma0 (N * q')) →+ ℤ) :
    Additive ↥((Gamma0 (N * q')).subgroupOf (Gamma0 N)) →+ ℤ :=
  AddMonoidHom.mk'
    (fun j => φ (Additive.ofMul (⟨((Additive.toMul j :
        ↥((Gamma0 (N * q')).subgroupOf (Gamma0 N))) : Gamma0 N), (Additive.toMul j).2⟩ :
      Gamma0 (N * q'))))
    (fun c d => by
      rw [← map_add, ← ofMul_mul]
      rfl)

omit [NeZero N] [NeZero q'] in
theorem iotaChar_apply (φ : Additive (Gamma0 (N * q')) →+ ℤ) (w : Gamma0 N)
    (h : w ∈ (Gamma0 (N * q')).subgroupOf (Gamma0 N)) :
    iotaChar N q' φ (Additive.ofMul ⟨w, h⟩) = φ (Additive.ofMul ⟨(w : SL(2, ℤ)), h⟩) :=
  rfl

omit [NeZero N] in

theorem heckeUpper_comap_conj_bezout (a b : ℤ) (hab : (q' : ℤ) * a - (N : ℤ) * b = 1) :
    (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (Ihara.ι₀ N q').range := by
  ext x
  constructor
  · intro hx
    have hmem : bezoutConjugator N q' a b hab * x * (bezoutConjugator N q' a b hab)⁻¹
        ∈ heckeUpper N q' := hx
    rw [← range_iota1 N (NeZero.ne q')] at hmem
    obtain ⟨δ, hδ⟩ := hmem
    have hsolve : alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)
        (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)
          ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) = δ := by
      rw [alConjHom_bezout_sq N q' a b hab]
      group
    have hι₁ : Ihara.ι₁ N q' δ
        = bezoutConjugator N q' a b hab *
            Ihara.ι₀ N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab)
              ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) *
            (bezoutConjugator N q' a b hab)⁻¹ := by
      conv_lhs => rw [← hsolve]
      rw [iota1_alConjHom]
    refine ⟨alConjHom N q' (bezoutConjugator N q' a b hab)
      (bezoutConjugator_heckeUpper_dvd N q' a b hab)
      ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab), ?_⟩
    have hux : bezoutConjugator N q' a b hab *
        Ihara.ι₀ N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)
          ((alConjSqElt N q' a b hab)⁻¹ * δ * alConjSqElt N q' a b hab)) *
        (bezoutConjugator N q' a b hab)⁻¹
        = bezoutConjugator N q' a b hab * x * (bezoutConjugator N q' a b hab)⁻¹ := by
      rw [← hι₁, hδ]
    exact mul_left_cancel (mul_right_cancel hux)
  · rintro ⟨γ, rfl⟩
    show bezoutConjugator N q' a b hab * Ihara.ι₀ N q' γ *
        (bezoutConjugator N q' a b hab)⁻¹ ∈ heckeUpper N q'
    exact (mem_heckeUpper N q').mpr (bezoutConjugator_heckeUpper_dvd N q' a b hab γ)

omit [NeZero N] in

theorem heckeUpper_comap_eq_subgroupOf (a b : ℤ)
    (hab : (q' : ℤ) * a - (N : ℤ) * b = 1) :
    (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (Gamma0 (N * q')).subgroupOf (Gamma0 N) :=
  (heckeUpper_comap_conj_bezout N q' a b hab).trans (range_iota0_eq_subgroupOf N q')

theorem degeneracyTransfer₀Aux_eq_coresHom_of_point (a b : ℤ)
    (hab : (q' : ℤ) * a - (N : ℤ) * b = 1)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ)
    (χ : Additive ↥((Gamma0 (N * q')).subgroupOf (Gamma0 N)) →+ ℤ)
    (hχpoint : ∀ (w : Gamma0 N) (h : w ∈ (Gamma0 (N * q')).subgroupOf (Gamma0 N)),
      χ (Additive.ofMul ⟨w, h⟩) = φ (Additive.ofMul ⟨(w : SL(2, ℤ)), h⟩))
    (x : Additive (Gamma0 N)) :
    degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x
      = coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) χ x := by
  classical
  have hcomap : (heckeUpper N q').comap
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      = (Gamma0 (N * q')).subgroupOf (Gamma0 N) :=
    heckeUpper_comap_eq_subgroupOf N q' a b hab
  haveI : ((heckeUpper N q').comap
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom).FiniteIndex := by
    rw [hcomap]; infer_instance
  have hσsurj : Function.Surjective
      (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom :=
    (MulAut.conj (bezoutConjugator N q' a b hab)).surjective
  have hRHS : degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
      (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x
      = coresHom (heckeUpper N q')
          (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
            (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)) x := rfl
  have hwash : coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) χ x
      = coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) χ
          (Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
            bezoutConjugator N q' a b hab)) := by
    rw [show Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
        bezoutConjugator N q' a b hab)
      = Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ : Gamma0 N)
        + Additive.ofMul (Additive.toMul x)
        + Additive.ofMul (bezoutConjugator N q' a b hab : Gamma0 N) from rfl]
    rw [map_add, map_add, ofMul_inv, map_neg]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx]
    abel
  have hG2 := coresHom_comp_apply (heckeUpper N q')
    (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
    (surj_quotMap_of_surjective _ _ hσsurj)
    (pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
      (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ))
    ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab)
  have hσg : (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab)
      = Additive.toMul x := by
    show bezoutConjugator N q' a b hab *
        ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab) *
        (bezoutConjugator N q' a b hab)⁻¹ = Additive.toMul x
    group
  have hχ : ∀ (w : Gamma0 N)
      (h₁ : w ∈ (heckeUpper N q').comap
        (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)
      (h₂ : w ∈ (Gamma0 (N * q')).subgroupOf (Gamma0 N)),
      ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
        (AddMonoidHom.mk' (fun j => Additive.ofMul
          (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
              (Additive.toMul j : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
            (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
          (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
                ((Additive.toMul c : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
                ((Additive.toMul d : ↥((heckeUpper N q').comap
                  (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
        (Additive.ofMul ⟨w, h₁⟩)
      = χ (Additive.ofMul ⟨w, h₂⟩) := by
    intro w h₁ h₂
    have hγr : w ∈ (Ihara.ι₀ N q').range := (range_iota0_eq_subgroupOf N q').symm ▸ h₂
    obtain ⟨γ, hγ⟩ := hγr
    have hval : (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
        h₁⟩ : ↥(heckeUpper N q'))
        = iotaUpperHom N q' (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ) := by
      refine Subtype.ext ?_
      rw [coe_iotaUpperHom, iota1_alConjHom]
      show bezoutConjugator N q' a b hab * w * (bezoutConjugator N q' a b hab)⁻¹
          = bezoutConjugator N q' a b hab * Ihara.ι₀ N q' γ *
            (bezoutConjugator N q' a b hab)⁻¹
      rw [hγ]
    have hsymmcollapse : ∀ z : Gamma0 (N * q'),
        (iotaUpperEquiv N q').symm.toMonoidHom (iotaUpperHom N q' z) = z := by
      intro z
      show (iotaUpperEquiv N q').symm (iotaUpperHom N q' z) = z
      rw [← iotaUpperEquiv_apply, MulEquiv.symm_apply_apply]
    have hL : ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)))
        (Additive.ofMul (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
          h₁⟩ : ↥(heckeUpper N q')))
        = φ (Additive.ofMul (alConjHom N q' (bezoutConjugator N q' a b hab)
            (bezoutConjugator_heckeUpper_dvd N q' a b hab)
            (alConjHom N q' (bezoutConjugator N q' a b hab)
              (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ))) := by
      rw [hval, pullbackHom_apply, hsymmcollapse, pullbackHom_apply]
    have hsq : φ (Additive.ofMul (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)
        (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab) γ)))
        = φ (Additive.ofMul γ) := by
      rw [alConjHom_bezout_sq N q' a b hab]
      rw [show Additive.ofMul (alConjSqElt N q' a b hab * γ * (alConjSqElt N q' a b hab)⁻¹)
          = Additive.ofMul (alConjSqElt N q' a b hab) + Additive.ofMul γ
            + Additive.ofMul ((alConjSqElt N q' a b hab))⁻¹ from rfl]
      rw [map_add, map_add, ofMul_inv, map_neg]
      abel
    have hR : χ (Additive.ofMul ⟨w, h₂⟩) = φ (Additive.ofMul γ) := by
      rw [hχpoint w h₂]
      exact congrArg φ (congrArg Additive.ofMul (Subtype.ext
        (congrArg (fun z : Gamma0 N => (z : SL(2, ℤ))) hγ.symm)))
    show ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
        (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
          (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)))
        (Additive.ofMul (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom w,
          h₁⟩ : ↥(heckeUpper N q'))) = _
    rw [hL, hsq, hR]
  have hcongr := coresHom_congr hcomap.symm χ
    ((pullbackHom ((iotaUpperEquiv N q').symm.toMonoidHom)
      (pullbackHom (alConjHom N q' (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab)) φ)).comp
      (AddMonoidHom.mk' (fun j => Additive.ofMul
        (⟨(MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
            (Additive.toMul j : ↥((heckeUpper N q').comap
              (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)),
          (Additive.toMul j).2⟩ : ↥(heckeUpper N q')))
        (fun c d => by
          rw [← ofMul_mul]
          exact congrArg Additive.ofMul (Subtype.ext
            (map_mul (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
              ((Additive.toMul c : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N)
              ((Additive.toMul d : ↥((heckeUpper N q').comap
                (MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom)) : Gamma0 N))))))
    (fun g hg => (hχ g (hcomap.symm ▸ hg) hg).symm)
    (Additive.ofMul ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x *
      bezoutConjugator N q' a b hab))
  have harg : Additive.ofMul ((MulAut.conj (bezoutConjugator N q' a b hab)).toMonoidHom
      ((bezoutConjugator N q' a b hab)⁻¹ * Additive.toMul x * bezoutConjugator N q' a b hab))
      = x := by
    rw [hσg]
    rfl
  have h1 := hwash.trans hcongr
  have h2 := h1.trans hG2.symm
  rw [harg] at h2
  exact hRHS.trans h2.symm

theorem degeneracyTransfer₀Aux_eq_coresHom_iotaChar (a b : ℤ)
    (hab : (q' : ℤ) * a - (N : ℤ) * b = 1)
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (x : Additive (Gamma0 N)) :
    degeneracyTransfer₀Aux N q' ℤ (bezoutConjugator N q' a b hab)
        (bezoutConjugator_heckeUpper_dvd N q' a b hab) φ x
      = coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) (iotaChar N q' φ) x :=
  degeneracyTransfer₀Aux_eq_coresHom_of_point N q' a b hab φ _
    (fun w h => iotaChar_apply N q' φ w h) x

variable (N q' ℓ : ℕ)

theorem mem_comap_heckeConj_subgroupOf (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) (hℓq' : ¬ q' ∣ ℓ)
    [NeZero ℓ] (x : ↥(heckeUpper N ℓ)) :
    x ∈ ((Gamma0 (N * q')).subgroupOf (Gamma0 N)).comap (heckeConj N ℓ)
      ↔ ((N * q' : ℕ) : ℤ) ∣ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  have hc : (((heckeConj N ℓ x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (ℓ : ℤ) := by
    rw [coe_heckeConj]
    rfl
  have hNc : ((N : ℕ) : ℤ) ∣ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp (x : Gamma0 N).2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp this
  have hcopNq : IsCoprime ((N : ℕ) : ℤ) ((q' : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((hq'.coprime_iff_not_dvd.mpr hq'N).symm)
  have hcopqℓ : IsCoprime ((q' : ℕ) : ℤ) ((ℓ : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (hq'.coprime_iff_not_dvd.mpr hℓq')
  constructor
  · intro hx
    have hmem : ((heckeConj N ℓ x : Gamma0 N) : SL(2, ℤ)) ∈ Gamma0 (N * q') :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hx)
    have hdvd : ((N * q' : ℕ) : ℤ) ∣
        (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (ℓ : ℤ) := by
      rw [← hc]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hmem)
    have hq'c : ((q' : ℕ) : ℤ) ∣ (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      refine hcopqℓ.dvd_of_dvd_mul_right ?_
      refine dvd_trans ?_ hdvd
      push_cast
      exact Dvd.intro_left _ rfl
    have : ((N : ℕ) : ℤ) * ((q' : ℕ) : ℤ) ∣
        (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
      hcopNq.mul_dvd hNc hq'c
    simpa [Nat.cast_mul] using this
  · intro hdvd
    refine Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    refine Gamma0_mem.mpr ?_
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    rw [hc]
    exact Dvd.dvd.mul_right hdvd _

theorem surj_quotMap_heckeConj_subgroupOf (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (hℓq' : ¬ q' ∣ ℓ) [NeZero N] [NeZero ℓ] :
    Function.Surjective
      (quotMap ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) (heckeConj N ℓ)) := by
  intro y
  induction y using Quotient.inductionOn' with
  | h g =>
    set a := (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 with ha
    set c := (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 with hcdef
    have hNc : ((N : ℕ) : ℤ) ∣ c := by
      have := Gamma0_mem.mp g.2
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp this
    obtain ⟨c₀, hc₀⟩ := hNc
    by_cases hq'a : ((q' : ℕ) : ℤ) ∣ a
    ·
      have hcop : IsCoprime ((q' : ℕ) : ℤ) (((ℓ : ℕ) : ℤ) * ((N : ℕ) : ℤ)) := by
        refine IsCoprime.mul_right ?_ ?_
        · exact Nat.isCoprime_iff_coprime.mpr (hq'.coprime_iff_not_dvd.mpr hℓq')
        · exact Nat.isCoprime_iff_coprime.mpr (hq'.coprime_iff_not_dvd.mpr hq'N)
      obtain ⟨s, m', hsm⟩ := hcop

      have hdet : Matrix.det !![(q' : ℤ) * s, (ℓ : ℤ); (N : ℤ) * (-m'), 1] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hsm
      have hxΓ : (⟨!![(q' : ℤ) * s, (ℓ : ℤ); (N : ℤ) * (-m'), 1], hdet⟩ : SL(2, ℤ))
          ∈ Gamma0 N := by
        refine Gamma0_mem.mpr ?_
        show (((N : ℤ) * (-m') : ℤ) : ZMod N) = 0
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨-m', rfl⟩
      have hxU : (⟨(⟨!![(q' : ℤ) * s, (ℓ : ℤ); (N : ℤ) * (-m'), 1], hdet⟩ : SL(2, ℤ)),
          hxΓ⟩ : Gamma0 N) ∈ heckeUpper N ℓ := by
        refine (mem_heckeUpper N ℓ).mpr ⟨1, ?_⟩
        show (ℓ : ℤ) = (ℓ : ℤ) * 1
        ring
      refine ⟨Quotient.mk'' ⟨_, hxU⟩, ?_⟩
      show quotMap _ _ ((⟨⟨_, hxΓ⟩, hxU⟩ : ↥(heckeUpper N ℓ)) :
        ↥(heckeUpper N ℓ) ⧸ _) = _
      rw [quotMap_mk]
      refine (QuotientGroup.eq).mpr ?_
      refine Subgroup.mem_subgroupOf.mpr ?_
      refine Gamma0_mem.mpr ?_
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
      obtain ⟨α, hα⟩ := hq'a
      have hentry : ((((heckeConj N ℓ ⟨⟨_, hxΓ⟩, hxU⟩ : Gamma0 N)⁻¹ * g : Gamma0 N) :
          SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
          = -((N : ℤ) * (-m') * (ℓ : ℤ)) * a + ((q' : ℤ) * s) * c := by
        rw [show (((heckeConj N ℓ ⟨⟨_, hxΓ⟩, hxU⟩ : Gamma0 N)⁻¹ * g : Gamma0 N) : SL(2, ℤ))
            = ((heckeConj N ℓ ⟨⟨_, hxΓ⟩, hxU⟩ : Gamma0 N) : SL(2, ℤ))⁻¹ * (g : SL(2, ℤ))
          from rfl]
        rw [coe_heckeConj]
        rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
        show (!![1, -(ℓ : ℤ) / (ℓ : ℤ); -((N : ℤ) * (-m') * (ℓ : ℤ)), (q' : ℤ) * s] *
          ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = _
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hcdef]
      rw [hentry, hα, hc₀]
      exact ⟨m' * (ℓ : ℤ) * α + s * c₀, by push_cast; ring⟩
    ·
      have hcop : IsCoprime (((N : ℕ) : ℤ) * ((ℓ : ℕ) : ℤ) * a) ((q' : ℕ) : ℤ) := by
        refine IsCoprime.mul_left (IsCoprime.mul_left ?_ ?_) ?_
        · exact (Nat.isCoprime_iff_coprime.mpr (hq'.coprime_iff_not_dvd.mpr hq'N)).symm
        · exact (Nat.isCoprime_iff_coprime.mpr (hq'.coprime_iff_not_dvd.mpr hℓq')).symm
        · have hq'abs : ¬ q' ∣ a.natAbs := fun h => hq'a (Int.natCast_dvd.mpr h)
          have : IsCoprime ((q' : ℕ) : ℤ) a := by
            rw [Int.isCoprime_iff_gcd_eq_one]
            show (Int.natAbs ((q' : ℕ) : ℤ)).gcd a.natAbs = 1
            rw [Int.natAbs_natCast]
            exact (hq'.coprime_iff_not_dvd.mpr hq'abs)
          exact this.symm
      obtain ⟨u, v, huv⟩ := hcop

      have hdet : Matrix.det !![(1 : ℤ), 0; (N : ℤ) * (u * (N : ℤ) * c₀), 1] = 1 := by
        rw [Matrix.det_fin_two_of]
        ring
      have hxΓ : (⟨!![(1 : ℤ), 0; (N : ℤ) * (u * (N : ℤ) * c₀), 1], hdet⟩ : SL(2, ℤ))
          ∈ Gamma0 N := by
        refine Gamma0_mem.mpr ?_
        show ((((N : ℤ) * (u * (N : ℤ) * c₀)) : ℤ) : ZMod N) = 0
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨u * (N : ℤ) * c₀, rfl⟩
      have hxU : (⟨(⟨!![(1 : ℤ), 0; (N : ℤ) * (u * (N : ℤ) * c₀), 1], hdet⟩ : SL(2, ℤ)),
          hxΓ⟩ : Gamma0 N) ∈ heckeUpper N ℓ := by
        refine (mem_heckeUpper N ℓ).mpr ⟨0, ?_⟩
        show (0 : ℤ) = (ℓ : ℤ) * 0
        ring
      refine ⟨Quotient.mk'' ⟨_, hxU⟩, ?_⟩
      show quotMap _ _ ((⟨⟨_, hxΓ⟩, hxU⟩ : ↥(heckeUpper N ℓ)) :
        ↥(heckeUpper N ℓ) ⧸ _) = _
      rw [quotMap_mk]
      refine (QuotientGroup.eq).mpr ?_
      refine Subgroup.mem_subgroupOf.mpr ?_
      refine Gamma0_mem.mpr ?_
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
      have hentry : ((((heckeConj N ℓ ⟨⟨_, hxΓ⟩, hxU⟩ : Gamma0 N)⁻¹ * g : Gamma0 N) :
          SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
          = -((N : ℤ) * (u * (N : ℤ) * c₀) * (ℓ : ℤ)) * a + 1 * c := by
        rw [show (((heckeConj N ℓ ⟨⟨_, hxΓ⟩, hxU⟩ : Gamma0 N)⁻¹ * g : Gamma0 N) : SL(2, ℤ))
            = ((heckeConj N ℓ ⟨⟨_, hxΓ⟩, hxU⟩ : Gamma0 N) : SL(2, ℤ))⁻¹ * (g : SL(2, ℤ))
          from rfl]
        rw [coe_heckeConj]
        rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
        show (!![1, -(0 : ℤ) / (ℓ : ℤ); -((N : ℤ) * (u * (N : ℤ) * c₀) * (ℓ : ℤ)), 1] *
          ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = _
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hcdef]
      rw [hentry, hc₀]
      exact ⟨c₀ * v, by push_cast; linear_combination (-(N : ℤ) * c₀) * huv⟩

theorem iotaChar_eq_pullback_equiv (φ : Additive (Gamma0 (N * q')) →+ ℤ) :
    iotaChar N q' φ = pullbackHom
      ((Subgroup.subgroupOfEquivOfLe (Ihara.Gamma0_mul_le N q')).toMonoidHom) φ := by
  ext j
  rfl

theorem meet_subgroups_eq (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) (hℓq' : ¬ q' ∣ ℓ)
    [NeZero ℓ] :
    (((Gamma0 (N * q')).subgroupOf (Gamma0 N)).comap (heckeConj N ℓ)).map
        (heckeUpper N ℓ).subtype
      = ((heckeUpper (N * q') ℓ).comap
          (Subgroup.subgroupOfEquivOfLe (Ihara.Gamma0_mul_le N q')).toMonoidHom).map
          ((Gamma0 (N * q')).subgroupOf (Gamma0 N)).subtype := by
  ext g
  constructor
  · rintro ⟨x, hxJ, rfl⟩
    have hdvdc : ((N * q' : ℕ) : ℤ) ∣
        (((x : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
      (mem_comap_heckeConj_subgroupOf N q' ℓ hq' hq'N hℓq' x).mp hxJ
    have hgK : ((heckeUpper N ℓ).subtype x : Gamma0 N)
        ∈ (Gamma0 (N * q')).subgroupOf (Gamma0 N) := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      refine Gamma0_mem.mpr ?_
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvdc
    refine ⟨⟨(heckeUpper N ℓ).subtype x, hgK⟩, ?_, rfl⟩
    show Subgroup.subgroupOfEquivOfLe (Ihara.Gamma0_mul_le N q')
        ⟨(heckeUpper N ℓ).subtype x, hgK⟩ ∈ heckeUpper (N * q') ℓ
    refine (mem_heckeUpper (N * q') ℓ).mpr ?_
    exact (mem_heckeUpper N ℓ).mp x.2
  · rintro ⟨y, hyJ, rfl⟩
    have hyU : (((Gamma0 (N * q')).subgroupOf (Gamma0 N)).subtype y : Gamma0 N)
        ∈ heckeUpper N ℓ := by
      refine (mem_heckeUpper N ℓ).mpr ?_
      exact (mem_heckeUpper (N * q') ℓ).mp hyJ
    refine ⟨⟨_, hyU⟩, ?_, rfl⟩
    refine (mem_comap_heckeConj_subgroupOf N q' ℓ hq' hq'N hℓq' _).mpr ?_
    have := Gamma0_mem.mp ((Subgroup.mem_subgroupOf.mp y.2))
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

theorem coresHom_iotaChar_heckeOperatorHom_comm (hq' : q'.Prime) (hq'N : ¬ q' ∣ N)
    (hℓq' : ¬ q' ∣ ℓ) [NeZero N] [NeZero q'] [NeZero ℓ]
    (φ : Additive (Gamma0 (N * q')) →+ ℤ) (g : Gamma0 N) :
    coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N))
        (iotaChar N q' (heckeOperatorHom (N * q') ℓ ℤ φ)) (Additive.ofMul g)
      = heckeOperatorHom N ℓ ℤ
        (coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) (iotaChar N q' φ))
        (Additive.ofMul g) := by
  classical
  haveI hNq'nz : NeZero (N * q') := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q')⟩
  set K := (Gamma0 (N * q')).subgroupOf (Gamma0 N) with hK
  set κ := heckeConj N ℓ with hκ
  set ê := (Subgroup.subgroupOfEquivOfLe (Ihara.Gamma0_mul_le N q')).toMonoidHom with hê

  haveI hJ₁FI : (K.comap κ).FiniteIndex :=
    finiteIndex_comap_of_surjQuot K κ
      (surj_quotMap_heckeConj_subgroupOf N q' ℓ hq' hq'N hℓq')
  haveI hJ₂FI : ((heckeUpper (N * q') ℓ).comap ê).FiniteIndex :=
    finiteIndex_comap_of_surjQuot (heckeUpper (N * q') ℓ) ê
      (surj_quotMap_of_surjective _ _
        (Subgroup.subgroupOfEquivOfLe (Ihara.Gamma0_mul_le N q')).surjective)
  haveI hM₁FI : ((K.comap κ).map (heckeUpper N ℓ).subtype).FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  haveI hM₂FI : (((heckeUpper (N * q') ℓ).comap ê).map K.subtype).FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

  have hpullκ : pullbackHom κ (coresHom K (iotaChar N q' φ))
      = coresHom (K.comap κ) ((iotaChar N q' φ).comp (AddMonoidHom.mk'
          (fun j => Additive.ofMul (⟨κ (Additive.toMul j : ↥(K.comap κ)),
            (Additive.toMul j).2⟩ : ↥K))
          (fun c d => by
            rw [← ofMul_mul]
            exact congrArg Additive.ofMul (Subtype.ext
              (map_mul κ ((Additive.toMul c : ↥(K.comap κ)) : ↥(heckeUpper N ℓ))
                ((Additive.toMul d : ↥(K.comap κ)) : ↥(heckeUpper N ℓ))))))) := by
    ext j
    exact coresHom_comp_apply K κ
      (surj_quotMap_heckeConj_subgroupOf N q' ℓ hq' hq'N hℓq')
      (iotaChar N q' φ) (Additive.toMul j)
  have hRHS : heckeOperatorHom N ℓ ℤ (coresHom K (iotaChar N q' φ)) (Additive.ofMul g)
      = coresHom ((K.comap κ).map (heckeUpper N ℓ).subtype)
          (pullbackHom (mapDown (heckeUpper N ℓ) (K.comap κ))
            ((iotaChar N q' φ).comp (AddMonoidHom.mk'
              (fun j => Additive.ofMul (⟨κ (Additive.toMul j : ↥(K.comap κ)),
                (Additive.toMul j).2⟩ : ↥K))
              (fun c d => by
                rw [← ofMul_mul]
                exact congrArg Additive.ofMul (Subtype.ext
                  (map_mul κ ((Additive.toMul c : ↥(K.comap κ)) : ↥(heckeUpper N ℓ))
                    ((Additive.toMul d : ↥(K.comap κ)) : ↥(heckeUpper N ℓ))))))))
          (Additive.ofMul g) := by
    show coresHom (heckeUpper N ℓ) (pullbackHom κ (coresHom K (iotaChar N q' φ)))
        (Additive.ofMul g) = _
    rw [hpullκ]
    exact coresHom_trans (heckeUpper N ℓ) (K.comap κ) _ g

  have hpullê : iotaChar N q' (heckeOperatorHom (N * q') ℓ ℤ φ)
      = coresHom ((heckeUpper (N * q') ℓ).comap ê)
          ((pullbackHom (heckeConj (N * q') ℓ) φ).comp (AddMonoidHom.mk'
            (fun j => Additive.ofMul (⟨ê (Additive.toMul j :
                ↥((heckeUpper (N * q') ℓ).comap ê)),
              (Additive.toMul j).2⟩ : ↥(heckeUpper (N * q') ℓ)))
            (fun c d => by
              rw [← ofMul_mul]
              exact congrArg Additive.ofMul (Subtype.ext
                (map_mul ê ((Additive.toMul c :
                    ↥((heckeUpper (N * q') ℓ).comap ê)) : ↥K)
                  ((Additive.toMul d :
                    ↥((heckeUpper (N * q') ℓ).comap ê)) : ↥K)))))) := by
    ext j
    exact coresHom_comp_apply (heckeUpper (N * q') ℓ) ê
      (surj_quotMap_of_surjective _ _
        (Subgroup.subgroupOfEquivOfLe (Ihara.Gamma0_mul_le N q')).surjective)
      (pullbackHom (heckeConj (N * q') ℓ) φ) (Additive.toMul j)
  have hLHS : coresHom K (iotaChar N q' (heckeOperatorHom (N * q') ℓ ℤ φ)) (Additive.ofMul g)
      = coresHom (((heckeUpper (N * q') ℓ).comap ê).map K.subtype)
          (pullbackHom (mapDown K ((heckeUpper (N * q') ℓ).comap ê))
            ((pullbackHom (heckeConj (N * q') ℓ) φ).comp (AddMonoidHom.mk'
              (fun j => Additive.ofMul (⟨ê (Additive.toMul j :
                  ↥((heckeUpper (N * q') ℓ).comap ê)),
                (Additive.toMul j).2⟩ : ↥(heckeUpper (N * q') ℓ)))
              (fun c d => by
                rw [← ofMul_mul]
                exact congrArg Additive.ofMul (Subtype.ext
                  (map_mul ê ((Additive.toMul c :
                      ↥((heckeUpper (N * q') ℓ).comap ê)) : ↥K)
                    ((Additive.toMul d :
                      ↥((heckeUpper (N * q') ℓ).comap ê)) : ↥K)))))))
          (Additive.ofMul g) :=
    (congrArg (fun ψ => coresHom K ψ (Additive.ofMul g)) hpullê).trans
      (coresHom_trans K ((heckeUpper (N * q') ℓ).comap ê) _ g)

  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  refine coresHom_congr (meet_subgroups_eq N q' ℓ hq' hq'N hℓq').symm _ _
    (fun w h₁ => ?_) (Additive.ofMul g)
  exact congrArg φ (congrArg Additive.ofMul (Subtype.ext (Subtype.ext rfl)))

end Gamma0Side

end INHHBZ
p2m_reactivate "P2MW.S_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm.INHHBZ"

theorem solution (N q' : ℕ) [NeZero N] [NeZero q']
    (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
      ∀ x : Additive (Gamma0 (N * q')) →+ ℤ,
        degeneracyTransfer₀ N q' ℤ hq' hq'N (heckeOperatorHom (N * q') ℓ ℤ x) =
          heckeOperatorHom N ℓ ℤ (degeneracyTransfer₀ N q' ℤ hq' hq'N x) := by
  intro ℓ _ hℓ hℓN x
  have hq'ℓ : ¬ q' ∣ ℓ := by
    intro h
    exact hℓN ((Nat.prime_dvd_prime_iff_eq hq' hℓ).mp h ▸ dvd_mul_left q' N)
  have hA : ∀ ψ : Additive (Gamma0 (N * q')) →+ ℤ,
      degeneracyTransfer₀ N q' ℤ hq' hq'N ψ
        = coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) (INHHBZ.iotaChar N q' ψ) := by
    intro ψ
    refine AddMonoidHom.ext fun y => ?_
    exact INHHBZ.degeneracyTransfer₀Aux_eq_coresHom_iotaChar N q'
      (Int.gcdA (q' : ℤ) (N : ℤ)) (-Int.gcdB (q' : ℤ) (N : ℤ))
      (bezout_of_prime_not_dvd N q' hq' hq'N) ψ y
  calc degeneracyTransfer₀ N q' ℤ hq' hq'N (heckeOperatorHom (N * q') ℓ ℤ x)
      = coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N))
          (INHHBZ.iotaChar N q' (heckeOperatorHom (N * q') ℓ ℤ x)) :=
        hA (heckeOperatorHom (N * q') ℓ ℤ x)
    _ = heckeOperatorHom N ℓ ℤ
          (coresHom ((Gamma0 (N * q')).subgroupOf (Gamma0 N)) (INHHBZ.iotaChar N q' x)) := by
        refine AddMonoidHom.ext fun y => ?_
        exact INHHBZ.coresHom_iotaChar_heckeOperatorHom_comm N q' ℓ hq' hq'N hq'ℓ x
          (Additive.toMul y)
    _ = heckeOperatorHom N ℓ ℤ (degeneracyTransfer₀ N q' ℤ hq' hq'N x) :=
        congrArg (heckeOperatorHom N ℓ ℤ) (hA x).symm

end S_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm
end P2MW
export P2MW.S_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm (solution)
