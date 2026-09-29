-- Prove2me | solution 1 for HeckeEis.heckeOperatorHom_pullback_iota0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b9b5a250-cc5d-5f83-8a42-059616361353

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_IharaIota
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_heckeOperatorHom_pullback_iota0

set_option autoImplicit false

open CongruenceSubgroup Matrix

open scoped MatrixGroups

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeConjMat_apply_zero_zero heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeConjMat_apply_one_one heckeUpper mem_heckeUpper heckeConj transferAux coe_transferAux coresHom coresHom_apply pullbackHom pullbackHom_apply heckeOperatorHom"
p2m_open "HeckeEis"

section Repr

variable {G : Type*} [Group G] (H : Subgroup G)
variable {A : Type*} [AddCommGroup A]
variable {I : Type*}

def transferAuxRepr (e : I ≃ G ⧸ H) (ρ : I → G) (hρ : ∀ i, ((ρ i : G) : G ⧸ H) = e i)
    (g : G) (i : I) : H :=
  ⟨(ρ (e.symm (g • e i)))⁻¹ * (g * ρ i), by
    refine QuotientGroup.eq.mp ?_
    have h1 : ((ρ (e.symm (g • e i)) : G) : G ⧸ H) = g • e i := by
      rw [hρ, e.apply_symm_apply]
    have h2 : ((g * ρ i : G) : G ⧸ H) = g • e i := by
      rw [show ((g * ρ i : G) : G ⧸ H) = g • ((ρ i : G) : G ⧸ H) from rfl, hρ]
    exact h1.trans h2.symm⟩

@[scoped simp]
theorem coe_transferAuxRepr (e : I ≃ G ⧸ H) (ρ : I → G)
    (hρ : ∀ i, ((ρ i : G) : G ⧸ H) = e i) (g : G) (i : I) :
    (transferAuxRepr H e ρ hρ g i : G) = (ρ (e.symm (g • e i)))⁻¹ * (g * ρ i) :=
  rfl

noncomputable def reprDefect (e : I ≃ G ⧸ H) (ρ : I → G)
    (hρ : ∀ i, ((ρ i : G) : G ⧸ H) = e i) (i : I) : H :=
  ⟨(e i).out⁻¹ * ρ i, QuotientGroup.eq.mp ((QuotientGroup.out_eq' (e i)).trans (hρ i).symm)⟩

@[scoped simp]
theorem coe_reprDefect (e : I ≃ G ⧸ H) (ρ : I → G)
    (hρ : ∀ i, ((ρ i : G) : G ⧸ H) = e i) (i : I) :
    (reprDefect H e ρ hρ i : G) = (e i).out⁻¹ * ρ i :=
  rfl

theorem transferAuxRepr_eq (e : I ≃ G ⧸ H) (ρ : I → G)
    (hρ : ∀ i, ((ρ i : G) : G ⧸ H) = e i) (g : G) (i : I) :
    transferAuxRepr H e ρ hρ g i =
      (reprDefect H e ρ hρ (e.symm (g • e i)))⁻¹ *
        (transferAux H g (e i) * reprDefect H e ρ hρ i) := by
  refine Subtype.ext ?_
  push_cast [coe_transferAuxRepr, coe_transferAux, coe_reprDefect]
  rw [e.apply_symm_apply]
  group

variable [H.FiniteIndex]

theorem coresHom_apply_repr [Fintype I] (e : I ≃ G ⧸ H) (ρ : I → G)
    (hρ : ∀ i, ((ρ i : G) : G ⧸ H) = e i) (φ : Additive H →+ A) (g : G) :
    coresHom H φ (Additive.ofMul g) =
      ∑ i : I, φ (Additive.ofMul (transferAuxRepr H e ρ hρ g i)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  have hperm : Function.Bijective (fun i : I => e.symm (g • e i)) :=
    (e.symm.bijective.comp (MulAction.bijective g)).comp e.bijective
  have hsum : ∑ i : I, φ (Additive.ofMul (reprDefect H e ρ hρ (e.symm (g • e i)))) =
      ∑ i : I, φ (Additive.ofMul (reprDefect H e ρ hρ i)) :=
    Fintype.sum_bijective _ hperm _ _ fun i => rfl
  calc coresHom H φ (Additive.ofMul g)
      = ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) := coresHom_apply H φ g
    _ = ∑ i : I, φ (Additive.ofMul (transferAux H g (e i))) :=
        (Fintype.sum_equiv e _ _ fun i => rfl).symm
    _ = ∑ i : I, φ (Additive.ofMul (transferAuxRepr H e ρ hρ g i)) := by
        simp_rw [transferAuxRepr_eq H e ρ hρ g, ofMul_mul, ofMul_inv, map_add, map_neg]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum]
        abel

end Repr

section Transitivity

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]
variable (H : Subgroup G) (KG : Subgroup G) (K : Subgroup H)

noncomputable def coresTransIndex (qr : (G ⧸ H) × (H ⧸ K)) : G ⧸ KG :=
  ((qr.1.out * (qr.2.out : G) : G) : G ⧸ KG)

theorem coresTransIndex_injective (hle : KG ≤ H) (hmem : ∀ h : H, (h : G) ∈ KG ↔ h ∈ K) :
    Function.Injective (coresTransIndex H KG K) := by
  rintro ⟨q₁, r₁⟩ ⟨q₂, r₂⟩ hqr
  rw [coresTransIndex, coresTransIndex, QuotientGroup.eq] at hqr
  have hH : (q₁.out)⁻¹ * q₂.out ∈ H := by
    have key : ((r₁.out : G)) * ((q₁.out * (r₁.out : G))⁻¹ * (q₂.out * (r₂.out : G))) *
        ((r₂.out : G))⁻¹ = (q₁.out)⁻¹ * q₂.out := by group
    rw [← key]
    exact mul_mem (mul_mem r₁.out.2 (hle hqr)) (inv_mem r₂.out.2)
  have hq : q₁ = q₂ := by
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.mpr hH
  subst hq
  have hKG : ((r₁.out⁻¹ * r₂.out : H) : G) ∈ KG := by
    have key : (q₁.out * (r₁.out : G))⁻¹ * (q₁.out * (r₂.out : G)) =
        ((r₁.out⁻¹ * r₂.out : H) : G) := by
      push_cast
      group
    rw [← key]
    exact hqr
  have hr : r₁ = r₂ := by
    rw [← QuotientGroup.out_eq' r₁, ← QuotientGroup.out_eq' r₂]
    exact QuotientGroup.eq.mpr ((hmem _).mp hKG)
  rw [hr]

theorem coresTransIndex_surjective (hmem : ∀ h : H, (h : G) ∈ KG ↔ h ∈ K) :
    Function.Surjective (coresTransIndex H KG K) := by
  intro s
  set q : G ⧸ H := ((s.out : G) : G ⧸ H) with hq
  have hmemH : (q.out)⁻¹ * s.out ∈ H :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  set r : H ⧸ K := ((⟨q.out⁻¹ * s.out, hmemH⟩ : H) : H ⧸ K) with hr
  refine ⟨(q, r), ?_⟩
  have hrK : (⟨q.out⁻¹ * s.out, hmemH⟩ : H)⁻¹ * r.out ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' r).symm
  have hKG : ((((⟨q.out⁻¹ * s.out, hmemH⟩ : H)⁻¹ * r.out : H)) : G) ∈ KG := (hmem _).mpr hrK
  rw [coresTransIndex, ← QuotientGroup.out_eq' s, eq_comm, QuotientGroup.eq]
  convert hKG using 1
  push_cast
  group

theorem coresTransIndex_smul (hmem : ∀ h : H, (h : G) ∈ KG ↔ h ∈ K) (g : G) (q : G ⧸ H)
    (r : H ⧸ K) :
    g • coresTransIndex H KG K (q, r) =
      coresTransIndex H KG K (g • q, transferAux H g q • r) := by
  show ((g * (q.out * ((r.out : H) : G)) : G) : G ⧸ KG) = _
  rw [coresTransIndex, eq_comm, QuotientGroup.eq]
  have hmemK : (((transferAux H g q • r).out⁻¹ *
      (transferAux H g q * r.out) : H) : G) ∈ KG :=
    (hmem _).mpr (transferAux K (transferAux H g q) r).2
  convert hmemK using 1
  push_cast [coe_transferAux]
  group

theorem coresHom_coresHom_apply [H.FiniteIndex] [KG.FiniteIndex] [K.FiniteIndex]
    (hle : KG ≤ H) (hmem : ∀ h : H, (h : G) ∈ KG ↔ h ∈ K)
    (ι : K →* KG) (hι : ∀ k : K, ((ι k : G)) = (((k : H)) : G))
    (φ : Additive KG →+ A) (g : G) :
    coresHom KG φ (Additive.ofMul g) =
      coresHom H (coresHom K (pullbackHom ι φ)) (Additive.ofMul g) := by
  letI := H.fintypeQuotientOfFiniteIndex
  letI := K.fintypeQuotientOfFiniteIndex
  letI : Fintype ((G ⧸ H) × (H ⧸ K)) := instFintypeProd _ _
  set e : (G ⧸ H) × (H ⧸ K) ≃ G ⧸ KG :=
    Equiv.ofBijective (coresTransIndex H KG K)
      ⟨coresTransIndex_injective H KG K hle hmem, coresTransIndex_surjective H KG K hmem⟩
    with he
  have hee : ∀ qr, e qr = coresTransIndex H KG K qr := fun _ => rfl
  set ρ : (G ⧸ H) × (H ⧸ K) → G := fun qr => qr.1.out * ((qr.2.out : H) : G) with hρdef
  have hρ : ∀ qr, ((ρ qr : G) : G ⧸ KG) = e qr := fun _ => rfl
  rw [coresHom_apply_repr KG e ρ hρ φ g]
  calc ∑ qr : (G ⧸ H) × (H ⧸ K), φ (Additive.ofMul (transferAuxRepr KG e ρ hρ g qr))
      = ∑ q : G ⧸ H, ∑ r : H ⧸ K,
          φ (Additive.ofMul (transferAuxRepr KG e ρ hρ g (q, r))) :=
        Fintype.sum_prod_type _
    _ = ∑ q : G ⧸ H, ∑ r : H ⧸ K,
          (pullbackHom ι φ) (Additive.ofMul (transferAux K (transferAux H g q) r)) := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
        have hidx : e.symm (g • e (q, r)) = (g • q, transferAux H g q • r) := by
          rw [Equiv.symm_apply_eq, hee, hee]
          exact coresTransIndex_smul H KG K hmem g q r
        rw [pullbackHom_apply]
        refine congrArg (φ ∘ Additive.ofMul) (Subtype.ext ?_)
        rw [coe_transferAuxRepr, hidx, hι]
        simp only [hρdef]
        push_cast [coe_transferAux]
        group
    _ = coresHom H (coresHom K (pullbackHom ι φ)) (Additive.ofMul g) := by
        rw [coresHom_apply]
        exact Finset.sum_congr rfl fun q _ => (coresHom_apply K _ _).symm

end Transitivity

section Mackey

variable {G : Type*} [Group G] {H : Type*} [Group H] {A : Type*} [AddCommGroup A]
variable (f : H →* G) (H' : Subgroup G) (K : Subgroup H)

noncomputable def mackeyIndex (r : H ⧸ K) : G ⧸ H' :=
  ((f (r.out : H) : G) : G ⧸ H')

theorem mackeyIndex_injective (hmem : ∀ h : H, f h ∈ H' ↔ h ∈ K) :
    Function.Injective (mackeyIndex f H' K) := by
  intro r₁ r₂ hr
  rw [mackeyIndex, mackeyIndex, QuotientGroup.eq, ← map_inv, ← map_mul] at hr
  rw [← QuotientGroup.out_eq' r₁, ← QuotientGroup.out_eq' r₂]
  exact QuotientGroup.eq.mpr ((hmem _).mp hr)

theorem mackeyIndex_surjective (hmem : ∀ h : H, f h ∈ H' ↔ h ∈ K)
    (hsurj : ∀ γ : G, ∃ h : H, (f h)⁻¹ * γ ∈ H') :
    Function.Surjective (mackeyIndex f H' K) := by
  intro s
  obtain ⟨h, hh⟩ := hsurj s.out
  refine ⟨((h : H) : H ⧸ K), ?_⟩
  rw [mackeyIndex, ← QuotientGroup.out_eq' s, QuotientGroup.eq]
  have hK : ((h : H) : H ⧸ K).out⁻¹ * h ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' ((h : H) : H ⧸ K))
  have key : (f (((h : H) : H ⧸ K).out))⁻¹ * s.out =
      (f (((h : H) : H ⧸ K).out⁻¹ * h)) * ((f h)⁻¹ * s.out) := by
    rw [map_mul, map_inv]
    group
  rw [key]
  exact mul_mem ((hmem _).mpr hK) hh

theorem mackeyIndex_smul (hmem : ∀ h : H, f h ∈ H' ↔ h ∈ K) (h : H) (r : H ⧸ K) :
    f h • mackeyIndex f H' K r = mackeyIndex f H' K (h • r) := by
  show ((f h * f (r.out : H) : G) : G ⧸ H') = ((f ((h • r).out : H) : G) : G ⧸ H')
  rw [eq_comm, QuotientGroup.eq, ← map_mul, ← map_inv, ← map_mul]
  exact (hmem _).mpr (transferAux K h r).2

theorem coresHom_apply_comp [H'.FiniteIndex] [K.FiniteIndex]
    (hmem : ∀ h : H, f h ∈ H' ↔ h ∈ K)
    (hsurj : ∀ γ : G, ∃ h : H, (f h)⁻¹ * γ ∈ H')
    (fK : K →* H') (hfK : ∀ k : K, ((fK k : G)) = f ((k : H)))
    (ψ : Additive H' →+ A) (h : H) :
    coresHom H' ψ (Additive.ofMul (f h)) =
      coresHom K (pullbackHom fK ψ) (Additive.ofMul h) := by
  letI := K.fintypeQuotientOfFiniteIndex
  set e : H ⧸ K ≃ G ⧸ H' :=
    Equiv.ofBijective (mackeyIndex f H' K)
      ⟨mackeyIndex_injective f H' K hmem, mackeyIndex_surjective f H' K hmem hsurj⟩
    with he
  have hee : ∀ r, e r = mackeyIndex f H' K r := fun _ => rfl
  set ρ : H ⧸ K → G := fun r => f (r.out : H) with hρdef
  have hρ : ∀ r, ((ρ r : G) : G ⧸ H') = e r := fun _ => rfl
  rw [coresHom_apply_repr H' e ρ hρ ψ (f h), coresHom_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hidx : e.symm (f h • e r) = h • r := by
    rw [Equiv.symm_apply_eq, hee, hee]
    exact mackeyIndex_smul f H' K hmem h r
  rw [pullbackHom_apply]
  refine congrArg (ψ ∘ Additive.ofMul) (Subtype.ext ?_)
  rw [coe_transferAuxRepr, hidx, hfK]
  show _ = f ((transferAux K h r : K) : H)
  push_cast [coe_transferAux]
  rw [map_mul, map_mul, map_inv]

end Mackey

section Witnesses

variable (N q : ℕ)

def levelUnipotent (β : ℤ) : Gamma0 (N * q) :=
  ⟨⟨!![1, β; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod (N * q)) = 0
    exact Int.cast_zero⟩

@[scoped simp]
theorem levelUnipotent_apply_zero_one (β : ℤ) :
    ((levelUnipotent N q β : Gamma0 (N * q)) : SL(2, ℤ)) 0 1 = β :=
  rfl

@[scoped simp]
theorem levelUnipotent_apply_one_one (β : ℤ) :
    ((levelUnipotent N q β : Gamma0 (N * q)) : SL(2, ℤ)) 1 1 = 1 :=
  rfl

variable (ℓ : ℕ)

def levelBezout (u v w : ℤ) (huvw : u * (ℓ : ℤ) + v * (w * ((N : ℤ) * (q : ℤ))) = 1) :
    Gamma0 (N * q) :=
  ⟨⟨!![u, v; -(w * ((N : ℤ) * (q : ℤ))), (ℓ : ℤ)], by
      rw [Matrix.det_fin_two_of]; linear_combination huvw⟩, by
    rw [Gamma0_mem]
    show ((-(w * ((N : ℤ) * (q : ℤ))) : ℤ) : ZMod (N * q)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-w, by push_cast; ring⟩⟩

@[scoped simp]
theorem levelBezout_apply_zero_one (u v w : ℤ)
    (huvw : u * (ℓ : ℤ) + v * (w * ((N : ℤ) * (q : ℤ))) = 1) :
    ((levelBezout N q ℓ u v w huvw : Gamma0 (N * q)) : SL(2, ℤ)) 0 1 = v :=
  rfl

@[scoped simp]
theorem levelBezout_apply_one_one (u v w : ℤ)
    (huvw : u * (ℓ : ℤ) + v * (w * ((N : ℤ) * (q : ℤ))) = 1) :
    ((levelBezout N q ℓ u v w huvw : Gamma0 (N * q)) : SL(2, ℤ)) 1 1 = (ℓ : ℤ) :=
  rfl

end Witnesses

section Detection

variable (N q : ℕ)

theorem iota0_inv_mul_apply (h : Gamma0 (N * q)) (γ : Gamma0 N) :
    (((Ihara.ι₀ N q h)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) 0 1 =
      ((h : SL(2, ℤ)) 1 1) * ((γ : SL(2, ℤ)) 0 1) -
        ((h : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) := by
  have h1 : (((Ihara.ι₀ N q h)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) =
      ((h : SL(2, ℤ)))⁻¹ * (γ : SL(2, ℤ)) := by
    push_cast [Ihara.coe_iota0]
    rfl
  rw [h1]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

end Detection

section Iota0

variable (N q ℓ : ℕ)

theorem iota0_mem_heckeUpper_iff (h : Gamma0 (N * q)) :
    Ihara.ι₀ N q h ∈ heckeUpper N ℓ ↔ h ∈ heckeUpper (N * q) ℓ := by
  rw [mem_heckeUpper, mem_heckeUpper, Ihara.coe_iota0]

variable [NeZero ℓ]

def iota0Restrict : heckeUpper (N * q) ℓ →* heckeUpper N ℓ :=
  ((Ihara.ι₀ N q).comp (heckeUpper (N * q) ℓ).subtype).codRestrict (heckeUpper N ℓ)
    fun k => (iota0_mem_heckeUpper_iff N q ℓ k).mpr k.2

omit [NeZero ℓ] in
@[scoped simp]
theorem coe_iota0Restrict (k : heckeUpper (N * q) ℓ) :
    ((iota0Restrict N q ℓ k : heckeUpper N ℓ) : Gamma0 N) = Ihara.ι₀ N q (k : Gamma0 (N * q)) :=
  rfl

theorem heckeConj_iota0Restrict (k : heckeUpper (N * q) ℓ) :
    heckeConj N ℓ (iota0Restrict N q ℓ k) =
      Ihara.ι₀ N q (heckeConj (N * q) ℓ k) :=
  rfl

omit [NeZero ℓ] in

theorem iota0_coset_surjective (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (γ : Gamma0 N) :
    ∃ h : Gamma0 (N * q), (Ihara.ι₀ N q h)⁻¹ * γ ∈ heckeUpper N ℓ := by
  by_cases hd : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 1
  ·
    have hN : ¬ (ℓ : ℤ) ∣ (N : ℤ) := by
      intro hdN
      have hc : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        hdN.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp γ.2)
      have hdet : (γ : SL(2, ℤ)) 0 0 * (γ : SL(2, ℤ)) 1 1 -
          (γ : SL(2, ℤ)) 0 1 * (γ : SL(2, ℤ)) 1 0 = 1 := by
        rw [← Matrix.det_fin_two]
        exact (γ : SL(2, ℤ)).2
      have hone : (ℓ : ℤ) ∣ 1 := by
        rw [← hdet]; exact dvd_sub (hd.mul_left _) (hc.mul_left _)
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
    have hcop : IsCoprime ((ℓ : ℕ) : ℤ) (((N * q : ℕ) : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
      exact Nat.Coprime.mul_right
        ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdvd =>
          hN (Int.natCast_dvd_natCast.mpr hdvd))
        ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq)
    obtain ⟨u, v, huv⟩ := hcop
    have huv' : u * (ℓ : ℤ) + v * (1 * ((N : ℤ) * (q : ℤ))) = 1 := by
      push_cast at huv ⊢; linarith
    refine ⟨levelBezout N q ℓ u v 1 huv', (mem_heckeUpper N ℓ).mpr ?_⟩
    rw [iota0_inv_mul_apply, levelBezout_apply_one_one, levelBezout_apply_zero_one]
    exact dvd_sub (dvd_mul_right _ _) (hd.mul_left _)
  ·
    have hcop : IsCoprime ((ℓ : ℤ)) ((γ : SL(2, ℤ)) 1 1) :=
      (Nat.prime_iff_prime_int.mp hℓ).coprime_iff_not_dvd.mpr hd
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨levelUnipotent N q ((γ : SL(2, ℤ)) 0 1 * v),
      (mem_heckeUpper N ℓ).mpr ?_⟩
    rw [iota0_inv_mul_apply, levelUnipotent_apply_one_one,
      levelUnipotent_apply_zero_one, one_mul]
    exact ⟨(γ : SL(2, ℤ)) 0 1 * u, by linear_combination (-(γ : SL(2, ℤ)) 0 1) * huv⟩

variable {A : Type*} [AddCommGroup A]

theorem heckeOperatorHom_pullback_iota0_impl (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q)
    (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (Ihara.ι₀ N q) (heckeOperatorHom N ℓ A φ) =
      heckeOperatorHom (N * q) ℓ A (pullbackHom (Ihara.ι₀ N q) φ) := by

  have hinner : pullbackHom (iota0Restrict N q ℓ) (pullbackHom (heckeConj N ℓ) φ) =
      pullbackHom (heckeConj (N * q) ℓ) (pullbackHom (Ihara.ι₀ N q) φ) := by
    refine AddMonoidHom.ext fun kk => ?_
    rw [← ofMul_toMul kk, pullbackHom_apply, pullbackHom_apply, pullbackHom_apply,
      pullbackHom_apply]
    exact congrArg (φ ∘ Additive.ofMul) (heckeConj_iota0Restrict N q ℓ kk.toMul)
  refine AddMonoidHom.ext fun gg => ?_
  rw [← ofMul_toMul gg, pullbackHom_apply]

  rw [show heckeOperatorHom N ℓ A φ =
      coresHom (heckeUpper N ℓ) (pullbackHom (heckeConj N ℓ) φ) from rfl,
    coresHom_apply_comp (Ihara.ι₀ N q) (heckeUpper N ℓ) (heckeUpper (N * q) ℓ)
      (iota0_mem_heckeUpper_iff N q ℓ) (iota0_coset_surjective N q ℓ hℓ hℓq)
      (iota0Restrict N q ℓ) (fun _ => rfl) (pullbackHom (heckeConj N ℓ) φ) gg.toMul,
    hinner]
  rfl

end Iota0

section Iota1

open Ihara

variable (N q ℓ : ℕ)

theorem coe_inv_mul_apply_zero_one {N : ℕ} (δ γ : Gamma0 N) :
    ((δ⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) 0 1 =
      (δ : SL(2, ℤ)) 1 1 * (γ : SL(2, ℤ)) 0 1 - (δ : SL(2, ℤ)) 0 1 * (γ : SL(2, ℤ)) 1 1 := by
  have h1 : ((δ⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) = (δ : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) := rfl
  rw [h1]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem iota1_apply_zero_one (h : Gamma0 (N * q)) :
    ((ι₁ N q h : Gamma0 N) : SL(2, ℤ)) 0 1 = (h : SL(2, ℤ)) 0 1 * (q : ℤ) :=
  rfl

theorem iota1_apply_one_one (h : Gamma0 (N * q)) :
    ((ι₁ N q h : Gamma0 N) : SL(2, ℤ)) 1 1 = (h : SL(2, ℤ)) 1 1 :=
  rfl

theorem iota1_inv_mul_apply (h : Gamma0 (N * q)) (γ : Gamma0 N) :
    (((ι₁ N q h)⁻¹ * γ : Gamma0 N) : SL(2, ℤ)) 0 1 =
      (h : SL(2, ℤ)) 1 1 * (γ : SL(2, ℤ)) 0 1 - (h : SL(2, ℤ)) 0 1 * (q : ℤ) * (γ : SL(2, ℤ)) 1 1 := by
  rw [coe_inv_mul_apply_zero_one, iota1_apply_one_one, iota1_apply_zero_one]

theorem iota1_mem_heckeUpper_of_mem (k : heckeUpper (N * q) ℓ) :
    ι₁ N q (k : Gamma0 (N * q)) ∈ heckeUpper N ℓ := by
  rw [mem_heckeUpper, iota1_apply_zero_one]
  exact Dvd.dvd.mul_right k.2 _

theorem iota1_mem_heckeUpper_iff (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (h : Gamma0 (N * q)) :
    ι₁ N q h ∈ heckeUpper N ℓ ↔ h ∈ heckeUpper (N * q) ℓ := by
  rw [mem_heckeUpper, mem_heckeUpper, iota1_apply_zero_one]
  constructor
  · intro hdvd
    rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_mul.mp hdvd with hb | hq
    · exact hb
    · exact absurd (Int.natCast_dvd_natCast.mp hq) hℓq
  · exact fun hb => hb.mul_right _

def iota1Restrict : heckeUpper (N * q) ℓ →* heckeUpper N ℓ :=
  ((ι₁ N q).comp (heckeUpper (N * q) ℓ).subtype).codRestrict (heckeUpper N ℓ)
    fun k => iota1_mem_heckeUpper_of_mem N q ℓ k

@[scoped simp]
theorem coe_iota1Restrict (k : heckeUpper (N * q) ℓ) :
    ((iota1Restrict N q ℓ k : heckeUpper N ℓ) : Gamma0 N) = ι₁ N q (k : Gamma0 (N * q)) :=
  rfl

theorem heckeConjMat_iota1Mat_comm {ℓ q : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) (hq : (q : ℤ) ≠ 0)
    {g : Matrix (Fin 2) (Fin 2) ℤ} (hb : (ℓ : ℤ) ∣ g 0 1) (hc : (q : ℤ) ∣ g 1 0) :
    heckeConjMat ℓ (iota1Mat q g) = iota1Mat q (heckeConjMat ℓ g) := by
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [heckeConjMat_apply_zero_zero, heckeConjMat_apply_zero_one,
      heckeConjMat_apply_one_zero, heckeConjMat_apply_one_one, iota1Mat_apply_zero_zero,
      iota1Mat_apply_zero_one, iota1Mat_apply_one_zero, iota1Mat_apply_one_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · rw [hb', mul_assoc, Int.mul_ediv_cancel_left _ hℓ, Int.mul_ediv_cancel_left _ hℓ]
  · rw [hc', Int.mul_ediv_cancel_left _ hq, mul_assoc, Int.mul_ediv_cancel_left _ hq]

variable [NeZero ℓ]

theorem heckeConj_iota1Restrict (hq : q ≠ 0) (k : heckeUpper (N * q) ℓ) :
    heckeConj N ℓ (iota1Restrict N q ℓ k) = ι₁ N q (heckeConj (N * q) ℓ k) := by
  refine Subtype.ext (Subtype.ext ?_)
  show heckeConjMat ℓ (iota1Mat q _) = iota1Mat q (heckeConjMat ℓ _)
  exact heckeConjMat_iota1Mat_comm (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
    (Int.natCast_ne_zero.mpr hq) k.2 (q_dvd_entry N q (k : Gamma0 (N * q)))

omit [NeZero ℓ] in

theorem iota1_coset_surjective (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (γ : Gamma0 N) :
    ∃ h : Gamma0 (N * q), (ι₁ N q h)⁻¹ * γ ∈ heckeUpper N ℓ := by
  by_cases hd : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 1
  ·
    have hN : ¬ (ℓ : ℤ) ∣ (N : ℤ) := by
      intro hdN
      have hc : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        hdN.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp γ.2)
      have hdet : (γ : SL(2, ℤ)) 0 0 * (γ : SL(2, ℤ)) 1 1 -
          (γ : SL(2, ℤ)) 0 1 * (γ : SL(2, ℤ)) 1 0 = 1 := by
        rw [← Matrix.det_fin_two]
        exact (γ : SL(2, ℤ)).2
      have hone : (ℓ : ℤ) ∣ 1 := by
        rw [← hdet]
        exact dvd_sub (hd.mul_left _) (hc.mul_left _)
      have hone' : ℓ ∣ 1 := by exact_mod_cast hone
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp hone')
    have hcop : IsCoprime ((ℓ : ℕ) : ℤ) (((N * q : ℕ) : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
      exact Nat.Coprime.mul_right
        ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdvd =>
          hN (Int.natCast_dvd_natCast.mpr hdvd))
        ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓq)
    obtain ⟨u, v, huv⟩ := hcop
    have huv' : u * (ℓ : ℤ) + v * (1 * ((N : ℤ) * (q : ℤ))) = 1 := by
      push_cast at huv ⊢; linarith
    refine ⟨levelBezout N q ℓ u v 1 huv', (mem_heckeUpper N ℓ).mpr ?_⟩
    rw [iota1_inv_mul_apply, levelBezout_apply_one_one, levelBezout_apply_zero_one]
    exact dvd_sub (dvd_mul_right _ _) (hd.mul_left _)
  ·
    have hcop : IsCoprime ((ℓ : ℤ)) ((q : ℤ) * (γ : SL(2, ℤ)) 1 1) :=
      IsCoprime.mul_right
        ((Nat.prime_iff_prime_int.mp hℓ).coprime_iff_not_dvd.mpr
          fun hdvd => hℓq (Int.natCast_dvd_natCast.mp hdvd))
        ((Nat.prime_iff_prime_int.mp hℓ).coprime_iff_not_dvd.mpr hd)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨levelUnipotent N q ((γ : SL(2, ℤ)) 0 1 * v), (mem_heckeUpper N ℓ).mpr ?_⟩
    rw [iota1_inv_mul_apply, levelUnipotent_apply_one_one, levelUnipotent_apply_zero_one, one_mul]
    exact ⟨(γ : SL(2, ℤ)) 0 1 * u, by linear_combination (-(γ : SL(2, ℤ)) 0 1) * huv⟩

variable {A : Type*} [AddCommGroup A]

theorem heckeOperatorHom_pullback_iota1_impl (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q)
    (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (Ihara.ι₁ N q) (heckeOperatorHom N ℓ A φ) =
      heckeOperatorHom (N * q) ℓ A (pullbackHom (Ihara.ι₁ N q) φ) := by
  have hq0 : q ≠ 0 := fun h => hℓq (h ▸ dvd_zero ℓ)

  have hinner : pullbackHom (iota1Restrict N q ℓ) (pullbackHom (heckeConj N ℓ) φ) =
      pullbackHom (heckeConj (N * q) ℓ) (pullbackHom (ι₁ N q) φ) := by
    refine AddMonoidHom.ext fun k => ?_
    rw [← ofMul_toMul k, pullbackHom_apply, pullbackHom_apply, pullbackHom_apply, pullbackHom_apply,
      heckeConj_iota1Restrict N q ℓ hq0]
  refine AddMonoidHom.ext fun x => ?_
  rw [← ofMul_toMul x, pullbackHom_apply]
  show coresHom (heckeUpper N ℓ) (pullbackHom (heckeConj N ℓ) φ) (Additive.ofMul (ι₁ N q x.toMul)) =
    coresHom (heckeUpper (N * q) ℓ) (pullbackHom (heckeConj (N * q) ℓ) (pullbackHom (ι₁ N q) φ))
      (Additive.ofMul x.toMul)
  rw [coresHom_apply_comp (ι₁ N q) (heckeUpper N ℓ) (heckeUpper (N * q) ℓ)
    (iota1_mem_heckeUpper_iff N q ℓ hℓ hℓq) (iota1_coset_surjective N q ℓ hℓ hℓq) (iota1Restrict N q ℓ)
    (fun _ => rfl) (pullbackHom (heckeConj N ℓ) φ) x.toMul, hinner]

end Iota1

end HeckeEis
p2m_reactivate "P2MW.S_HeckeEis_heckeOperatorHom_pullback_iota0.HeckeEis"

open CongruenceSubgroup _root_.HeckeEis _root_.P2MW.S_HeckeEis_heckeOperatorHom_pullback_iota0.HeckeEis in
theorem solution (N q ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (Ihara.ι₀ N q) (heckeOperatorHom N ℓ A φ) =
      heckeOperatorHom (N * q) ℓ A (pullbackHom (Ihara.ι₀ N q) φ) :=
  HeckeEis.heckeOperatorHom_pullback_iota0_impl N q ℓ hℓ hℓq φ

#print axioms solution

end S_HeckeEis_heckeOperatorHom_pullback_iota0
end P2MW
export P2MW.S_HeckeEis_heckeOperatorHom_pullback_iota0 (solution)
