-- Prove2me | solution 1 for HeckeCohomology.commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3933a562-c4dd-5dab-82e8-d2c421076375

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import Definitions.Def_GroupCohomology_DClassCoeff
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_HeckeCohomology_heckeH1_eq_of_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid

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
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal"

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
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal"

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
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal"

end D1Chi
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

namespace D1Chi

section SA

open CongruenceSubgroup
open scoped MatrixGroups

theorem diag_mul_conjUpperMat (ℓ : ℕ) (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    !![(ℓ : ℤ), 0; 0, 1] * ((CohCarrier.conjUpperMat ℓ A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (A : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by
  have h01 : (ℓ : ℤ) * (A 0 1 / (ℓ : ℤ)) = A 0 1 := Int.mul_ediv_cancel' h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, h01, mul_comm]

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

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

end SA
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

end D1Chi
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

set_option autoImplicit false

open groupCohomology

namespace HTDChi

open D1Chi

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) {K : Subgroup G} (φ : K →* G) (a : V →ₗ[k] V)

def Dop (θ : G →* G) (b : V →ₗ[k] V) (f : G → V) : G → V := fun γ => b (f (θ γ))

variable [K.FiniteIndex]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem Dop_TR (θ : G ≃* G) (hθK : ∀ x : G, x ∈ K ↔ θ x ∈ K)
    (b : V →ₗ[k] V) (hb : ∀ (g : G) (v : V), b (ρ (θ g) v) = ρ g (b v))
    (ha : ∀ (s : K) (v : V), a (ρ (φ s) v) = ρ s (a v))
    (τ : G) (hτ : ∀ s : K, φ ⟨θ s, (hθK s).mp s.2⟩ = τ * θ (φ s) * τ⁻¹)
    (hba : ∀ v : V, b (a v) = a (b (ρ τ⁻¹ v)))
    (f : G → V) (hf : ∀ x y : G, f (x * y) = f x + ρ x (f y))
    (T : Transversal K) :
    ∃ (T' : Transversal K) (u : V), ∀ γ : G,
      Dop (θ : G →* G) b (TR ρ φ a T f) γ = TR ρ φ a T' (Dop (θ : G →* G) b f) γ + (u - ρ γ u) := by
  classical

  have hwd : ∀ x y : G, (QuotientGroup.rightRel K) x y → (QuotientGroup.rightRel K) (θ x) (θ y) := by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact (hθK _).mp h
  have hwd' : ∀ x y : G, (QuotientGroup.rightRel K) x y → (QuotientGroup.rightRel K) (θ.symm x) (θ.symm y) := by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    rw [hθK, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact h
  let Θ : RQ K ≃ RQ K :=
    { toFun := Quotient.map' θ hwd
      invFun := Quotient.map' θ.symm hwd'
      left_inv := fun q => Quotient.inductionOn' q fun x => by
        show (Quotient.mk'' (θ.symm (θ x)) : RQ K) = Quotient.mk'' x
        rw [MulEquiv.symm_apply_apply]
      right_inv := fun q => Quotient.inductionOn' q fun x => by
        show (Quotient.mk'' (θ (θ.symm x)) : RQ K) = Quotient.mk'' x
        rw [MulEquiv.apply_symm_apply] }
  have hΘ : ∀ x : G, Θ (Quotient.mk'' x) = Quotient.mk'' (θ x) := fun x => rfl
  have hΘmul : ∀ (q : RQ K) (γ : G), Θ (HeckeCohomology.mulRight K γ q) = HeckeCohomology.mulRight K (θ γ) (Θ q) := by
    intro q γ
    induction q using Quotient.inductionOn' with
    | h x => show (Quotient.mk'' (θ (x * γ)) : RQ K) = Quotient.mk'' (θ x * θ γ); rw [map_mul]

  let T' : Transversal K :=
    { R := fun q => θ.symm (T.R (Θ q))
      hR := fun q => by
        have h1 : (Quotient.mk'' (θ.symm (T.R (Θ q))) : RQ K) = Θ.symm (Quotient.mk'' (T.R (Θ q))) := rfl
        rw [h1, T.hR, Equiv.symm_apply_apply] }
  have hslip : ∀ (q : RQ K) (γ : G), θ (T'.slip q γ : G) = (T.slip (Θ q) (θ γ) : G) := by
    intro q γ
    simp only [Transversal.coe_slip, T', map_mul, map_inv, MulEquiv.apply_symm_apply, hΘmul]

  let w : V := b (a (f τ))
  refine ⟨T', ∑ q, ρ (T'.R q)⁻¹ w, fun γ => ?_⟩

  have hf1 : f 1 = 0 := by have := hf 1 1; simp at this; exact this
  have hfinv : ∀ x : G, f x⁻¹ = - ρ x⁻¹ (f x) := fun x => by
    have := hf x⁻¹ x
    rw [inv_mul_cancel, hf1] at this
    exact eq_neg_of_add_eq_zero_left this.symm

  have hL : Dop (θ : G →* G) b (TR ρ φ a T f) γ = ∑ q, b (ρ (T.R (Θ q))⁻¹ (a (f (φ (T.slip (Θ q) (θ γ)))))) := by
    simp only [Dop, TR, map_sum, MulEquiv.coe_toMonoidHom]
    exact (Fintype.sum_equiv Θ _ _ fun q => rfl).symm
  rw [hL]
  have hterm : ∀ q, b (ρ (T.R (Θ q))⁻¹ (a (f (φ (T.slip (Θ q) (θ γ)))))) =
      ρ (T'.R q)⁻¹ (a ((Dop (θ : G →* G) b f) (φ (T'.slip q γ)))) +
        (ρ (T'.R q)⁻¹ w - ρ γ (ρ (T'.R (HeckeCohomology.mulRight K γ q))⁻¹ w)) := by
    intro q

    have h1 : b (ρ (T.R (Θ q))⁻¹ (a (f (φ (T.slip (Θ q) (θ γ)))))) =
        ρ (T'.R q)⁻¹ (b (a (f (φ (T.slip (Θ q) (θ γ)))))) := by
      rw [← hb]
      simp only [T', map_inv, MulEquiv.apply_symm_apply]
    rw [h1]

    have h2 : φ (T.slip (Θ q) (θ γ)) = τ * θ (φ (T'.slip q γ)) * τ⁻¹ := by
      rw [← hτ]
      congr 1
      apply Subtype.ext
      exact (hslip q γ).symm
    rw [h2]

    have h3 : f (τ * θ (φ (T'.slip q γ)) * τ⁻¹) =
        f τ + ρ τ (f (θ (φ (T'.slip q γ)))) - ρ (τ * θ (φ (T'.slip q γ)) * τ⁻¹) (f τ) := by
      rw [hf, hf, hfinv, map_neg, rho_rho]
      abel
    rw [h3, map_sub, map_add, map_sub, map_add]

    have h4 : b (a (ρ τ (f (θ (φ (T'.slip q γ)))))) = a ((Dop (θ : G →* G) b f) (φ (T'.slip q γ))) := by
      rw [hba, rho_rho, inv_mul_cancel, map_one, Module.End.one_apply]
      rfl

    have h5 : b (a (ρ (τ * θ (φ (T'.slip q γ)) * τ⁻¹) (f τ))) = ρ (T'.slip q γ : G) w := by
      rw [hba, rho_rho]
      have : τ⁻¹ * (τ * θ (φ (T'.slip q γ)) * τ⁻¹) = θ (φ (T'.slip q γ)) * τ⁻¹ := by group
      rw [this, ← rho_rho, hb, ha, ← hba]
    rw [h4, h5, map_sub, map_add]

    have h6 : ρ (T'.R q)⁻¹ (ρ (T'.slip q γ : G) w) = ρ γ (ρ (T'.R (HeckeCohomology.mulRight K γ q))⁻¹ w) := by
      rw [rho_rho, rho_rho, Transversal.coe_slip]
      congr 2
      group
    rw [h6]
    abel
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum, TR]
  rw [show ∑ q, ρ γ (ρ (T'.R (HeckeCohomology.mulRight K γ q))⁻¹ w) = ∑ q, ρ γ (ρ (T'.R q)⁻¹ w) from
    Fintype.sum_equiv (HeckeCohomology.mulRight K γ) _ _ fun _ => rfl]

end HTDChi
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

set_option autoImplicit false

open groupCohomology CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace HTDChi

open D1Chi

section Rep

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

theorem Dop_mem_cocycles₁ (θ : G →* G) (b : A →ₗ[k] A) (hb : ∀ (g : G) (v : A), b (A.ρ (θ g) v) = A.ρ g (b v))
    (f : cocycles₁ A) : Dop θ b f ∈ cocycles₁ A := by
  rw [mem_cocycles₁_iff]
  intro g h
  simp only [Dop, map_mul, (mem_cocycles₁_iff f).1 f.2, map_add, hb]

theorem H1π_Dop_eq_of_sub (θ : G →* G) (b : A →ₗ[k] A) (hb : ∀ (g : G) (v : A), b (A.ρ (θ g) v) = A.ρ g (b v))
    (f g : cocycles₁ A) (h : H1π A f = H1π A g) :
    H1π A ⟨Dop θ b f, Dop_mem_cocycles₁ A θ b hb f⟩ = H1π A ⟨Dop θ b g, Dop_mem_cocycles₁ A θ b hb g⟩ := by
  rw [H1π_eq_iff] at h ⊢
  obtain ⟨v, hv⟩ := h
  refine ⟨b v, funext fun γ => ?_⟩
  have := congrFun hv (θ γ)
  simp only [d₀₁_hom_apply, Pi.sub_apply] at this ⊢
  show A.ρ γ (b v) - b v = b (f (θ γ)) - b (g (θ γ))
  rw [← map_sub b, ← this, map_sub, hb]

theorem heckeH1_top_eq_H1π_Dop (θ : G →* G) (b : A →ₗ[k] A)
    (hψ : HeckeCohomology.IsTwist ⊤ ⊤ ((θ.comp (⊤ : Subgroup G).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _) A b)
    (f : cocycles₁ A) :
    HeckeCohomology.heckeH1 ⊤ ⊤ ((θ.comp (⊤ : Subgroup G).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _) A b hψ (H1π A f) =
      H1π A ⟨Dop θ b f, Dop_mem_cocycles₁ A θ b (fun g v => hψ ⟨g, Subgroup.mem_top g⟩ v) f⟩ := by
  symm
  refine HeckeCohomology.heckeH1_eq_of_section ⊤ ⊤ _ A b hψ (fun _ => 1) (fun _ γ => ⟨γ, Subgroup.mem_top γ⟩)
    (fun q γ => by simp) f _ fun γ => ?_
  haveI : Subsingleton (Quotient (QuotientGroup.rightRel (⊤ : Subgroup G))) := by
    refine ⟨fun x y => ?_⟩
    induction x using Quotient.inductionOn' with
    | h x => induction y using Quotient.inductionOn' with
      | h y => exact Quotient.sound' (by rw [QuotientGroup.rightRel_apply]; exact Subgroup.mem_top _)
  rw [Fintype.sum_subsingleton _ (Quotient.mk'' (1 : G))]
  simp only [inv_one, map_one, Module.End.one_apply]
  rfl

variable {K : Subgroup G} [K.FiniteIndex] (φ : K →* G) (a : A →ₗ[k] A)

theorem heckeZ1_eq_TR' (ha : HeckeCohomology.IsTwist ⊤ K (φ.codRestrict ⊤ fun _ => Subgroup.mem_top _) A a)
    (f : cocycles₁ A) (γ : G) :
    (HeckeCohomology.heckeZ1 ⊤ K (φ.codRestrict ⊤ fun _ => Subgroup.mem_top _) A a ha f : G → A) γ =
      TR A.ρ φ a (Transversal.out K) f γ := by
  rw [HeckeCohomology.heckeZ1_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hs : (HeckeCohomology.slip K q γ : G) = ((Transversal.out K).slip q γ : G) := by
    simp only [HeckeCohomology.slip, Transversal.coe_slip, Transversal.out, HeckeCohomology.mulRight_apply]
  have hs' : HeckeCohomology.slip K q γ = (Transversal.out K).slip q γ := Subtype.ext hs
  rw [hs']
  rfl

theorem exists_TR_eq_heckeZ1_add (ha : HeckeCohomology.IsTwist ⊤ K (φ.codRestrict ⊤ fun _ => Subgroup.mem_top _) A a)
    (f : cocycles₁ A) (T : Transversal K) :
    ∃ u : A, ∀ γ : G, TR A.ρ φ a T f γ =
      (HeckeCohomology.heckeZ1 ⊤ K (φ.codRestrict ⊤ fun _ => Subgroup.mem_top _) A a ha f : G → A) γ + (u - A.ρ γ u) := by
  obtain ⟨u, hu⟩ := TR_sub_TR (ρ := A.ρ) (φ := φ) (a := a) (K := K) (fun s v => ha s v) f
    (fun x y => by rw [(mem_cocycles₁_iff f).1 f.2]; abel) (Transversal.out K) T
  refine ⟨u, fun γ => ?_⟩
  rw [heckeZ1_eq_TR', ← hu γ]
  abel

end Rep
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

section Concrete

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]

set_option quotPrecheck false in
local notation "Γ₁" => ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))

def conjEquiv (σ : Gamma0 N) : Γ₁ ≃* Γ₁ :=
  MonoidHom.toMulEquiv (CohCarrier.conjHom N ⊥ σ) (CohCarrier.conjHom N ⊥ σ⁻¹)
    (by ext γ; simp [CohCarrier.conjHom, mul_assoc])
    (by ext γ; simp [CohCarrier.conjHom, mul_assoc])

theorem conjEquiv_apply (σ : Gamma0 N) (γ : Γ₁) :
    ((conjEquiv N σ γ : Γ₁) : SL(2, ℤ)) = (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ := rfl

theorem coe_conjEquiv (σ : Gamma0 N) : (conjEquiv N σ : Γ₁ →* Γ₁) = CohCarrier.conjHom N ⊥ σ := rfl

variable (σ : Gamma0 N) (hσ : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) (σ : SL(2, ℤ)) = 1)

include hσ in
theorem dvd_b : (ℓ : ℤ) ∣ (σ : SL(2, ℤ)) 0 1 := by
  have h := congrArg (fun A : SL(2, ZMod ℓ) => A 0 1) hσ
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast,
    Matrix.SpecialLinearGroup.coe_one, ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

include hσ in

theorem mem_upper_iff (x : Γ₁) : x ∈ CohCarrier.GammaHUpper N ⊥ ℓ ↔ conjEquiv N σ x ∈ CohCarrier.GammaHUpper N ⊥ ℓ := by
  simp only [CohCarrier.GammaHUpper, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper]
  have key : ∀ A : SL(2, ℤ), ((A 0 1 : ℤ) : ZMod ℓ) = (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) A) 0 1 :=
    fun A => rfl
  rw [key, key]
  show _ ↔ (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) ((σ : SL(2, ℤ)) * (x : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹)) 0 1 = 0
  rw [map_mul, map_mul, map_inv, hσ, one_mul, inv_one, mul_one]

noncomputable def sigma' : SL(2, ℤ) := CohCarrier.conjUpperMat ℓ (σ : SL(2, ℤ)) (dvd_b N ℓ σ hσ)

theorem sigma'_mem_Gamma0 : sigma' N ℓ σ hσ ∈ Gamma0 N := by
  rw [Gamma0_mem, sigma', CohCarrier.conjUpperMat_apply_10, Int.cast_mul, Gamma0_mem.mp σ.2, zero_mul]

theorem tau_mem : sigma' N ℓ σ hσ * (σ : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ) := by
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : sigma' N ℓ σ hσ * (σ : SL(2, ℤ))⁻¹ ∈ Gamma0 N :=
    (Gamma0 N).mul_mem (sigma'_mem_Gamma0 N ℓ σ hσ) ((Gamma0 N).inv_mem σ.2)
  refine ⟨h0, ?_⟩
  rw [Subgroup.mem_bot]

  have h1 : CohCarrier.gamma0Units N ⟨_, h0⟩ =
      CohCarrier.gamma0Units N ⟨sigma' N ℓ σ hσ, sigma'_mem_Gamma0 N ℓ σ hσ⟩ * (CohCarrier.gamma0Units N σ)⁻¹ := by
    rw [← map_inv, ← map_mul]; rfl
  have h2 : CohCarrier.gamma0Units N ⟨sigma' N ℓ σ hσ, sigma'_mem_Gamma0 N ℓ σ hσ⟩ = CohCarrier.gamma0Units N σ := by
    apply Units.ext
    simp only [CohCarrier.val_gamma0Units, Gamma0Map]
    show (((sigma' N ℓ σ hσ) 1 1 : ℤ) : ZMod N) = (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)
    rw [sigma', CohCarrier.conjUpperMat_apply_11]
  rw [h1, h2, mul_inv_cancel]

noncomputable def tau : Γ₁ := ⟨sigma' N ℓ σ hσ * (σ : SL(2, ℤ))⁻¹, tau_mem N ℓ σ hσ⟩

theorem conjUpperMat_inv (A : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) (hA' : (ℓ : ℤ) ∣ A⁻¹ 0 1) :
    CohCarrier.conjUpperMat ℓ A⁻¹ hA' = (CohCarrier.conjUpperMat ℓ A hA)⁻¹ := by
  have h1 : (ℓ : ℤ) ∣ (A * A⁻¹) 0 1 := by rw [mul_inv_cancel]; simp
  have hmul := CohCarrier.conjUpperMat_mul ℓ A A⁻¹ hA hA' h1
  have hone : CohCarrier.conjUpperMat ℓ (A * A⁻¹) h1 = 1 := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    have : A * A⁻¹ = 1 := mul_inv_cancel A
    fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjUpperMat, this]
  rw [hone] at hmul
  exact (eq_inv_of_mul_eq_one_right hmul.symm)

theorem conjL_conj (s : ↥(CohCarrier.GammaHUpper N ⊥ ℓ)) :
    (CohCarrier.conjL N ⊥ ℓ ⟨conjEquiv N σ s, (mem_upper_iff N ℓ σ hσ s).mp s.2⟩ : Γ₁) =
      tau N ℓ σ hσ * conjEquiv N σ (CohCarrier.conjL N ⊥ ℓ s) * (tau N ℓ σ hσ)⁻¹ := by
  apply Subtype.ext
  have hb := dvd_b N ℓ σ hσ
  have hbinv : (ℓ : ℤ) ∣ (σ : SL(2, ℤ))⁻¹ 0 1 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simpa using hb
  have hs := CohCarrier.dvd_of_mem_GammaHUpper N ⊥ ℓ s
  have hσs : (ℓ : ℤ) ∣ ((σ : SL(2, ℤ)) * ((s : Γ₁) : SL(2, ℤ))) 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, (Matrix.two_mul_expl (σ : SL(2, ℤ)).1 ((s : Γ₁) : SL(2, ℤ)).1).2.1]
    exact dvd_add (hs.mul_left _) (hb.mul_right _)
  have hall : (ℓ : ℤ) ∣ ((σ : SL(2, ℤ)) * ((s : Γ₁) : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, (Matrix.two_mul_expl ((σ : SL(2, ℤ)) * ((s : Γ₁) : SL(2, ℤ))).1 ((σ : SL(2, ℤ))⁻¹).1).2.1]
    exact dvd_add (hbinv.mul_left _) (hσs.mul_right _)
  show CohCarrier.conjUpperMat ℓ ((σ : SL(2, ℤ)) * ((s : Γ₁) : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) hall =
    (sigma' N ℓ σ hσ * (σ : SL(2, ℤ))⁻¹) *
      ((σ : SL(2, ℤ)) * CohCarrier.conjUpperMat ℓ ((s : Γ₁) : SL(2, ℤ)) hs * (σ : SL(2, ℤ))⁻¹) *
      (sigma' N ℓ σ hσ * (σ : SL(2, ℤ))⁻¹)⁻¹
  rw [CohCarrier.conjUpperMat_mul ℓ _ _ hσs hbinv, CohCarrier.conjUpperMat_mul ℓ _ _ hb hs,
    conjUpperMat_inv ℓ _ hb hbinv, sigma']
  group

theorem diag_mul_sigma' :
    !![(ℓ : ℤ), 0; 0, 1] * ((sigma' N ℓ σ hσ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] :=
  diag_mul_conjUpperMat ℓ _ _

end Concrete
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

end HTDChi
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

set_option autoImplicit false

open groupCohomology CongruenceSubgroup HeckeCohomology
open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace HTDChi

open D1Chi

section Main

variable (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)

set_option quotPrecheck false in
local notation "Γ₁" => ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))

def emb (g : Gamma0 N) : M := ⟨((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hΓ _ g.2⟩

theorem emb_mul (g h : Gamma0 N) : emb N M hΓ (g * h) = emb N M hΓ g * emb N M hΓ h := by
  apply Subtype.ext
  simp [emb]

theorem rho'_emb_mul (g h : Gamma0 N) : ρ' (emb N M hΓ (g * h)) = ρ' (emb N M hΓ g) * ρ' (emb N M hΓ h) := by
  rw [emb_mul, map_mul]

theorem rho'_emb_inv_mul (g : Gamma0 N) (v : X) : ρ' (emb N M hΓ g⁻¹) (ρ' (emb N M hΓ g) v) = v := by
  rw [← Module.End.mul_apply, ← rho'_emb_mul, inv_mul_cancel]
  have : emb N M hΓ 1 = 1 := Subtype.ext (by simp [emb])
  rw [this, map_one, Module.End.one_apply]

theorem rho'_emb_mul_inv (g : Gamma0 N) (v : X) : ρ' (emb N M hΓ g) (ρ' (emb N M hΓ g⁻¹) v) = v := by
  simpa using rho'_emb_inv_mul N κ X M hΓ ρ' g⁻¹ v

include hρ' in
theorem rho_eq (γ : Γ₁) : X.ρ γ = ρ' (emb N M hΓ (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) ⊥) γ)) :=
  hρ' γ

include hρ' in

theorem hb_of (σ : Gamma0 N) (g : Γ₁) (v : X) :
    ρ' (emb N M hΓ σ⁻¹) (X.ρ (conjEquiv N σ g) v) = X.ρ g (ρ' (emb N M hΓ σ⁻¹) v) := by
  rw [rho_eq N κ X M hΓ ρ' hρ' (conjEquiv N σ g), rho_eq N κ X M hΓ ρ' hρ' g]
  have : Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) ⊥) (conjEquiv N σ g) =
      σ * Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) ⊥) g * σ⁻¹ := rfl
  rw [this, rho'_emb_mul, rho'_emb_mul, Module.End.mul_apply, Module.End.mul_apply, rho'_emb_inv_mul]

variable (ℓ : ℕ) [NeZero ℓ] (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M)

include hρ' in

theorem hba_of (σ : Gamma0 N) (hσ : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) (σ : SL(2, ℤ)) = 1) (v : X) :
    ρ' (emb N M hΓ σ⁻¹) (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩ v) =
      ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩ (ρ' (emb N M hΓ σ⁻¹) (X.ρ (tau N ℓ σ hσ)⁻¹ v)) := by

  let σ'g : Gamma0 N := ⟨sigma' N ℓ σ hσ, sigma'_mem_Gamma0 N ℓ σ hσ⟩
  have hτ : Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) ⊥) (tau N ℓ σ hσ)⁻¹ = σ * σ'g⁻¹ := by
    apply Subtype.ext
    show (sigma' N ℓ σ hσ * (σ : SL(2, ℤ))⁻¹)⁻¹ = (σ : SL(2, ℤ)) * (sigma' N ℓ σ hσ)⁻¹
    rw [mul_inv_rev, inv_inv]
  rw [rho_eq N κ X M hΓ ρ' hρ' , hτ]
  have e1 : ρ' (emb N M hΓ σ⁻¹) (ρ' (emb N M hΓ (σ * σ'g⁻¹)) v) = ρ' (emb N M hΓ σ'g⁻¹) v := by
    rw [← Module.End.mul_apply, ← rho'_emb_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  show ((σ⁻¹ : Gamma0 N) : SL(2, ℤ)).1 * !![(ℓ : ℤ), 0; 0, 1] = !![(ℓ : ℤ), 0; 0, 1] * ((σ'g⁻¹ : Gamma0 N) : SL(2, ℤ)).1
  have h1 : ((σ⁻¹ : Gamma0 N) : SL(2, ℤ)).1 * ((σ : Gamma0 N) : SL(2, ℤ)).1 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]; simp
  have h2 : ((σ'g : Gamma0 N) : SL(2, ℤ)).1 * ((σ'g⁻¹ : Gamma0 N) : SL(2, ℤ)).1 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]; simp
  have h3 := diag_mul_sigma' N ℓ σ hσ
  calc ((σ⁻¹ : Gamma0 N) : SL(2, ℤ)).1 * !![(ℓ : ℤ), 0; 0, 1]
      = ((σ⁻¹ : Gamma0 N) : SL(2, ℤ)).1 * !![(ℓ : ℤ), 0; 0, 1] * (((σ'g : Gamma0 N) : SL(2, ℤ)).1 * ((σ'g⁻¹ : Gamma0 N) : SL(2, ℤ)).1) := by
        rw [h2, mul_one]
    _ = ((σ⁻¹ : Gamma0 N) : SL(2, ℤ)).1 * (!![(ℓ : ℤ), 0; 0, 1] * ((σ'g : Gamma0 N) : SL(2, ℤ)).1) * ((σ'g⁻¹ : Gamma0 N) : SL(2, ℤ)).1 := by
        simp only [mul_assoc]
    _ = ((σ⁻¹ : Gamma0 N) : SL(2, ℤ)).1 * (((σ : Gamma0 N) : SL(2, ℤ)).1 * !![(ℓ : ℤ), 0; 0, 1]) * ((σ'g⁻¹ : Gamma0 N) : SL(2, ℤ)).1 := by
        rw [show ((σ'g : Gamma0 N) : SL(2, ℤ)).1 = ((sigma' N ℓ σ hσ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) from rfl, h3]
    _ = !![(ℓ : ℤ), 0; 0, 1] * ((σ'g⁻¹ : Gamma0 N) : SL(2, ℤ)).1 := by
        rw [← mul_assoc, h1, one_mul]

variable [Fact ℓ.Prime]

include hρ' in

theorem H1π_Dop_reduce (σ σd : Gamma0 N) (γ₀ : Γ₁) (hσ : σ = Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) ⊥) γ₀ * σd)
    (f : cocycles₁ X) :
    H1π X ⟨Dop (CohCarrier.conjHom N ⊥ σ) (ρ' (emb N M hΓ σ⁻¹)) f,
        Dop_mem_cocycles₁ X _ _ (fun g v => hb_of N κ X M hΓ ρ' hρ' σ g v) f⟩ =
      H1π X ⟨Dop (CohCarrier.conjHom N ⊥ σd) (ρ' (emb N M hΓ σd⁻¹)) f,
        Dop_mem_cocycles₁ X _ _ (fun g v => hb_of N κ X M hΓ ρ' hρ' σd g v) f⟩ := by
  rw [H1π_eq_iff]

  let b : X →ₗ[κ] X := ρ' (emb N M hΓ σd⁻¹)
  let v : X := X.ρ γ₀⁻¹ (f γ₀)
  refine ⟨-(b v), funext fun γ => ?_⟩
  have hz : ∀ x y : Γ₁, f (x * y) = f x + X.ρ x (f y) := fun x y => by rw [(mem_cocycles₁_iff f).1 f.2]; abel
  have hzinv : ∀ x : Γ₁, f x⁻¹ = - X.ρ x⁻¹ (f x) := fun x => by
    have := hz x⁻¹ x
    rw [inv_mul_cancel, cocycles₁_map_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hconj : CohCarrier.conjHom N ⊥ σ γ = γ₀ * CohCarrier.conjHom N ⊥ σd γ * γ₀⁻¹ := by
    apply Subtype.ext
    simp only [CohCarrier.conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, hσ,
      Subgroup.coe_inclusion, mul_inv_rev, mul_assoc]
  have hbσ : ∀ w : X, ρ' (emb N M hΓ σ⁻¹) w = b (X.ρ γ₀⁻¹ w) := by
    intro w
    rw [rho_eq N κ X M hΓ ρ' hρ', ← Module.End.mul_apply, ← rho'_emb_mul]
    congr 2
    rw [hσ, mul_inv_rev]
    rfl
  have hb : ∀ (g : Γ₁) (w : X), b (X.ρ (CohCarrier.conjHom N ⊥ σd g) w) = X.ρ g (b w) :=
    fun g w => hb_of N κ X M hΓ ρ' hρ' σd g w
  show X.ρ γ (-(b v)) - (-(b v)) =
    ρ' (emb N M hΓ σ⁻¹) (f (CohCarrier.conjHom N ⊥ σ γ)) - b (f (CohCarrier.conjHom N ⊥ σd γ))
  rw [hconj, hbσ, hz, hz, hzinv]
  simp only [map_add, map_neg, rho_rho, inv_mul_cancel, map_one, Module.End.one_apply]
  have : γ₀⁻¹ * (γ₀ * CohCarrier.conjHom N ⊥ σd γ * γ₀⁻¹) = CohCarrier.conjHom N ⊥ σd γ * γ₀⁻¹ := by group
  rw [this, ← rho_rho, hb]
  simp only [v, b]
  abel

end Main
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

end HTDChi
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

set_option autoImplicit false

open groupCohomology CongruenceSubgroup HeckeCohomology
open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace HTDChi

open D1Chi

theorem main
    (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M)
    (hφ : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X
        (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩))
    (σ : CongruenceSubgroup.Gamma0 N)
    (hψ : HeckeCohomology.IsTwist ⊤ ⊤
            (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
            X (ρ' ⟨(((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹).2⟩)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    Commute (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X _ hφ)
      (HeckeCohomology.heckeH1 ⊤ ⊤
          (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
          X _ hψ) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero N := ⟨fun h => hℓN (h ▸ dvd_zero ℓ)⟩

  obtain ⟨γ₀, hγ₀⟩ := exists_gammaH_bot_map_eq N ℓ hℓN
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) (σ : SL(2, ℤ)))
  let ι : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) →* Gamma0 N :=
    Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) ⊥)
  let σd : Gamma0 N := (ι γ₀)⁻¹ * σ
  have hσd : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) (σd : SL(2, ℤ)) = 1 := by
    show Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) ((γ₀ : SL(2, ℤ))⁻¹ * (σ : SL(2, ℤ))) = 1
    rw [map_mul, map_inv, hγ₀, inv_mul_cancel]
  have hσ : σ = ι γ₀ * σd := by simp [σd]

  let K := CohCarrier.GammaHUpper N ⊥ ℓ
  let φ : ↥K →* ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) := CohCarrier.conjL N ⊥ ℓ
  let a : X →ₗ[κ] X := ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩
  let b : X →ₗ[κ] X := ρ' (emb N M hΓ σd⁻¹)
  let θ := conjEquiv N σd
  have ha : ∀ (s : ↥K) (v : X), a (X.ρ (φ s) v) = X.ρ s (a v) := fun s v => hφ s v
  have hb : ∀ (g : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) (v : X), b (X.ρ (θ g) v) = X.ρ g (b v) :=
    fun g v => hb_of N κ X M hΓ ρ' hρ' σd g v

  have eD : ∀ g : cocycles₁ X,
      heckeH1 ⊤ ⊤ (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
          fun _ => Subgroup.mem_top _) X _ hψ (H1π X g) =
        H1π X ⟨Dop (CohCarrier.conjHom N ⊥ σd) b g, Dop_mem_cocycles₁ X _ _ hb g⟩ := by
    intro g
    rw [heckeH1_top_eq_H1π_Dop X (CohCarrier.conjHom N ⊥ σ) _ hψ g]
    exact H1π_Dop_reduce N κ X M hΓ ρ' hρ' σ σd γ₀ hσ g
  have eT : ∀ g : cocycles₁ X,
      heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X _ hφ (H1π X g) =
        H1π X (heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X _ hφ g) :=
    fun g => heckeH1_H1π _ _ _ _ _ hφ g

  show _ * _ = _ * _
  apply LinearMap.ext
  intro x
  induction x using H1_induction_on with
  | h f =>
    rw [Module.End.mul_apply, Module.End.mul_apply, eD, eT, eT, eD]

    obtain ⟨T', u₁, hu₁⟩ := Dop_TR X.ρ φ a θ (fun x => mem_upper_iff N ℓ σd hσd x) b hb ha (tau N ℓ σd hσd)
      (fun s => conjL_conj N ℓ σd hσd s) (fun v => hba_of N κ X M hΓ ρ' hρ' ℓ hℓM σd hσd v)
      f (fun x y => by rw [(mem_cocycles₁_iff f).1 f.2]; abel) (Transversal.out K)
    let g' : cocycles₁ X := ⟨Dop (CohCarrier.conjHom N ⊥ σd) b f, Dop_mem_cocycles₁ X _ _ hb f⟩
    obtain ⟨u₂, hu₂⟩ := exists_TR_eq_heckeZ1_add X φ a hφ g' T'
    rw [H1π_eq_iff]
    refine ⟨u₁ + u₂, funext fun γ => ?_⟩
    simp only [d₀₁_hom_apply, Pi.sub_apply]
    show X.ρ γ (u₁ + u₂) - (u₁ + u₂) =
      (heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X a hφ g' : _ → X) γ -
        b ((heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X a hφ f : _ → X) (CohCarrier.conjHom N ⊥ σd γ))
    have e1 : (heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X a hφ f : _ → X) (CohCarrier.conjHom N ⊥ σd γ) =
        TR X.ρ φ a (Transversal.out K) f (θ γ) := heckeZ1_eq_TR' X φ a hφ f _
    have e2 := hu₁ γ
    have e3 : TR X.ρ φ a T' g' γ =
        (heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X a hφ g' : _ → X) γ + (u₂ - X.ρ γ u₂) := hu₂ γ
    rw [e1]
    change X.ρ γ (u₁ + u₂) - (u₁ + u₂) = _ - Dop (θ : _ →* _) b (TR X.ρ φ a (Transversal.out K) f) γ
    rw [e2]
    change X.ρ γ (u₁ + u₂) - (u₁ + u₂) =
      (heckeZ1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (cTop N ⊥ ℓ) X a hφ g' : _ → X) γ - (TR X.ρ φ a T' g' γ + (u₁ - X.ρ γ u₁))
    rw [e3, map_add]
    abel

end HTDChi
p2m_reactivate "P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi.Transversal P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.D1Chi"

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
    (hφ : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X
        (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩))
    (σ : CongruenceSubgroup.Gamma0 N)
    (hψ : HeckeCohomology.IsTwist ⊤ ⊤
            (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
            X (ρ' ⟨(((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹).2⟩)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    Commute (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X _ hφ)
      (HeckeCohomology.heckeH1 ⊤ ⊤
          (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
          X _ hψ) :=
  HTDChi.main N κ X M hΓ ρ' hρ' ℓ hℓ hℓN hℓM hφ σ hψ

end S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
end P2MW
export P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid (solution)
