-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4052edc9-6cc9-581e-9e0a-74100afa03e3

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_ModularCurve_index_heckeUpper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1

set_option autoImplicit false

namespace LevelRaise

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

@[scoped simp] theorem coe_heckeZ1 (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    (heckeZ1 ha z : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

theorem unique_of_isCoeffHeckeOnH1 {T T' : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T)
    (hT' : IsCoeffHeckeOnH1 N ℓ ρ a T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨w', hw', hTw'⟩ := hT' z
  rw [hTw, hTw']
  congr 1
  exact Subtype.ext (hw.trans hw'.symm)

theorem coeffH1Mk_eq_iff (z w : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = coeffH1Mk ρ w ↔ (z : Gamma0 N → V) - w ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.eq _).trans Submodule.mem_comap

end Induced

section CorRes

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (H : Subgroup G) [H.FiniteIndex]

noncomputable def tr (g : G) (q : G ⧸ H) : G := (g • q).out⁻¹ * g * q.out

omit [H.FiniteIndex] in
theorem tr_mem (g : G) (q : G ⧸ H) : tr H g q ∈ H := by
  unfold tr
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq']
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  exact MulAction.Quotient.smul_mk H g q.out

omit [H.FiniteIndex] in
theorem out_smul_mul_tr (g : G) (q : G ⧸ H) : (g • q).out * tr H g q = g * q.out := by
  unfold tr
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

omit [H.FiniteIndex] in
theorem sum_smul_eq [Fintype (G ⧸ H)] {M : Type*} [AddCommMonoid M] (g : G) (F : G ⧸ H → M) :
    ∑ q, F (g • q) = ∑ q, F q :=
  Fintype.sum_equiv (MulAction.toPerm g) _ _ fun _ => rfl

theorem index_smul_mem_coeffCoboundaries (ρ : Representation K G V) {z : G → V} (hz : z ∈ coeffCocycles ρ)
    (u : V) (hzH : ∀ t : G, t ∈ H → z t = ρ t u - u) :
    (H.index : K) • z ∈ coeffCoboundaries ρ := by
  classical
  letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  set v : V := ∑ q : G ⧸ H, z q.out with hv
  set v' : V := ∑ q : G ⧸ H, ρ q.out u with hv'
  refine ⟨v' - v, funext fun g => ?_⟩
  simp only [coeffCoboundaryMap_apply, Pi.smul_apply]
  have h1 : ∑ q : G ⧸ H, ρ (g • q).out (z (tr H g q)) = (H.index : K) • z g + (ρ g v - v) := by
    have hq : ∀ q : G ⧸ H, ρ (g • q).out (z (tr H g q)) = z g + ρ g (z q.out) - z (g • q).out := by
      intro q
      have e1 : z ((g • q).out * tr H g q) = z (g • q).out + ρ (g • q).out (z (tr H g q)) := hz _ _
      have e2 : z (g * q.out) = z g + ρ g (z q.out) := hz _ _
      rw [out_smul_mul_tr] at e1
      rw [e2] at e1
      exact eq_sub_of_add_eq' e1.symm
    simp_rw [hq]
    have hcard : Fintype.card (G ⧸ H) = H.index := by rw [Subgroup.index, Nat.card_eq_fintype_card]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, ← map_sum,
      sum_smul_eq H g (fun q => z q.out), ← hv, ← Nat.cast_smul_eq_nsmul K, add_sub_assoc]
  have h2 : ∑ q : G ⧸ H, ρ (g • q).out (z (tr H g q)) = ρ g v' - v' := by
    have hq : ∀ q : G ⧸ H, ρ (g • q).out (z (tr H g q)) = ρ g (ρ q.out u) - ρ (g • q).out u := by
      intro q
      rw [hzH _ (tr_mem H g q), map_sub, ← Module.End.mul_apply, ← map_mul, out_smul_mul_tr, map_mul,
        Module.End.mul_apply]
    simp_rw [hq]
    rw [Finset.sum_sub_distrib, ← map_sum, sum_smul_eq H g (fun q => ρ q.out u), ← hv']
  have h3 : (H.index : K) • z g + (ρ g v - v) = ρ g v' - v' := h1.symm.trans h2
  rw [map_sub]
  have := congrArg (fun w => w - (ρ g v - v)) h3
  simp only [add_sub_cancel_right] at this
  rw [this]
  abel

end CorRes

section Atkin

variable (N : ℕ) [NeZero N]

theorem natCast_N_ne_zero : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)

def wMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; (N : ℤ), 0]

theorem eq_of_mul_wMat_eq {A B : Matrix (Fin 2) (Fin 2) ℤ} (h : A * wMat N = B * wMat N) : A = B := by
  ext i j
  have h0 := congrFun (congrFun h i) 0
  have h1 := congrFun (congrFun h i) 1
  simp only [wMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, zero_add, mul_neg, mul_one, add_zero] at h0 h1
  fin_cases j
  · exact neg_injective h1
  · exact mul_right_cancel₀ (natCast_N_ne_zero N) h0

theorem N_dvd_entry (γ : Gamma0 N) : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)

def atkMat (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 1 1, -(g 1 0 / (N : ℤ)); -((N : ℤ) * g 0 1), g 0 0]

theorem atkMat_mul_wMat {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (N : ℤ) ∣ g 1 0) :
    atkMat N g * wMat N = wMat N * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkMat, wMat, Matrix.mul_apply, Fin.sum_univ_two, Int.ediv_mul_cancel hg, Int.mul_ediv_cancel' hg,
      mul_comm]

theorem atkMat_mul {g h : Matrix (Fin 2) (Fin 2) ℤ} (hg : (N : ℤ) ∣ g 1 0) (hh : (N : ℤ) ∣ h 1 0)
    (hgh : (N : ℤ) ∣ (g * h) 1 0) : atkMat N (g * h) = atkMat N g * atkMat N h := by
  apply eq_of_mul_wMat_eq N
  rw [mul_assoc, atkMat_mul_wMat N hh, ← mul_assoc, atkMat_mul_wMat N hg, mul_assoc, atkMat_mul_wMat N hgh]

omit [NeZero N] in
theorem det_atkMat {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (N : ℤ) ∣ g 1 0) : (atkMat N g).det = g.det := by
  rw [atkMat, Matrix.det_fin_two_of, Matrix.det_fin_two]
  have := Int.ediv_mul_cancel hg
  linear_combination -(g 0 1) * this

theorem atkMat_atkMat {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (N : ℤ) ∣ g 1 0) : atkMat N (atkMat N g) = g := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · show -(-((N : ℤ) * g 0 1) / (N : ℤ)) = g 0 1
    rw [Int.neg_ediv_of_dvd (Dvd.intro _ rfl), neg_neg, Int.mul_ediv_cancel_left _ (natCast_N_ne_zero N)]
  · show -((N : ℤ) * -(g 1 0 / (N : ℤ))) = g 1 0
    rw [mul_neg, neg_neg, Int.mul_ediv_cancel' hg]
  · rfl

def atk (γ : Gamma0 N) : Gamma0 N :=
  ⟨⟨atkMat N ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
      rw [det_atkMat N (N_dvd_entry N γ)]; exact (γ : SL(2, ℤ)).2⟩, by
    rw [Gamma0_mem]
    show (((-((N : ℤ) * (γ : SL(2, ℤ)) 0 1) : ℤ)) : ZMod N) = 0
    simp⟩

@[scoped simp] theorem coe_atk (γ : Gamma0 N) :
    (((atk N γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      atkMat N ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl

def atkHom : Gamma0 N →* Gamma0 N where
  toFun := atk N
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_atk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [atkMat]
  map_mul' γ δ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_atk]
    exact atkMat_mul N (N_dvd_entry N γ) (N_dvd_entry N δ) (N_dvd_entry N (γ * δ))

theorem atkHom_atkHom (γ : Gamma0 N) : atkHom N (atkHom N γ) = γ :=
  Subtype.ext (Subtype.ext (atkMat_atkMat N (N_dvd_entry N γ)))

theorem atkHom_surjective : Function.Surjective (atkHom N) :=
  fun γ => ⟨atkHom N γ, atkHom_atkHom N γ⟩

theorem comap_atkHom_heckeUpper (q : ℕ) :
    (heckeUpper N q).comap (atkHom N) = (Gamma0 (N * q)).subgroupOf (Gamma0 N) := by
  ext γ
  rw [Subgroup.mem_comap, mem_heckeUpper, Subgroup.mem_subgroupOf, Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  show (q : ℤ) ∣ -((γ : SL(2, ℤ)) 1 0 / (N : ℤ)) ↔ ((N * q : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0
  obtain ⟨k, hk⟩ := N_dvd_entry N γ
  rw [hk, Int.mul_ediv_cancel_left _ (natCast_N_ne_zero N), dvd_neg, Nat.cast_mul]
  exact (mul_dvd_mul_iff_left (natCast_N_ne_zero N)).symm

theorem index_subgroupOf_mul {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N) :
    ((Gamma0 (N * q)).subgroupOf (Gamma0 N)).index = q + 1 := by
  rw [← comap_atkHom_heckeUpper, Subgroup.index_comap_of_surjective _ (atkHom_surjective N),
    ModularCurve.index_heckeUpper hq hqN]

end Atkin

section Restrict

variable (N q : ℕ)

theorem gamma0_mul_le : Gamma0 (N * q) ≤ Gamma0 N := by
  intro g hg
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
  exact (show (N : ℤ) ∣ ((N * q : ℕ) : ℤ) from ⟨(q : ℤ), by push_cast; ring⟩).trans hg

def incl : Gamma0 (N * q) →* Gamma0 N := Subgroup.inclusion (gamma0_mul_le N q)

@[scoped simp] theorem coe_incl (γ : Gamma0 (N * q)) : ((incl N q γ : Gamma0 N) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := rfl

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (ρ' : Representation K (Gamma0 (N * q)) V)
  (hρ : ∀ γ : Gamma0 (N * q), ρ (incl N q γ) = ρ' γ)

include hρ in

theorem restrict_mem_coeffCocycles {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) :
    (fun γ => z (incl N q γ)) ∈ coeffCocycles ρ' := by
  intro g h
  simp only [map_mul, hz (incl N q g) (incl N q h), hρ]

include hρ in
theorem restrict_mem_coeffCoboundaries {z : Gamma0 N → V} (hz : z ∈ coeffCoboundaries ρ) :
    (fun γ => z (incl N q γ)) ∈ coeffCoboundaries ρ' := by
  obtain ⟨v, rfl⟩ := hz
  refine ⟨v, funext fun γ => ?_⟩
  simp [coeffCoboundaryMap_apply, hρ]

def resZ1 : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ') where
  toFun z := ⟨fun γ => (z : Gamma0 N → V) (incl N q γ), restrict_mem_coeffCocycles N q ρ ρ' hρ z.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

@[scoped simp] theorem coe_resZ1 (z : ↥(coeffCocycles ρ)) :
    (resZ1 N q ρ ρ' hρ z : Gamma0 (N * q) → V) = fun γ => (z : Gamma0 N → V) (incl N q γ) := rfl

theorem comap_le_comap_resZ1 :
    (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype ≤
      ((coeffCoboundaries ρ').comap (coeffCocycles ρ').subtype).comap (resZ1 N q ρ ρ' hρ) := by
  intro z hz
  change (fun γ => (z : Gamma0 N → V) (incl N q γ)) ∈ coeffCoboundaries ρ'
  exact restrict_mem_coeffCoboundaries N q ρ ρ' hρ hz

def resH1 : coeffH1 ρ →ₗ[K] coeffH1 ρ' :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ').comap (coeffCocycles ρ').subtype)
    (resZ1 N q ρ ρ' hρ) (comap_le_comap_resZ1 N q ρ ρ' hρ)

theorem resH1_mk (z : ↥(coeffCocycles ρ)) :
    resH1 N q ρ ρ' hρ (coeffH1Mk _ z) = coeffH1Mk _ (resZ1 N q ρ ρ' hρ z) := rfl

theorem resH1_injective [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N) (hq1 : IsUnit (((q + 1 : ℕ) : K))) :
    Function.Injective (resH1 N q ρ ρ' hρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  rw [resH1_mk, coeffH1Mk_eq_zero_iff] at hx
  rw [coeffH1Mk_eq_zero_iff]
  obtain ⟨u, hu⟩ := (mem_coeffCoboundaries_iff _ _).mp hx
  set H : Subgroup (Gamma0 N) := (Gamma0 (N * q)).subgroupOf (Gamma0 N) with hH
  have hindex : H.index = q + 1 := index_subgroupOf_mul N hq hqN
  haveI : H.FiniteIndex := ⟨by rw [hindex]; exact Nat.succ_ne_zero q⟩
  have hzH : ∀ t : Gamma0 N, t ∈ H → (z : Gamma0 N → V) t = ρ t u - u := by
    intro t ht
    have h := congrFun hu ⟨(t : SL(2, ℤ)), ht⟩
    rw [← hρ] at h
    exact h.symm
  have hcob := index_smul_mem_coeffCoboundaries H ρ z.2 u hzH
  rw [hindex] at hcob
  obtain ⟨c, hc⟩ := hq1
  have h := (coeffCoboundaries ρ).smul_mem (↑c⁻¹ : K) hcob
  rwa [← hc, smul_smul, Units.inv_mul, one_smul] at h

variable (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓq : ¬ ℓ ∣ q)

theorem incl_mem_heckeUpper_iff (γ : Gamma0 (N * q)) : incl N q γ ∈ heckeUpper N ℓ ↔ γ ∈ heckeUpper (N * q) ℓ := by
  rw [mem_heckeUpper, mem_heckeUpper, coe_incl]

def cosetMap : Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ → Gamma0 N ⧸ heckeUpper N ℓ :=
  Quotient.map' (incl N q) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact (incl_mem_heckeUpper_iff N q ℓ _).mpr hab

theorem cosetMap_mk (γ : Gamma0 (N * q)) :
    cosetMap N q ℓ (γ : Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ) = ((incl N q γ : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

theorem cosetMap_smul (γ : Gamma0 (N * q)) (x : Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ) :
    cosetMap N q ℓ (γ • x) = incl N q γ • cosetMap N q ℓ x := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    show cosetMap N q ℓ ((γ * x : Gamma0 (N * q)) : _ ⧸ _) = _
    rw [cosetMap_mk, cosetMap_mk, map_mul]
    rfl

theorem cosetMap_injective : Function.Injective (cosetMap N q ℓ) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
    intro h
    rw [cosetMap_mk, cosetMap_mk, QuotientGroup.eq, ← map_inv, ← map_mul, incl_mem_heckeUpper_iff] at h
    exact QuotientGroup.eq.mpr h

include hℓ hℓN hℓq in
theorem cosetMap_bijective : Function.Bijective (cosetMap N q ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Finite (Gamma0 N ⧸ heckeUpper N ℓ) := Subgroup.finite_quotient_of_finiteIndex
  refine (cosetMap_injective N q ℓ).bijective_of_nat_card_le (le_of_eq ?_)
  have hℓNq : ¬ ℓ ∣ N * q := fun h => ((Nat.Prime.dvd_mul hℓ).mp h).elim hℓN hℓq
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card, ModularCurve.index_heckeUpper hℓ hℓN,
    ModularCurve.index_heckeUpper hℓ hℓNq]

noncomputable def cosetEquiv : (Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ) :=
  Equiv.ofBijective _ (cosetMap_bijective N q ℓ hℓ hℓN hℓq)

theorem cosetEquiv_apply (x : Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ) :
    cosetEquiv N q ℓ hℓ hℓN hℓq x = cosetMap N q ℓ x := rfl

noncomputable def sec (x : Gamma0 N ⧸ heckeUpper N ℓ) : Gamma0 N :=
  incl N q ((cosetEquiv N q ℓ hℓ hℓN hℓq).symm x).out

theorem sec_spec (x : Gamma0 N ⧸ heckeUpper N ℓ) :
    ((sec N q ℓ hℓ hℓN hℓq x : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ) = x := by
  rw [sec, ← cosetMap_mk N q ℓ, QuotientGroup.out_eq', ← cosetEquiv_apply N q ℓ hℓ hℓN hℓq, Equiv.apply_symm_apply]

theorem sec_cosetEquiv (x : Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ) :
    sec N q ℓ hℓ hℓN hℓq (cosetEquiv N q ℓ hℓ hℓN hℓq x) = incl N q x.out := by
  rw [sec, Equiv.symm_apply_apply]

noncomputable def tra (g : Gamma0 N) (x : Gamma0 N ⧸ heckeUpper N ℓ) : ↥(heckeUpper N ℓ) :=
  ⟨(sec N q ℓ hℓ hℓN hℓq (g • x))⁻¹ * (g * sec N q ℓ hℓ hℓN hℓq x), by
    refine QuotientGroup.eq.mp ?_
    rw [sec_spec]
    show g • x = ((g * sec N q ℓ hℓ hℓN hℓq x : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ)
    rw [show ((g * sec N q ℓ hℓ hℓN hℓq x : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ)
        = g • ((sec N q ℓ hℓ hℓN hℓq x : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ) from rfl, sec_spec]⟩

theorem sec_mul_tra (g : Gamma0 N) (x : Gamma0 N ⧸ heckeUpper N ℓ) :
    sec N q ℓ hℓ hℓN hℓq (g • x) * (tra N q ℓ hℓ hℓN hℓq g x : Gamma0 N) = g * sec N q ℓ hℓ hℓN hℓq x := by
  show sec N q ℓ hℓ hℓN hℓq (g • x) * ((sec N q ℓ hℓ hℓN hℓq (g • x))⁻¹ * (g * sec N q ℓ hℓ hℓN hℓq x)) = _
  rw [mul_inv_cancel_left]

theorem coe_tra_incl (γ : Gamma0 (N * q)) (x : Gamma0 (N * q) ⧸ heckeUpper (N * q) ℓ) :
    (tra N q ℓ hℓ hℓN hℓq (incl N q γ) (cosetEquiv N q ℓ hℓ hℓN hℓq x) : Gamma0 N) =
      incl N q (transferAux (heckeUpper (N * q) ℓ) γ x : Gamma0 (N * q)) := by
  show (sec N q ℓ hℓ hℓN hℓq (incl N q γ • cosetEquiv N q ℓ hℓ hℓN hℓq x))⁻¹ *
      (incl N q γ * sec N q ℓ hℓ hℓN hℓq (cosetEquiv N q ℓ hℓ hℓN hℓq x)) = _
  have h1 : incl N q γ • cosetEquiv N q ℓ hℓ hℓN hℓq x = cosetEquiv N q ℓ hℓ hℓN hℓq (γ • x) := by
    rw [cosetEquiv_apply, cosetEquiv_apply, cosetMap_smul]
  rw [h1, sec_cosetEquiv, sec_cosetEquiv, coe_transferAux, map_mul, map_mul, map_inv]

theorem heckeConj_incl [NeZero ℓ] (u : ↥(heckeUpper (N * q) ℓ)) (hu : incl N q (u : Gamma0 (N * q)) ∈ heckeUpper N ℓ) :
    heckeConj N ℓ ⟨incl N q (u : Gamma0 (N * q)), hu⟩ = incl N q (heckeConj (N * q) ℓ u : Gamma0 (N * q)) :=
  Subtype.ext (Subtype.ext rfl)

variable (a : V →ₗ[K] V)

include hρ hℓ hℓN hℓq in

theorem resH1_heckeH1 [NeZero ℓ] (ha : IsCompat N ℓ ρ a) (ha' : IsCompat (N * q) ℓ ρ' a) (x : coeffH1 ρ) :
    resH1 N q ρ ρ' hρ (heckeH1 ha x) = heckeH1 ha' (resH1 N q ρ ρ' hρ x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  rw [heckeH1_mk, resH1_mk, resH1_mk, heckeH1_mk, coeffH1Mk_eq_iff]

  have hcob := sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha
    (sec N q ℓ hℓ hℓN hℓq) (tra N q ℓ hℓ hℓN hℓq) (sec_spec N q ℓ hℓ hℓN hℓq)
    (sec_mul_tra N q ℓ hℓ hℓN hℓq) z.2

  have hres := restrict_mem_coeffCoboundaries N q ρ ρ' hρ hcob

  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  letI := (heckeUpper (N * q) ℓ).fintypeQuotientOfFiniteIndex
  have hsum : ∀ γ : Gamma0 (N * q),
      (∑ x : Gamma0 N ⧸ heckeUpper N ℓ,
        ρ (sec N q ℓ hℓ hℓN hℓq (incl N q γ • x))
          (a ((z : Gamma0 N → V) (heckeConj N ℓ (tra N q ℓ hℓ hℓN hℓq (incl N q γ) x)))))
      = coeffHeckeFun (N * q) ℓ ρ' a (fun δ => (z : Gamma0 N → V) (incl N q δ)) γ := by
    intro γ
    rw [coeffHeckeFun_apply, ← (cosetEquiv N q ℓ hℓ hℓN hℓq).sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hsx : sec N q ℓ hℓ hℓN hℓq (incl N q γ • cosetEquiv N q ℓ hℓ hℓN hℓq x) = incl N q (γ • x).out := by
      rw [show incl N q γ • cosetEquiv N q ℓ hℓ hℓN hℓq x = cosetEquiv N q ℓ hℓ hℓN hℓq (γ • x) by
        rw [cosetEquiv_apply, cosetEquiv_apply, cosetMap_smul], sec_cosetEquiv]
    have hmem : incl N q (transferAux (heckeUpper (N * q) ℓ) γ x : Gamma0 (N * q)) ∈ heckeUpper N ℓ :=
      (incl_mem_heckeUpper_iff N q ℓ _).mpr (transferAux (heckeUpper (N * q) ℓ) γ x).2
    have htra : tra N q ℓ hℓ hℓN hℓq (incl N q γ) (cosetEquiv N q ℓ hℓ hℓN hℓq x)
        = ⟨incl N q (transferAux (heckeUpper (N * q) ℓ) γ x : Gamma0 (N * q)), hmem⟩ :=
      Subtype.ext (coe_tra_incl N q ℓ hℓ hℓN hℓq γ x)
    rw [hsx, htra, heckeConj_incl, hρ]

  have hkey : (fun γ : Gamma0 (N * q) =>
      coeffHeckeFun (N * q) ℓ ρ' a (fun δ => (z : Gamma0 N → V) (incl N q δ)) γ
        - coeffHeckeFun N ℓ ρ a z (incl N q γ)) ∈ coeffCoboundaries ρ' := by
    convert hres using 1
    funext γ
    simp only [Pi.sub_apply, hsum γ]
  have hneg := (coeffCoboundaries ρ').neg_mem hkey
  convert hneg using 1
  funext γ
  simp only [Pi.sub_apply, Pi.neg_apply, neg_sub, coe_heckeZ1, coe_resZ1]

end Restrict

end LevelRaise
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1.LevelRaise"

open scoped MatrixGroups in
theorem solution
    (N : ℕ) [NeZero N] (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (κ : Type) [Field κ] (hq1 : ((q + 1 : ℕ) : κ) ≠ 0) (S₀ : Set ℕ) (n : ℕ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    HeckeEis.IsEigensystemH1 (N * q)
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 (N * q)).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) (insert q S₀) lam := by
  open LevelRaise HeckeEis CongruenceSubgroup in

  set ρ : Representation κ (Gamma0 N) ↥(BinaryForm κ n) := (binaryFormRepSL κ n).comp (Gamma0 N).subtype
  set ρ' : Representation κ (Gamma0 (N * q)) ↥(BinaryForm κ n) :=
    (binaryFormRepSL κ n).comp (Gamma0 (N * q)).subtype
  have hρ : ∀ γ : Gamma0 (N * q), ρ (incl N q γ) = ρ' γ := fun _ => rfl
  have hcompat : ∀ (M ℓ : ℕ) [NeZero ℓ],
      IsCompat M ℓ ((binaryFormRepSL κ n).comp (Gamma0 M).subtype) (binaryFormAlphaAdj κ n ℓ) :=
    fun M ℓ _ u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj κ n M ℓ u
  obtain ⟨x, hx, heig⟩ := hocc
  have hunit : IsUnit (((q + 1 : ℕ) : κ)) := isUnit_iff_ne_zero.mpr hq1
  refine ⟨resH1 N q ρ ρ' hρ x, fun h => hx (resH1_injective N q ρ ρ' hρ hq hqN hunit (by rw [h, map_zero])), ?_⟩
  intro ℓ hℓ hℓNq hℓS
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓN : ¬ ℓ ∣ N := fun h => hℓNq (h.mul_right q)
  have hℓq : ¬ ℓ ∣ q := by
    intro h
    have : ℓ = q := (Nat.prime_dvd_prime_iff_eq hℓ hq).mp h
    exact hℓS (this ▸ Set.mem_insert q S₀)
  have hℓS' : ℓ ∉ S₀ := fun h => hℓS (Set.mem_insert_of_mem q h)
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS'
  refine ⟨heckeH1 (hcompat (N * q) ℓ), isCoeffHeckeOnH1_heckeH1 _, ?_⟩
  have hT' : IsCoeffHeckeOnH1 N ℓ ρ (binaryFormAlphaAdj κ n ℓ) T := hT
  rw [unique_of_isCoeffHeckeOnH1 hT' (isCoeffHeckeOnH1_heckeH1 (hcompat N ℓ))] at hTx
  rw [← resH1_heckeH1 N q ρ ρ' hρ ℓ hℓ hℓN hℓq (binaryFormAlphaAdj κ n ℓ) (hcompat N ℓ) (hcompat (N * q) ℓ),
    hTx, map_smul]

end S_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1 (solution)
