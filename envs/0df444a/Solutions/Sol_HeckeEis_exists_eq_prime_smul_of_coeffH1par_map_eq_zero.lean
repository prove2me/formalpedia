-- Prove2me | solution 1 for HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3a49ed0c-c5a3-5583-9cd2-013c429c1dc6

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Theorems.Thm_HeckeEis_binaryFormRepSL_neg_one_apply
import Theorems.Thm_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
import Theorems.Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff binaryFormRepSL_neg_one_apply coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem"
namespace CoeffMapAux
p2m_open "HeckeEis"

open MvPolynomial
open scoped MatrixGroups

variable {R R' : Type*} [CommRing R] [CommRing R']

theorem binarySubst_eq_bind₁ (S : Type*) [CommRing S] (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) S) :
    binarySubst S M P = bind₁ (fun j => ∑ i : Fin 2, C ((M i j : ℤ) : S) * X i) P := by
  rw [binarySubst, aeval_eq_bind₁]

theorem map_binarySubst_int (φ : ℤ →+* R) (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.map φ (binarySubst ℤ M P) = binarySubst R M (MvPolynomial.map φ P) := by
  have key : (MvPolynomial.map φ).comp (binarySubst ℤ M : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] MvPolynomial (Fin 2) ℤ).toRingHom
      = (binarySubst R M : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R).toRingHom.comp (MvPolynomial.map φ) :=
    MvPolynomial.ringHom_ext (fun a => by simp [binarySubst_C]) (fun j => by simp [binarySubst_X, map_sum])
  exact RingHom.congr_fun key P

def substCoeff (M : Matrix (Fin 2) (Fin 2) ℤ) (d d' : Fin 2 →₀ ℕ) : ℤ :=
  coeff d (binarySubst ℤ M (monomial d' 1))

theorem binarySubst_monomial_one (M : Matrix (Fin 2) (Fin 2) ℤ) (d' : Fin 2 →₀ ℕ) :
    binarySubst R M (monomial d' 1) = MvPolynomial.map (Int.castRingHom R) (binarySubst ℤ M (monomial d' 1)) := by
  rw [map_binarySubst_int, map_monomial, (Int.castRingHom R).map_one]

theorem coeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst R M P) = ∑ d' ∈ P.support, (substCoeff M d d' : R) * coeff d' P := by
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [show monomial d' (coeff d' P) = C (coeff d' P) * monomial d' 1 by rw [C_mul_monomial, mul_one], map_mul, binarySubst_C,
    coeff_C_mul, binarySubst_monomial_one, coeff_map, substCoeff, mul_comm]
  rfl

variable (f : R →+ R')

def pushCoeff (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R' :=
  ∑ d ∈ P.support, monomial d (f (coeff d P))

@[scoped simp] theorem coeff_pushCoeff (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) : coeff d (pushCoeff f P) = f (coeff d P) := by
  classical
  rw [pushCoeff, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

theorem support_pushCoeff (P : MvPolynomial (Fin 2) R) : (pushCoeff f P).support ⊆ P.support := by
  intro d hd
  rw [mem_support_iff, coeff_pushCoeff] at hd
  rw [mem_support_iff]
  intro h; exact hd (by rw [h, map_zero])

theorem pushCoeff_mem (n : ℕ) {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : pushCoeff f P ∈ BinaryForm R' n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  intro d hd
  exact hP (mem_support_iff.mp (support_pushCoeff f P (mem_support_iff.mpr hd)))

theorem pushCoeff_add (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P + Q) = pushCoeff f P + pushCoeff f Q := by
  ext d; simp

theorem pushCoeff_sub (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P - Q) = pushCoeff f P - pushCoeff f Q := by
  ext d; simp

theorem pushCoeff_zero : pushCoeff f (0 : MvPolynomial (Fin 2) R) = 0 := by
  ext d; simp

theorem eq_pushCoeff_iff (P : MvPolynomial (Fin 2) R) (Q : MvPolynomial (Fin 2) R') :
    Q = pushCoeff f P ↔ ∀ d, coeff d Q = f (coeff d P) := by
  constructor
  · rintro rfl d; exact coeff_pushCoeff f P d
  · intro h; ext d; rw [h d, coeff_pushCoeff]

theorem pushCoeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    pushCoeff f (binarySubst R M P) = binarySubst R' M (pushCoeff f P) := by
  classical
  ext d
  rw [coeff_pushCoeff, coeff_binarySubst, coeff_binarySubst, map_sum]

  rw [Finset.sum_subset (support_pushCoeff f P)]
  · refine Finset.sum_congr rfl fun d' _ => ?_
    rw [coeff_pushCoeff, ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul]
  · intro d' _ hd'
    rw [notMem_support_iff.mp hd', mul_zero]

def pushForm (n : ℕ) (P : ↥(BinaryForm R n)) : ↥(BinaryForm R' n) := ⟨pushCoeff f P, pushCoeff_mem f n P.2⟩

@[scoped simp] theorem coe_pushForm (n : ℕ) (P : ↥(BinaryForm R n)) :
    ((pushForm f n P : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = pushCoeff f P := rfl

theorem pushForm_add (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P + Q) = pushForm f n P + pushForm f n Q :=
  Subtype.ext (by simp [pushCoeff_add])

theorem pushForm_sub (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P - Q) = pushForm f n P - pushForm f n Q :=
  Subtype.ext (by simp [pushCoeff_sub])

theorem pushForm_zero (n : ℕ) : pushForm f n (0 : ↥(BinaryForm R n)) = 0 := Subtype.ext (by simp [pushCoeff_zero])

theorem pushForm_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (P : ↥(BinaryForm R n)) :
    pushForm f n (binaryFormRepSL R n g P) = binaryFormRepSL R' n g (pushForm f n P) :=
  Subtype.ext (by simp [pushCoeff_binarySubst])

section Cocycles

variable {Γ : Subgroup SL(2, ℤ)} (n : ℕ)

theorem pushForm_comp_mem_coeffCocycles {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCocycles ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffCocycles ((binaryFormRepSL R' n).comp Γ.subtype) := by
  intro g h
  show pushForm f n (z (g * h)) = pushForm f n (z g) + binaryFormRepSL R' n ((g : Γ) : SL(2, ℤ)) (pushForm f n (z h))
  rw [hz g h, pushForm_add, ← pushForm_binaryFormRepSL]
  rfl

theorem isParabolicCocycle_pushForm_comp {z : Γ → ↥(BinaryForm R n)}
    (hz : IsParabolicCocycle ((binaryFormRepSL R n).comp Γ.subtype) z) :
    IsParabolicCocycle ((binaryFormRepSL R' n).comp Γ.subtype) (fun g => pushForm f n (z g)) := by
  intro γ hγ
  obtain ⟨u, hu⟩ := hz γ hγ
  refine ⟨pushForm f n u, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply] at hu ⊢
  change binaryFormRepSL R n (γ : SL(2, ℤ)) u - u = z γ at hu
  show binaryFormRepSL R' n (γ : SL(2, ℤ)) (pushForm f n u) - pushForm f n u = pushForm f n (z γ)
  rw [← hu, pushForm_sub, pushForm_binaryFormRepSL]

theorem pushForm_comp_mem_coeffParabolicCocycles {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype) :=
  ⟨pushForm_comp_mem_coeffCocycles f n hz.1, isParabolicCocycle_pushForm_comp f n hz.2⟩

theorem pushForm_comp_mem_coeffCoboundaries {z : Γ → ↥(BinaryForm R n)}
    (hz : z ∈ coeffCoboundaries ((binaryFormRepSL R n).comp Γ.subtype)) :
    (fun g => pushForm f n (z g)) ∈ coeffCoboundaries ((binaryFormRepSL R' n).comp Γ.subtype) := by
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hz
  rw [mem_coeffCoboundaries_iff]
  refine ⟨pushForm f n v, funext fun g => ?_⟩
  have h := congrFun hv g
  change binaryFormRepSL R n (g : SL(2, ℤ)) v - v = z g at h
  show binaryFormRepSL R' n (g : SL(2, ℤ)) (pushForm f n v) - pushForm f n v = pushForm f n (z g)
  rw [← h, pushForm_sub, pushForm_binaryFormRepSL]

def pushPar : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))
    →+ ↥(coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype)) where
  toFun z := ⟨fun g => pushForm f n (z.1 g), pushForm_comp_mem_coeffParabolicCocycles f n z.2⟩
  map_zero' := by
    apply Subtype.ext; funext g
    show pushForm f n ((0 : Γ → ↥(BinaryForm R n)) g) = 0
    rw [Pi.zero_apply, pushForm_zero]
  map_add' z w := by
    apply Subtype.ext; funext g
    show pushForm f n (z.1 g + w.1 g) = pushForm f n (z.1 g) + pushForm f n (w.1 g)
    rw [pushForm_add]

@[scoped simp] theorem pushPar_apply_coe (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) (g : Γ) :
    (((pushPar f n z).1 g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = pushCoeff f (z.1 g) := rfl

theorem pushPar_apply_val (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) (g : Γ) :
    (pushPar f n z).1 g = pushForm f n (z.1 g) := rfl

theorem mk_eq_mk_iff {S : Type*} [CommRing S] (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))) :
    coeffH1parMk _ a = coeffH1parMk _ b ↔
      ((a - b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))).1
        ∈ coeffCoboundaries ((binaryFormRepSL S n).comp Γ.subtype)) := by
  rw [← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]

theorem pushPar_sub (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) :
    pushPar f n (a - b) = pushPar f n a - pushPar f n b :=
  map_sub (pushPar f n) a b

theorem mk_pushPar_congr {a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))}
    (h : coeffH1parMk _ a = coeffH1parMk _ b) :
    coeffH1parMk _ (pushPar f n a) = coeffH1parMk _ (pushPar f n b) := by
  rw [mk_eq_mk_iff] at h ⊢
  rw [← pushPar_sub]
  exact pushForm_comp_mem_coeffCoboundaries f n h

def pushH1par : coeffH1par ((binaryFormRepSL R n).comp Γ.subtype) →+ coeffH1par ((binaryFormRepSL R' n).comp Γ.subtype) where
  toFun x := coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) x))
  map_zero' := by
    have h0 : coeffH1parMk _ (Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) 0)
        = coeffH1parMk _ (0 : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) := by
      rw [Function.surjInv_eq (coeffH1parMk_surjective _), map_zero]
    show coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) 0)) = 0
    rw [mk_pushPar_congr f n h0, map_zero, map_zero]
  map_add' x y := by
    have hxy : coeffH1parMk _ (Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) (x + y))
        = coeffH1parMk _ (Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) x
            + Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) y) := by
      rw [map_add, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _),
        Function.surjInv_eq (coeffH1parMk_surjective _)]
    show coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) (x + y))) = _
    rw [mk_pushPar_congr f n hxy, map_add, map_add]

theorem pushH1par_mk (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) :
    pushH1par f n (coeffH1parMk _ z) = coeffH1parMk _ (pushPar f n z) := by
  show coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) (coeffH1parMk _ z))) = _
  apply mk_pushPar_congr
  exact Function.surjInv_eq (coeffH1parMk_surjective _) _

end Cocycles

end HeckeEis.CoeffMapAux
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis"

end
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff binaryFormRepSL_neg_one_apply coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem"
namespace GenAux
p2m_open "HeckeEis"

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

theorem coeffCocycles_apply_one {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h

  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem coeffCocycles_apply_inv {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) (g : G) :
    z g⁻¹ = -(ρ g⁻¹ (z g)) := by
  have h := hz g⁻¹ g
  rw [inv_mul_cancel, coeffCocycles_apply_one hz] at h

  exact eq_neg_of_add_eq_zero_left h.symm

theorem mem_of_mem_coeffCocycles_of_closure_eq_top {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ)
    (M : AddSubgroup V) (hM : ∀ (g : G) (v : V), v ∈ M → ρ g v ∈ M) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (h : ∀ g ∈ s, z g ∈ M) (g : G) : z g ∈ M := by
  let H : Subgroup G :=
    { carrier := {g | z g ∈ M}
      one_mem' := by
        show z 1 ∈ M
        rw [coeffCocycles_apply_one hz]; exact M.zero_mem
      mul_mem' := by
        intro a b ha hb
        show z (a * b) ∈ M
        rw [hz a b]
        exact M.add_mem ha (hM a _ hb)
      inv_mem' := by
        intro a ha
        show z a⁻¹ ∈ M
        rw [coeffCocycles_apply_inv hz]
        exact M.neg_mem (hM _ _ ha) }
  have hle : (⊤ : Subgroup G) ≤ H := by
    rw [← hs, Subgroup.closure_le]
    exact h
  exact hle (Subgroup.mem_top g)

theorem coeffCocycles_eq_of_eqOn {ρ : Representation K G V} {z z' : G → V} (hz : z ∈ coeffCocycles ρ) (hz' : z' ∈ coeffCocycles ρ)
    {s : Set G} (hs : Subgroup.closure s = ⊤) (h : ∀ g ∈ s, z g = z' g) : z = z' := by
  have hd : z - z' ∈ coeffCocycles ρ := Submodule.sub_mem _ hz hz'
  funext g
  have := mem_of_mem_coeffCocycles_of_closure_eq_top hd ⊥ (fun g v hv => by
    rw [AddSubgroup.mem_bot] at hv ⊢; rw [hv, map_zero]) hs (fun g hg => by
    rw [AddSubgroup.mem_bot, Pi.sub_apply, h g hg, sub_self]) g
  rw [AddSubgroup.mem_bot, Pi.sub_apply] at this
  exact sub_eq_zero.mp this

end HeckeEis.GenAux
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff binaryFormRepSL_neg_one_apply coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem"
namespace RatAux
p2m_open "HeckeEis"
end HeckeEis.RatAux
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff binaryFormRepSL_neg_one_apply coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem"
namespace ZQAux
p2m_open "HeckeEis"

open MvPolynomial HeckeEis.CoeffMapAux HeckeEis.RatAux HeckeEis.GenAux CongruenceSubgroup
open scoped MatrixGroups

theorem Gamma_le_Gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := fun _ hA => Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1

theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by rw [Gamma0_mem]; simp

theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (δ : SL(2, ℤ)) : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := by
  have hTN : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  exact Gamma_le_Gamma0 N ((CongruenceSubgroup.Gamma_normal N).conj_mem _ hTN δ)

scoped instance instGroupFG_Gamma0 (N : ℕ) [NeZero N] : Group.FG (Gamma0 N) := by
  haveI : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_Gamma0 N)
  haveI : Group.FG SL(2, ℤ) := ⟨⟨{ModularGroup.S, ModularGroup.T}, by simpa using SpecialLinearGroup.SL2Z_generators⟩⟩
  exact Subgroup.fg_of_index_ne_zero _

theorem conj_T_zpow_eq (δ : SL(2, ℤ)) (h : ℤ) : δ * ModularGroup.T ^ h * δ⁻¹ = MulAut.conj δ (ModularGroup.T ^ h) := by
  rw [MulAut.conj_apply]

theorem conj_T_zpow_add (δ : SL(2, ℤ)) (x y : ℤ) :
    δ * ModularGroup.T ^ (x + y) * δ⁻¹ = (δ * ModularGroup.T ^ x * δ⁻¹) * (δ * ModularGroup.T ^ y * δ⁻¹) := by
  rw [zpow_add]; group

theorem conj_T_zpow_mul (δ : SL(2, ℤ)) (a k : ℤ) :
    δ * ModularGroup.T ^ (a * k) * δ⁻¹ = (δ * ModularGroup.T ^ a * δ⁻¹) ^ k := by
  rw [zpow_mul]
  have h := map_zpow (MulAut.conj δ) (ModularGroup.T ^ a) k
  simp only [MulAut.conj_apply] at h
  exact h

theorem trace_conj_T_zpow (δ : SL(2, ℤ)) (h : ℤ) :
    ((δ * ModularGroup.T ^ h * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
    ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  ring

section CuspWidth

variable (N : ℕ) [NeZero N]

theorem exists_pos_conj_T_pow_mem (δ : SL(2, ℤ)) : ∃ a : ℕ, 0 < a ∧ δ * ModularGroup.T ^ (a : ℤ) * δ⁻¹ ∈ Gamma0 N :=
  ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), conj_T_zpow_mem_Gamma0 N δ⟩

open Classical in

def cuspWidth (δ : SL(2, ℤ)) : ℕ := Nat.find (exists_pos_conj_T_pow_mem N δ)

open Classical in
theorem cuspWidth_spec (δ : SL(2, ℤ)) :
    0 < cuspWidth N δ ∧ δ * ModularGroup.T ^ (cuspWidth N δ : ℤ) * δ⁻¹ ∈ Gamma0 N :=
  Nat.find_spec (exists_pos_conj_T_pow_mem N δ)

open Classical in
theorem cuspWidth_min (δ : SL(2, ℤ)) {r : ℕ} (hr : 0 < r) (hmem : δ * ModularGroup.T ^ (r : ℤ) * δ⁻¹ ∈ Gamma0 N) :
    cuspWidth N δ ≤ r :=
  Nat.find_min' (exists_pos_conj_T_pow_mem N δ) ⟨hr, hmem⟩

theorem cuspWidth_dvd (δ : SL(2, ℤ)) {h : ℤ} (hh : δ * ModularGroup.T ^ h * δ⁻¹ ∈ Gamma0 N) :
    (cuspWidth N δ : ℤ) ∣ h := by
  obtain ⟨ha, hmem⟩ := cuspWidth_spec N δ
  set a : ℕ := cuspWidth N δ with hadef
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha

  have hrmem : δ * ModularGroup.T ^ (h % a) * δ⁻¹ ∈ Gamma0 N := by
    have e : h % (a : ℤ) = h + (a : ℤ) * (-(h / a)) := by rw [Int.emod_def]; ring
    rw [e, conj_T_zpow_add, conj_T_zpow_mul]
    exact Subgroup.mul_mem _ hh (Subgroup.zpow_mem _ hmem _)
  by_contra hnd
  have hne : h % (a : ℤ) ≠ 0 := fun h0 => hnd (Int.dvd_of_emod_eq_zero h0)
  have hnn : 0 ≤ h % (a : ℤ) := Int.emod_nonneg _ ha'.ne'
  have hlt : h % (a : ℤ) < a := Int.emod_lt_of_pos _ ha'
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hnn
  rw [hr] at hne hlt hrmem
  have hrpos : 0 < r := by omega
  have := cuspWidth_min N δ hrpos hrmem
  omega

end CuspWidth
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"

section CocycleAlgebra

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {ρ : Representation K G V} {y : G → V}

theorem mem_range_of_mem_closure (hy : y ∈ coeffCocycles ρ) (w : V) {s : Set G} (hs : ∀ v ∈ s, y v = ρ v w - w)
    {g : G} (hg : g ∈ Subgroup.closure s) : y g = ρ g w - w := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => rw [coeffCocycles_apply_one hy, map_one, Module.End.one_apply, sub_self]
  | mul a b _ _ iha ihb =>
    rw [hy a b, iha, ihb, map_mul, Module.End.mul_apply, map_sub]
    abel
  | inv a _ iha =>
    rw [coeffCocycles_apply_inv hy, iha, map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
    abel

theorem apply_conj (hy : y ∈ coeffCocycles ρ) (g v : G) :
    y (g * v * g⁻¹) = ρ g (y v) - (ρ (g * v * g⁻¹) (y g) - y g) := by
  have h3 : ρ (g * v) (ρ g⁻¹ (y g)) = ρ (g * v * g⁻¹) (y g) := by
    rw [← Module.End.mul_apply, ← map_mul]
  rw [hy (g * v) g⁻¹, hy g v, coeffCocycles_apply_inv hy, map_neg, h3]
  abel

theorem apply_conj_mem_range (hy : y ∈ coeffCocycles ρ) {v : G} {w : V} (hv : y v = ρ v w - w) (g : G) :
    y (g * v * g⁻¹) ∈ LinearMap.range (ρ (g * v * g⁻¹) - 1) := by
  refine ⟨ρ g w - y g, ?_⟩
  rw [apply_conj hy, hv, LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub]
  have : ρ (g * v * g⁻¹) (ρ g w) = ρ g (ρ v w) := by
    rw [← Module.End.mul_apply, ← map_mul, show g * v * g⁻¹ * g = g * v by group, map_mul, Module.End.mul_apply]
  rw [this]
  abel

end CocycleAlgebra
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"

end HeckeEis.ZQAux
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.ZQAux"
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux"

end
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.ZQAux"

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL coeffCocycles coeffCoboundaries mem_coeffCoboundaries_iff IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff binaryFormRepSL_neg_one_apply coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem"
namespace ModPAux
p2m_open "HeckeEis"

open MvPolynomial HeckeEis.CoeffMapAux HeckeEis.GenAux HeckeEis.ZQAux CongruenceSubgroup
open scoped MatrixGroups

theorem pushCoeff_pushCoeff {R R' R'' : Type*} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+ R') (g : R' →+ R'')
    (P : MvPolynomial (Fin 2) R) : pushCoeff g (pushCoeff f P) = pushCoeff (g.comp f) P :=
  (eq_pushCoeff_iff _ _ _).mpr fun d => by rw [coeff_pushCoeff, coeff_pushCoeff]; rfl

theorem pushForm_pushForm {R R' R'' : Type*} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+ R') (g : R' →+ R'')
    (n : ℕ) (P : ↥(BinaryForm R n)) : pushForm g n (pushForm f n P) = pushForm (g.comp f) n P :=
  Subtype.ext (pushCoeff_pushCoeff f g P)

theorem map_eq_pushCoeff {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ P = pushCoeff φ.toAddMonoidHom P :=
  (eq_pushCoeff_iff _ _ _).mpr fun d => by rw [coeff_map]; rfl

def cf (n : ℕ) (d : Fin 2 →₀ ℕ) : ↥(BinaryForm ℤ n) →+ ℤ :=
  ((MvPolynomial.lcoeff ℤ d).comp (BinaryForm ℤ n).subtype).toAddMonoidHom

theorem cf_apply (n : ℕ) (d : Fin 2 →₀ ℕ) (P : ↥(BinaryForm ℤ n)) : cf n d P = coeff d (P : MvPolynomial (Fin 2) ℤ) := rfl

theorem coeff_zsmul_val (n : ℕ) (m : ℤ) (P : ↥(BinaryForm ℤ n)) (d : Fin 2 →₀ ℕ) :
    coeff d (((m • P : ↥(BinaryForm ℤ n))) : MvPolynomial (Fin 2) ℤ) = m * coeff d (P : MvPolynomial (Fin 2) ℤ) := by
  rw [← cf_apply, ← cf_apply, map_zsmul, zsmul_eq_mul]
  first
    | rfl
    | simp

theorem exists_pushForm_intCast_eq (p : ℕ) [NeZero p] (n : ℕ) (Q : ↥(BinaryForm (ZMod p) n)) :
    ∃ P : ↥(BinaryForm ℤ n), pushForm (Int.castRingHom (ZMod p)).toAddMonoidHom n P = Q := by
  classical
  let P : MvPolynomial (Fin 2) ℤ := ∑ d ∈ (Q : MvPolynomial (Fin 2) (ZMod p)).support, monomial d (((coeff d (Q : MvPolynomial (Fin 2) (ZMod p))).val : ℤ))
  have hcoeff : ∀ d, coeff d P = ((coeff d (Q : MvPolynomial (Fin 2) (ZMod p))).val : ℤ) := by
    intro d
    simp only [P, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, ZMod.val_zero, Nat.cast_zero]
  have hP : P ∈ BinaryForm ℤ n := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    intro d hd
    have hq : coeff d (Q : MvPolynomial (Fin 2) (ZMod p)) ≠ 0 := by
      intro h0; apply hd; rw [hcoeff, h0, ZMod.val_zero, Nat.cast_zero]
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mp Q.2 hq
  refine ⟨⟨P, hP⟩, Subtype.ext ((eq_pushCoeff_iff _ _ _).mpr fun d => ?_).symm⟩
  show coeff d (Q : MvPolynomial (Fin 2) (ZMod p)) = (Int.castRingHom (ZMod p)) (coeff d P)
  rw [hcoeff, map_natCast, ZMod.natCast_zmod_val]

theorem exists_eq_zsmul_of_pushForm_eq_zero (p : ℕ) [NeZero p] (n : ℕ) (P : ↥(BinaryForm ℤ n))
    (hP : pushForm (Int.castRingHom (ZMod p)).toAddMonoidHom n P = 0) :
    ∃ P' : ↥(BinaryForm ℤ n), P = (p : ℤ) • P' := by
  classical
  have hdvd : ∀ d, (p : ℤ) ∣ coeff d (P : MvPolynomial (Fin 2) ℤ) := by
    intro d
    have h := congrArg (fun Q : ↥(BinaryForm (ZMod p) n) => coeff d (Q : MvPolynomial (Fin 2) (ZMod p))) hP
    simp only [Submodule.coe_zero, coeff_zero] at h
    change coeff d (pushCoeff (Int.castRingHom (ZMod p)).toAddMonoidHom (P : MvPolynomial (Fin 2) ℤ)) = 0 at h
    rw [coeff_pushCoeff] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
  let P' : MvPolynomial (Fin 2) ℤ := ∑ d ∈ (P : MvPolynomial (Fin 2) ℤ).support, monomial d (coeff d (P : MvPolynomial (Fin 2) ℤ) / p)
  have hcoeff : ∀ d, coeff d P' = coeff d (P : MvPolynomial (Fin 2) ℤ) / p := by
    intro d
    simp only [P', coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, Int.zero_ediv]
  have hP' : P' ∈ BinaryForm ℤ n := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    intro d hd
    have : coeff d (P : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
      intro h0; apply hd; rw [hcoeff, h0, Int.zero_ediv]
    exact (MvPolynomial.mem_homogeneousSubmodule n _).mp P.2 this
  refine ⟨⟨P', hP'⟩, Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)⟩
  rw [coeff_zsmul_val]
  change coeff d (P : MvPolynomial (Fin 2) ℤ) = (p : ℤ) * coeff d P'
  rw [hcoeff, Int.mul_ediv_cancel' (hdvd d)]

theorem exists_retraction (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    ∃ π : K →+ ZMod p, ∀ m : ℤ, π (m : K) = (m : ZMod p) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (ZMod p) K)
    (LinearMap.ker_eq_bot.mpr (algebraMap (ZMod p) K).injective)
  refine ⟨g.toAddMonoidHom, fun m => ?_⟩
  have h1 : (m : K) = Algebra.linearMap (ZMod p) K (m : ZMod p) := by
    rw [Algebra.linearMap_apply, map_intCast]
  rw [LinearMap.toAddMonoidHom_coe, h1, ← LinearMap.comp_apply, hg, LinearMap.id_apply]

theorem aux_cocycle {V : Type*} [AddCommGroup V] (f : V →+ V) (p : ℤ) (hinj : ∀ x : V, p • x = 0 → x = 0)
    (a b c A B C : V) (ha : A = p • a) (hb : B = p • b) (hc : C = p • c) (h : A = B + f C) : a = b + f c := by
  have : p • (a - (b + f c)) = 0 := by
    rw [zsmul_sub, zsmul_add, ← map_zsmul, ← ha, ← hb, ← hc, h, sub_self]
  exact sub_eq_zero.mp (hinj _ this)

theorem aux_range {V : Type*} [AddCommGroup V] (f : V →+ V) (p : ℤ) (x w A : V) (hA : A = p • x) (hw : f w - w = A) :
    p • x = f w - w := by rw [hw, hA]

theorem mem_range_conj_iff {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K SL(2, ℤ) V) (δ u : SL(2, ℤ)) (x : V) :
    x ∈ LinearMap.range (ρ (δ * u * δ⁻¹) - 1) ↔ ρ δ⁻¹ x ∈ LinearMap.range (ρ u - 1) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨ρ δ⁻¹ w, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply] at hw ⊢
    rw [← hw, map_sub, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  · rintro ⟨w, hw⟩
    refine ⟨ρ δ w, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply] at hw ⊢
    have : x = ρ δ (ρ u w - w) := by
      rw [hw, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [this, map_sub, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group

variable (N : ℕ) [NeZero N] (n : ℕ) (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 1600000 in
theorem main (hpN : ¬ p ∣ N) (hn : n < p) (K : Type*) [Field K] [CharP K p]
    (Φ : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) →+ coeffH1par ((binaryFormRepSL K n).comp (Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)),
      ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL K n).comp (Gamma0 N).subtype)),
        (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm K n)) g : MvPolynomial (Fin 2) K)
            = MvPolynomial.map (Int.castRingHom K) (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (coeffH1parMk _ z) = coeffH1parMk _ w)
    (y : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) (hy : Φ y = 0) :
    ∃ y' : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype), y = (p : ℤ) • y' := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_Gamma0 N)
  haveI : Fintype (SL(2, ℤ) ⧸ Gamma0 N) := Fintype.ofFinite _
  have hρZ' : ∀ g : Gamma0 N, ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) g = binaryFormRepSL ℤ n (g : SL(2, ℤ)) :=
    fun g => rfl
  have hρK' : ∀ g : Gamma0 N, ((binaryFormRepSL K n).comp (Gamma0 N).subtype) g = binaryFormRepSL K n (g : SL(2, ℤ)) :=
    fun g => rfl
  have hρF' : ∀ g : Gamma0 N, ((binaryFormRepSL (ZMod p) n).comp (Gamma0 N).subtype) g = binaryFormRepSL (ZMod p) n (g : SL(2, ℤ)) :=
    fun g => rfl
  have htf : ∀ x : ↥(BinaryForm ℤ n), (p : ℤ) • x = 0 → x = 0 := fun x hx =>
    (smul_eq_zero.mp hx).resolve_left (by exact_mod_cast hp.ne_zero)
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) y
  let m₁ : Gamma0 N := ⟨-1, neg_one_mem_Gamma0 N⟩
  have hm₁ : m₁ = ⟨-1, neg_one_mem_Gamma0 N⟩ := rfl
  rcases Nat.even_or_odd n with heven | hodd
  swap
  ·
    refine ⟨0, ?_⟩
    rw [smul_zero]
    have hρm : ∀ v, ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) m₁ v = -v := fun v => by
      rw [hρZ']
      show binaryFormRepSL ℤ n (-1) v = -v
      rw [binaryFormRepSL_neg_one_apply, Odd.neg_one_pow hodd]
      exact neg_one_smul ℤ v
    have hz := z.2.1
    have htwo : ((2 : ℤ) • z).1 ∈ coeffCoboundaries ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) := by
      rw [mem_coeffCoboundaries_iff]
      refine ⟨-((z.1) m₁), funext fun g => ?_⟩
      have hcomm : g * m₁ = m₁ * g := Subtype.ext (by simp [hm₁])
      have h1 := hz g m₁
      have h2 := hz m₁ g
      rw [hcomm, h2, hρm] at h1
      have h4 : z.1 g + z.1 g = z.1 m₁ - ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) g (z.1 m₁) := by
        rw [eq_sub_iff_add_eq]
        calc z.1 g + z.1 g + ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) g (z.1 m₁)
            = z.1 g + (z.1 g + ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) g (z.1 m₁)) := by abel
          _ = z.1 g + (z.1 m₁ + -z.1 g) := by rw [h1]
          _ = z.1 m₁ := by abel
      rw [map_neg]
      show _ = (2 : ℤ) • z.1 g
      rw [two_zsmul, h4]
      abel
    have h0 : (2 : ℤ) • coeffH1parMk ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) z = 0 := by
      rw [← map_zsmul, coeffH1parMk_eq_zero_iff]
      exact htwo
    exact coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero n N 2 two_ne_zero _ h0
  ·
    have hgen : ∀ (R : Type) [CommRing R] (P : ↥(BinaryForm R n)), ((-1 : R) ^ n) • P = P := by
      intro R _ P
      rw [Even.neg_one_pow heven, one_smul]
    have hρm1 : binaryFormRepSL ℤ n (-1) = 1 := by
      refine LinearMap.ext fun P => ?_
      rw [Module.End.one_apply]
      exact (binaryFormRepSL_neg_one_apply ℤ n P).trans (hgen ℤ P)

    let κ : ℤ →+ K := (Int.castRingHom K).toAddMonoidHom
    have hκ : κ = (Int.castRingHom K).toAddMonoidHom := rfl
    let cz : ℤ →+ ZMod p := (Int.castRingHom (ZMod p)).toAddMonoidHom
    have hcz : cz = (Int.castRingHom (ZMod p)).toAddMonoidHom := rfl
    obtain ⟨π, hπ⟩ := exists_retraction p K
    have hπκ : π.comp κ = cz := by
      refine AddMonoidHom.ext_int ?_
      exact hπ 1

    obtain ⟨w, hw1, hw2⟩ := hΦ z
    have hwv : ∀ g, w.1 g = pushForm κ n (z.1 g) := fun g =>
      Subtype.ext ((hw1 g).trans (map_eq_pushCoeff _ _))
    rw [hw2, coeffH1parMk_eq_zero_iff, mem_coeffCoboundaries_iff] at hy
    obtain ⟨vK, hvK⟩ := hy

    let ubar : ↥(BinaryForm (ZMod p) n) := pushForm π n vK
    have hubar : ubar = pushForm π n vK := rfl
    have hzbar : ∀ g : Gamma0 N, pushForm cz n (z.1 g) = binaryFormRepSL (ZMod p) n (g : SL(2, ℤ)) ubar - ubar := by
      intro g
      have h := congrFun hvK g
      change binaryFormRepSL K n (g : SL(2, ℤ)) vK - vK = w.1 g at h
      rw [hwv] at h
      have h2 := congrArg (pushForm π n) h
      rw [pushForm_sub, pushForm_binaryFormRepSL, pushForm_pushForm, hπκ] at h2
      exact h2.symm

    obtain ⟨u, hu⟩ := exists_pushForm_intCast_eq p n ubar
    let du : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) :=
      ⟨fun g => ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) g u - u,
        coeffCoboundaries_le_coeffParabolicCocycles _ ((mem_coeffCoboundaries_iff _ _).mpr ⟨u, rfl⟩)⟩
    have hdu_cob : du.1 ∈ coeffCoboundaries ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) :=
      (mem_coeffCoboundaries_iff _ _).mpr ⟨u, rfl⟩
    let z₁ : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) := z - du
    have hz₁ : z₁ = z - du := rfl
    have hz₁v : ∀ g, z₁.1 g = z.1 g - (binaryFormRepSL ℤ n (g : SL(2, ℤ)) u - u) := fun g => rfl
    have hmk : coeffH1parMk _ z = coeffH1parMk _ z₁ := by
      rw [mk_eq_mk_iff]
      have hzz : z - z₁ = du := by
        first
          | exact sub_sub_cancel z du
          | (rw [hz₁]; abel)
          | (rw [hz₁]; exact sub_sub_cancel _ _)
      rw [hzz]
      exact hdu_cob

    have hz₁0 : ∀ g, pushForm cz n (z₁.1 g) = 0 := by
      intro g
      rw [hz₁v, pushForm_sub, pushForm_sub, pushForm_binaryFormRepSL, hu, hzbar, sub_self]
    choose Y hY using fun g => exists_eq_zsmul_of_pushForm_eq_zero p n (z₁.1 g) (hz₁0 g)

    have hz₁coc := z₁.2.1
    have hYcoc : Y ∈ coeffCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) := by
      intro g h
      exact aux_cocycle (((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) g).toAddMonoidHom (p : ℤ) htf
        _ _ _ _ _ _ (hY (g * h)) (hY g) (hY h) (hz₁coc g h)

    let δ : SL(2, ℤ) ⧸ (Gamma0 N) → SL(2, ℤ) := fun q => (Quotient.out q)⁻¹
    have hδ : δ = fun q => (Quotient.out q)⁻¹ := rfl
    let a : SL(2, ℤ) ⧸ (Gamma0 N) → ℕ := fun q => cuspWidth N (δ q)
    have ha : a = fun q => cuspWidth N (δ q) := rfl
    have hua : ∀ q, δ q * ModularGroup.T ^ (a q : ℤ) * (δ q)⁻¹ ∈ Gamma0 N := fun q => (cuspWidth_spec N (δ q)).2
    let uq : SL(2, ℤ) ⧸ (Gamma0 N) → Gamma0 N := fun q => ⟨δ q * ModularGroup.T ^ (a q : ℤ) * (δ q)⁻¹, hua q⟩
    have huqdef : uq = fun q => ⟨δ q * ModularGroup.T ^ (a q : ℤ) * (δ q)⁻¹, hua q⟩ := rfl
    have hutr : ∀ q, (((uq q : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := fun q => by
      show ((δ q * ModularGroup.T ^ (a q : ℤ) * (δ q)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
      rw [trace_conj_T_zpow]; norm_num

    have hpa : ∀ q, ¬ (p : ℤ) ∣ (a q : ℤ) := by
      intro q hdiv
      have hadvd : (a q : ℤ) ∣ (N : ℤ) := cuspWidth_dvd N (δ q) (conj_T_zpow_mem_Gamma0 N (δ q))
      exact hpN (Int.natCast_dvd_natCast.mp (hdiv.trans hadvd))

    have hWq : ∀ q, ∃ W : ↥(BinaryForm ℤ n), Y (uq q) = binaryFormRepSL ℤ n (uq q : SL(2, ℤ)) W - W := by
      intro q
      obtain ⟨wq, hwq⟩ := z₁.2.2 (uq q) (hutr q)

      have h1 : (p : ℤ) • Y (uq q) ∈ LinearMap.range (binaryFormRepSL ℤ n (δ q * ModularGroup.T ^ (a q : ℤ) * (δ q)⁻¹) - 1) := by
        refine ⟨wq, ?_⟩
        rw [← hY (uq q), ← hwq]
        rfl
      rw [mem_range_conj_iff] at h1
      rw [LinearMap.map_smul_of_tower] at h1
      have h2 := mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem n hp hn (hpa q) _ h1
      obtain ⟨W, hW⟩ := (mem_range_conj_iff (binaryFormRepSL ℤ n) (δ q) _ (Y (uq q))).mpr h2
      refine ⟨W, ?_⟩
      rw [LinearMap.sub_apply, Module.End.one_apply] at hW
      exact hW.symm

    have hYpar : IsParabolicCocycle ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) Y := by
      intro γ hγ
      obtain ⟨ε, σ, h, hε, hγeq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
      let q : SL(2, ℤ) ⧸ Gamma0 N := QuotientGroup.mk σ⁻¹
      have hq : q = QuotientGroup.mk σ⁻¹ := rfl
      have hg₀ : σ * (δ q)⁻¹ ∈ Gamma0 N := by
        have hmk : (QuotientGroup.mk (Quotient.out q) : SL(2, ℤ) ⧸ Gamma0 N) = QuotientGroup.mk σ⁻¹ := by
          rw [hq]; exact Quotient.out_eq _
        have h2 : (Quotient.out q)⁻¹ * σ⁻¹ ∈ Gamma0 N := QuotientGroup.eq.mp hmk
        have h3 := Subgroup.inv_mem _ h2
        rw [mul_inv_rev, inv_inv, inv_inv] at h3
        simpa only [hδ, inv_inv] using h3
      let g₀ : Gamma0 N := ⟨σ * (δ q)⁻¹, hg₀⟩
      have hg₀def : g₀ = ⟨σ * (δ q)⁻¹, hg₀⟩ := rfl
      have hσ : σ = (g₀ : SL(2, ℤ)) * δ q := by simp [hg₀def]
      have hεmem : ε ∈ Gamma0 N := hε.elim (fun h => h ▸ Subgroup.one_mem _) (fun h => h ▸ neg_one_mem_Gamma0 N)
      have hconj_mem : δ q * ModularGroup.T ^ h * (δ q)⁻¹ ∈ Gamma0 N := by
        have e1 : δ q * ModularGroup.T ^ h * (δ q)⁻¹ = (g₀ : SL(2, ℤ))⁻¹ * (ε⁻¹ * (γ : SL(2, ℤ))) * g₀ := by
          rw [hγeq, hσ]; group
        rw [e1]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ g₀.2)
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ hεmem) γ.2)) g₀.2
      obtain ⟨k, hk⟩ := cuspWidth_dvd N (δ q) hconj_mem
      have hpow : δ q * ModularGroup.T ^ h * (δ q)⁻¹ = ((uq q : Gamma0 N) : SL(2, ℤ)) ^ k := by
        rw [hk, conj_T_zpow_mul]
      let γ' : Gamma0 N := g₀ * (uq q) ^ k * g₀⁻¹
      have hγ'def : γ' = g₀ * (uq q) ^ k * g₀⁻¹ := rfl
      have hγ'coe : (γ' : SL(2, ℤ)) = σ * ModularGroup.T ^ h * σ⁻¹ := by
        simp only [hγ'def, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, ← hpow, hσ]
        group
      obtain ⟨W, hW⟩ := hWq q
      have hW' : Y (uq q) = ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (uq q) W - W := hW
      have hzp : ∀ v ∈ Subgroup.zpowers (uq q), Y v = ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) v W - W := fun v hv =>
        mem_range_of_mem_closure hYcoc W (s := {uq q}) (fun v hv => by rw [Set.mem_singleton_iff.mp hv]; exact hW')
          (by rwa [Subgroup.zpowers_eq_closure] at hv)
      have hpar' : Y γ' ∈ LinearMap.range (((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) γ' - 1) :=
        apply_conj_mem_range hYcoc (hzp _ (Subgroup.zpow_mem_zpowers _ _)) g₀
      rcases hε with rfl | rfl
      · have : γ = γ' := Subtype.ext (by rw [hγ'coe, hγeq, one_mul])
        rw [this]; exact hpar'
      · have hγm : γ = m₁ * γ' := Subtype.ext (by rw [Subgroup.coe_mul, hγ'coe, hγeq])
        have hρm₁ : ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) m₁ = 1 := by rw [hρZ']; exact hρm1
        have hYm₁ : Y m₁ = 0 := by
          have h1 := hYcoc m₁ m₁
          have hmm : m₁ * m₁ = 1 := Subtype.ext (by simp [hm₁])
          rw [hmm, coeffCocycles_apply_one hYcoc, hρm₁, Module.End.one_apply] at h1
          apply Subtype.ext; ext d
          have h2 := congrArg (fun P : ↥(BinaryForm ℤ n) => coeff d (P : MvPolynomial (Fin 2) ℤ)) h1
          simp only [Submodule.coe_add, coeff_add, Submodule.coe_zero, coeff_zero] at h2
          simp only [Submodule.coe_zero, coeff_zero]
          omega
        rw [hγm, hYcoc m₁ γ', hYm₁, zero_add, hρm₁, Module.End.one_apply, map_mul, hρm₁, one_mul]
        exact hpar'

    let Yp : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) := ⟨Y, hYcoc, hYpar⟩
    have hYp : Yp = ⟨Y, hYcoc, hYpar⟩ := rfl
    refine ⟨coeffH1parMk _ Yp, ?_⟩
    rw [hmk, ← map_zsmul]
    congr 1
    apply Subtype.ext; funext g
    exact hY g

end HeckeEis.ModPAux
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.ZQAux"
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.ZQAux"

end
p2m_reactivate "P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.CoeffMapAux P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero.HeckeEis.ZQAux"

open scoped MatrixGroups in
theorem solution (N : ℕ) [NeZero N] (n : ℕ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hn : n < p)
    (K : Type*) [Field K] [CharP K p]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g : MvPolynomial (Fin 2) K)
            = MvPolynomial.map (Int.castRingHom K) (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w))
    (y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) (hy : Φ y = 0) :
    ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y' :=
  HeckeEis.ModPAux.main N n p hpN hn K Φ hΦ y hy

#print axioms solution

end S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero
end P2MW
export P2MW.S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero (solution)
