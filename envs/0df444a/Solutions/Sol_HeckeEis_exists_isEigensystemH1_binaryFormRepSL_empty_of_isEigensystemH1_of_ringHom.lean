-- Prove2me | solution 1 for HeckeEis.exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7c5489cd-8259-54ae-bfe3-f39d78ad24db

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom

set_option autoImplicit false

namespace EigenCompletion

open CongruenceSubgroup HeckeEis Polynomial
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

@[scoped simp] theorem heckeLin_apply (z : Gamma0 N → V) : heckeLin N ℓ ρ a z = coeffHeckeFun N ℓ ρ a z := rfl

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

theorem heckeH1_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (hne : ℓ ≠ ℓ') {a a' : V →ₗ[K] V}
    (ha : IsCompat N ℓ ρ a) (ha' : IsCompat N ℓ' ρ a') (hcomm : a ∘ₗ a' = a' ∘ₗ a) (x : coeffH1 ρ) :
    heckeH1 ha (heckeH1 ha' x) = heckeH1 ha' (heckeH1 ha x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [heckeH1_mk, heckeH1_mk, heckeH1_mk, heckeH1_mk, coeffH1Mk_eq_iff]
  simp only [coe_heckeZ1]
  haveI : NeZero (ℓ * ℓ') := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  have hℓℓ' : ¬ ℓ ∣ ℓ' := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp h)
  have hℓ'ℓ : ¬ ℓ' ∣ ℓ := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ' hℓ).mp h).symm
  have h1 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ ℓ' (ℓ * ℓ')
    hℓ hℓN hℓℓ' rfl ρ a a' ha ha' z.2
  have h2 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ' ℓ (ℓ * ℓ')
    hℓ' hℓ'N hℓ'ℓ (Nat.mul_comm ℓ ℓ') ρ a' a ha' ha z.2
  rw [← hcomm] at h2
  have h3 := (coeffCoboundaries ρ).sub_mem h1 h2
  convert h3 using 1
  abel

end Induced

section Sym

variable (R : Type) [CommRing R] (N : ℕ) (n : ℕ)

noncomputable abbrev ρSym : Representation R (Gamma0 N) ↥(BinaryForm R n) :=
  (binaryFormRepSL R n).comp (Gamma0 N).subtype

def dMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), 0; 0, 1]

theorem dMat_comm (ℓ ℓ' : ℕ) : dMat ℓ * dMat ℓ' = dMat ℓ' * dMat ℓ := by
  simp only [dMat, Matrix.mul_fin_two, mul_zero, add_zero, zero_add, mul_one, mul_comm]

theorem binaryFormAlphaAdj_eq (ℓ : ℕ) : binaryFormAlphaAdj R n ℓ = binaryFormRep R n (dMat ℓ) := rfl

theorem isCompat_sym (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj R n N ℓ u

theorem alpha_comm (ℓ ℓ' : ℕ) :
    binaryFormAlphaAdj R n ℓ ∘ₗ binaryFormAlphaAdj R n ℓ' =
      binaryFormAlphaAdj R n ℓ' ∘ₗ binaryFormAlphaAdj R n ℓ := by
  rw [binaryFormAlphaAdj_eq, binaryFormAlphaAdj_eq]
  change binaryFormRep R n (dMat ℓ) * binaryFormRep R n (dMat ℓ') =
    binaryFormRep R n (dMat ℓ') * binaryFormRep R n (dMat ℓ)
  rw [← map_mul, ← map_mul, dMat_comm]

abbrev H1 : Type := coeffH1 (ρSym R N n)

noncomputable def TH (ℓ : ℕ) [NeZero ℓ] : H1 R N n →ₗ[R] H1 R N n :=
  heckeH1 (isCompat_sym R N n ℓ)

theorem isCoeffHeckeOnH1_TH (ℓ : ℕ) [NeZero ℓ] :
    IsCoeffHeckeOnH1 N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) (TH R N n ℓ) :=
  isCoeffHeckeOnH1_heckeH1 _

theorem TH_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) : Commute (TH R N n ℓ) (TH R N n ℓ') := by
  by_cases hne : ℓ = ℓ'
  · subst hne; exact Commute.refl _
  refine LinearMap.ext fun x => ?_
  exact heckeH1_comm hℓ hℓ' hℓN hℓ'N hne (isCompat_sym R N n ℓ) (isCompat_sym R N n ℓ')
    (alpha_comm R n ℓ ℓ') x

end Sym

section FiniteGen

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cocycle_apply_eq_zero_of_closure {G : Type*} [Group G] (ρ : Representation K G V)
    (z : ↥(coeffCocycles ρ)) (S : Set G) (hS : ∀ s ∈ S, (z : G → V) s = 0)
    (g : G) (hg : g ∈ Subgroup.closure S) : (z : G → V) g = 0 := by
  have hz := z.2
  have h1 : (z : G → V) 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ ihx ihy => rw [hz x y, ihx, ihy, map_zero, zero_add]
  | inv x _ ih =>
    have h := hz x x⁻¹
    rw [mul_inv_cancel, h1, ih, zero_add] at h
    have h2 : ρ x⁻¹ (ρ x ((z : G → V) x⁻¹)) = 0 := by rw [← h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

theorem exists_finset_closure_eq_top (N : ℕ) [NeZero N] :
    ∃ S : Finset (Gamma0 N), Subgroup.closure (S : Set (Gamma0 N)) = ⊤ := by
  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
      Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  exact hΓ.out

theorem moduleFinite_coeffH1 (N : ℕ) [NeZero N] [IsNoetherianRing K] [Module.Finite K V]
    (ρ : Representation K (Gamma0 N) V) : Module.Finite K (coeffH1 ρ) := by
  obtain ⟨S, hS⟩ := exists_finset_closure_eq_top N
  let ev : ↥(coeffCocycles ρ) →ₗ[K] (↥S → V) :=
    { toFun := fun z s => (z : Gamma0 N → V) s
      map_add' := fun z w => by ext s; rfl
      map_smul' := fun c z => by ext s; rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    refine Subtype.ext (funext fun g => ?_)
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    exact cocycle_apply_eq_zero_of_closure ρ z S (fun s hs => congrFun hz ⟨s, hs⟩) g hg
  haveI : Module.Finite K ↥(coeffCocycles ρ) := Module.Finite.of_injective ev hev
  exact Module.Finite.of_surjective (coeffH1Mk ρ) (coeffH1Mk_surjective ρ)

scoped instance moduleFinite_binaryForm [IsNoetherianRing K] (n : ℕ) : Module.Finite K ↥(BinaryForm K n) := by
  have hle : BinaryForm K n ≤ MvPolynomial.restrictTotalDegree (Fin 2) K n := fun φ hφ =>
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.mem_homogeneousSubmodule n φ).mp hφ).totalDegree_le
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end FiniteGen

section Substitution

theorem map_binarySubst {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (F : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (binarySubst R M F) = binarySubst S M (MvPolynomial.map f F) := by
  have key : (MvPolynomial.map f).comp (binarySubst R M : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R) =
      (binarySubst S M : MvPolynomial (Fin 2) S →+* MvPolynomial (Fin 2) S).comp (MvPolynomial.map f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_C, MvPolynomial.map_C]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_X, MvPolynomial.map_X, map_sum, map_mul,
        map_intCast]
  exact RingHom.congr_fun key F

end Substitution

section FpStructure

variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ]

noncomputable def cmap (l : κ →+ ZMod p) : MvPolynomial (Fin 2) κ →+ MvPolynomial (Fin 2) (ZMod p) :=
  { toFun := AddMonoidAlgebra.map l
    map_zero' := AddMonoidAlgebra.map_zero l
    map_add' := AddMonoidAlgebra.map_add l }

variable {p κ}

@[scoped simp] theorem coeff_cmap (l : κ →+ ZMod p) (F : MvPolynomial (Fin 2) κ) (m : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff m (cmap p κ l F) = l (MvPolynomial.coeff m F) :=
  rfl

theorem cmap_mem {n : ℕ} (l : κ →+ ZMod p) {F : MvPolynomial (Fin 2) κ} (hF : F ∈ BinaryForm κ n) :
    cmap p κ l F ∈ BinaryForm (ZMod p) n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hF ⊢
  intro d hd
  refine hF fun h0 => hd ?_
  rw [coeff_cmap, h0, map_zero]

theorem cmap_C_mul_map (l : κ →+ ZMod p) (c : κ) (G : MvPolynomial (Fin 2) ℤ) :
    cmap p κ l (MvPolynomial.C c * MvPolynomial.map (Int.castRingHom κ) G) =
      MvPolynomial.C (l c) * MvPolynomial.map (Int.castRingHom (ZMod p)) G := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_cmap, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
    MvPolynomial.coeff_map, eq_intCast, eq_intCast, mul_comm c, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul,
    mul_comm]

theorem cmap_monomial (l : κ →+ ZMod p) (d : Fin 2 →₀ ℕ) (c : κ) :
    cmap p κ l (MvPolynomial.monomial d c) = MvPolynomial.monomial d (l c) := by
  refine MvPolynomial.ext _ _ fun m => ?_
  classical
  rw [coeff_cmap, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs
  · rfl
  · exact map_zero l

theorem binarySubst_monomial_eq (R : Type*) [CommRing R] (M : Matrix (Fin 2) (Fin 2) ℤ)
    (d : Fin 2 →₀ ℕ) (c : R) :
    binarySubst R M (MvPolynomial.monomial d c) =
      MvPolynomial.C c * MvPolynomial.map (Int.castRingHom R) (binarySubst ℤ M (MvPolynomial.monomial d 1)) := by
  rw [map_binarySubst, MvPolynomial.map_monomial, map_one]
  conv_lhs => rw [← mul_one c, ← MvPolynomial.C_mul_monomial, map_mul, binarySubst_C]

theorem cmap_binarySubst (l : κ →+ ZMod p) (M : Matrix (Fin 2) (Fin 2) ℤ) (F : MvPolynomial (Fin 2) κ) :
    cmap p κ l (binarySubst κ M F) = binarySubst (ZMod p) M (cmap p κ l F) := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [binarySubst_monomial_eq κ M d (MvPolynomial.coeff d F), cmap_C_mul_map, cmap_monomial,
    binarySubst_monomial_eq (ZMod p) M d (l (MvPolynomial.coeff d F))]

variable (N n : ℕ)

noncomputable def cocycleCmap (l : κ →+ ZMod p) (z : ↥(coeffCocycles (ρSym κ N n))) :
    ↥(coeffCocycles (ρSym (ZMod p) N n)) :=
  ⟨fun g => ⟨cmap p κ l ((z : Gamma0 N → ↥(BinaryForm κ n)) g : MvPolynomial (Fin 2) κ),
      cmap_mem l ((z : Gamma0 N → ↥(BinaryForm κ n)) g).2⟩, by
    intro g h
    apply Subtype.ext
    have hz := congrArg Subtype.val (z.2 g h)
    change ((((z : Gamma0 N → ↥(BinaryForm κ n)) (g * h) : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ)) =
      ((z : Gamma0 N → ↥(BinaryForm κ n)) g : MvPolynomial (Fin 2) κ) +
        binarySubst κ ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          ((z : Gamma0 N → ↥(BinaryForm κ n)) h : MvPolynomial (Fin 2) κ) at hz
    change cmap p κ l (((z : Gamma0 N → ↥(BinaryForm κ n)) (g * h) : MvPolynomial (Fin 2) κ)) =
      cmap p κ l ((z : Gamma0 N → ↥(BinaryForm κ n)) g : MvPolynomial (Fin 2) κ) +
        binarySubst (ZMod p) ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          (cmap p κ l ((z : Gamma0 N → ↥(BinaryForm κ n)) h : MvPolynomial (Fin 2) κ))
    rw [hz, map_add, cmap_binarySubst]⟩

theorem coe_cocycleCmap_apply (l : κ →+ ZMod p) (z : ↥(coeffCocycles (ρSym κ N n))) (g : Gamma0 N) :
    (((cocycleCmap N n l z : Gamma0 N → ↥(BinaryForm (ZMod p) n)) g : ↥(BinaryForm (ZMod p) n)) :
      MvPolynomial (Fin 2) (ZMod p)) =
      cmap p κ l ((z : Gamma0 N → ↥(BinaryForm κ n)) g : MvPolynomial (Fin 2) κ) :=
  rfl

structure IsCoeffMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (Φ : H1 R N n →+ H1 R' N n) : Prop where
  mk_spec : ∀ z : ↥(coeffCocycles (ρSym R N n)), ∃ w : ↥(coeffCocycles (ρSym R' N n)),
    (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm R' n)) g : MvPolynomial (Fin 2) R') =
      MvPolynomial.map φ (((z : Gamma0 N → ↥(BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
    Φ (coeffH1Mk _ z) = coeffH1Mk _ w
  smul : ∀ (c : R) (x : H1 R N n), Φ (c • x) = φ c • Φ x
  hecke : ∀ (ℓ : ℕ) [NeZero ℓ] (x : H1 R N n), Φ (TH R N n ℓ x) = TH R' N n ℓ (Φ x)

theorem exists_isCoeffMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    ∃ Φ : H1 R N n →+ H1 R' N n, IsCoeffMap N n φ Φ := by
  obtain ⟨Φ, h1, h2, h3, -, -⟩ := exists_coeffH1_map_ringHom_binaryFormRepSL φ n N
  exact ⟨Φ, ⟨h1, h2, fun ℓ _ x => h3 ℓ (TH R N n ℓ) (TH R' N n ℓ) (isCoeffHeckeOnH1_TH R N n ℓ)
    (isCoeffHeckeOnH1_TH R' N n ℓ) x⟩⟩

variable {N n}

theorem IsCoeffMap.apply_mk_eq {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'}
    {Φ : H1 R N n →+ H1 R' N n} (hΦ : IsCoeffMap N n φ Φ) (z : ↥(coeffCocycles (ρSym R N n)))
    (w : ↥(coeffCocycles (ρSym R' N n)))
    (hw : ∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm R' n)) g : MvPolynomial (Fin 2) R') =
      MvPolynomial.map φ (((z : Gamma0 N → ↥(BinaryForm R n)) g : MvPolynomial (Fin 2) R))) :
    Φ (coeffH1Mk _ z) = coeffH1Mk _ w := by
  obtain ⟨w', hw', hΦz⟩ := hΦ.mk_spec z
  rw [hΦz]
  congr 1
  exact Subtype.ext (funext fun g => Subtype.ext ((hw' g).trans (hw g).symm))

theorem mem_span_range [NeZero N] [Algebra (ZMod p) κ] {Φ : H1 (ZMod p) N n →+ H1 κ N n}
    (hΦ : IsCoeffMap N n (algebraMap (ZMod p) κ) Φ) (x : H1 κ N n) :
    x ∈ Submodule.span κ (Set.range Φ) := by
  classical
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x

  let B := Module.Basis.ofVectorSpace (ZMod p) κ
  let crd : Module.Basis.ofVectorSpaceIndex (ZMod p) κ → (κ →+ ZMod p) := fun b => (B.coord b).toAddMonoidHom
  have crd_apply : ∀ b (c : κ), crd b c = B.repr c b := fun b c => rfl

  let zc : Module.Basis.ofVectorSpaceIndex (ZMod p) κ → ↥(coeffCocycles (ρSym (ZMod p) N n)) :=
    fun b => cocycleCmap N n (crd b) z

  obtain ⟨S, hS⟩ := exists_finset_closure_eq_top N
  let J : Finset (Module.Basis.ofVectorSpaceIndex (ZMod p) κ) :=
    S.biUnion fun s => (((z : Gamma0 N → ↥(BinaryForm κ n)) s : MvPolynomial (Fin 2) κ).support).biUnion
      fun m => (B.repr (MvPolynomial.coeff m ((z : Gamma0 N → ↥(BinaryForm κ n)) s : MvPolynomial (Fin 2) κ))).support

  have hzero : ∀ b, b ∉ J → zc b = 0 := by
    intro b hb
    have hgen : ∀ s ∈ (S : Set (Gamma0 N)), (zc b : Gamma0 N → ↥(BinaryForm (ZMod p) n)) s = 0 := by
      intro s hs
      apply Subtype.ext
      refine MvPolynomial.ext _ _ fun m => ?_
      rw [coe_cocycleCmap_apply, coeff_cmap, crd_apply, Submodule.coe_zero, MvPolynomial.coeff_zero]
      by_contra hne
      apply hb
      refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_biUnion.mpr ⟨m, ?_, Finsupp.mem_support_iff.mpr hne⟩⟩
      rw [MvPolynomial.mem_support_iff]
      intro h0
      rw [h0, map_zero, Finsupp.zero_apply] at hne
      exact hne rfl
    apply Subtype.ext
    funext g
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    exact cocycle_apply_eq_zero_of_closure _ (zc b) S hgen g hg

  have hw : ∀ b, ∃ w : ↥(coeffCocycles (ρSym κ N n)),
      (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm κ n)) g : MvPolynomial (Fin 2) κ) =
        MvPolynomial.map (algebraMap (ZMod p) κ)
          (((zc b : Gamma0 N → ↥(BinaryForm (ZMod p) n)) g : MvPolynomial (Fin 2) (ZMod p)))) ∧
      Φ (coeffH1Mk _ (zc b)) = coeffH1Mk _ w := fun b => hΦ.mk_spec (zc b)
  choose w hwval hwΦ using hw

  have hrec : z = ∑ b ∈ J, (B b : κ) • w b := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_sum, MvPolynomial.coeff_sum]
    simp only [Submodule.coe_smul, Pi.smul_apply, MvPolynomial.coeff_smul, hwval, MvPolynomial.coeff_map,
      smul_eq_mul]
    set c : κ := MvPolynomial.coeff m (((z : Gamma0 N → ↥(BinaryForm κ n)) g : ↥(BinaryForm κ n)) :
      MvPolynomial (Fin 2) κ) with hc
    have hsupp : (B.repr c).support ⊆ J := by
      intro b hb
      by_contra hbJ
      have h0 := hzero b hbJ
      have : B.repr c b = 0 := by
        have h1 : MvPolynomial.coeff m ((((zc b : Gamma0 N → ↥(BinaryForm (ZMod p) n)) g :
            ↥(BinaryForm (ZMod p) n)) : MvPolynomial (Fin 2) (ZMod p))) = B.repr c b := by
          rw [coe_cocycleCmap_apply, coeff_cmap, crd_apply]
        rw [← h1, h0]
        rfl
      exact (Finsupp.mem_support_iff.mp hb) this
    calc c = Finsupp.linearCombination (ZMod p) B (B.repr c) := (B.linearCombination_repr c).symm
      _ = ∑ b ∈ (B.repr c).support, B.repr c b • (B b : κ) := Finsupp.linearCombination_apply _ _
      _ = ∑ b ∈ J, B.repr c b • (B b : κ) :=
          Finset.sum_subset hsupp fun b _ hb => by rw [Finsupp.notMem_support_iff.mp hb, zero_smul]
      _ = ∑ b ∈ J, (B b : κ) * algebraMap (ZMod p) κ (B.repr c b) :=
          Finset.sum_congr rfl fun b _ => by rw [Algebra.smul_def, mul_comm]
  rw [hrec, map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [map_smul, ← hwΦ b]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end FpStructure

section Splitting

theorem mem_integralClosure_of_mem_roots {g : ℤ[X]} (hg : g.Monic) {z : ℂ}
    (hz : z ∈ (g.map (algebraMap ℤ ℂ)).roots) : z ∈ integralClosure ℤ ℂ := by
  rw [mem_integralClosure_iff]
  refine ⟨g, hg, ?_⟩
  have hne : g.map (algebraMap ℤ ℂ) ≠ 0 := (hg.map _).ne_zero
  have := (mem_roots hne).mp hz
  rwa [IsRoot.def, eval_map, ← aeval_def] at this

theorem splits_map_integralClosure {g : ℤ[X]} (hg : g.Monic) :
    Splits (g.map (algebraMap ℤ (integralClosure ℤ ℂ))) := by
  let i : integralClosure ℤ ℂ →+* ℂ := (integralClosure ℤ ℂ).val.toRingHom
  have hi : Function.Injective i := Subtype.val_injective
  have hmap : (g.map (algebraMap ℤ (integralClosure ℤ ℂ))).map i = g.map (algebraMap ℤ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  refine Splits.of_splits_map_of_injective hi ?_ ?_
  · rw [hmap]
    exact IsAlgClosed.splits _
  · intro a ha
    rw [hmap] at ha
    exact ⟨⟨a, mem_integralClosure_of_mem_roots hg ha⟩, rfl⟩

theorem splits_map_intCast_of_ringHom_integralClosure {κ : Type*} [Field κ]
    (φ : integralClosure ℤ ℂ →+* κ) {g : ℤ[X]} (hg : g.Monic) :
    Splits (g.map (Int.castRingHom κ)) := by
  have h := (splits_map_integralClosure hg).map φ
  rw [Polynomial.map_map] at h
  convert h using 2
  exact RingHom.ext_int _ _

theorem splits_map_of_monic_zmod {p : ℕ} [Fact p.Prime] {κ : Type*} [Field κ]
    (φ : integralClosure ℤ ℂ →+* κ) (ι : ZMod p →+* κ) {P : (ZMod p)[X]} (hP : P.Monic) :
    Splits (P.map ι) := by
  have hlift : P ∈ Polynomial.lifts (Int.castRingHom (ZMod p)) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ (ZMod.ringHom_surjective _) P
  obtain ⟨Q, hQP, -, hQmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP
  have h := splits_map_intCast_of_ringHom_integralClosure φ hQmonic
  have hcomp : ι.comp (Int.castRingHom (ZMod p)) = Int.castRingHom κ := RingHom.ext_int _ _
  rw [← hQP, Polynomial.map_map, hcomp]
  exact h

end Splitting

section Annihilator

variable {p : ℕ} [Fact p.Prime] {κ : Type} [Field κ] [Algebra (ZMod p) κ] {N n : ℕ}

theorem IsCoeffMap.apply_aeval {Φ : H1 (ZMod p) N n →+ H1 κ N n}
    (hΦ : IsCoeffMap N n (algebraMap (ZMod p) κ) Φ) (ℓ : ℕ) [NeZero ℓ] (Q : (ZMod p)[X])
    (y : H1 (ZMod p) N n) :
    Φ (aeval (TH (ZMod p) N n ℓ) Q y) = aeval (TH κ N n ℓ) (Q.map (algebraMap (ZMod p) κ)) (Φ y) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply, map_add, hP, hQ, Polynomial.map_add, map_add,
      LinearMap.add_apply]
  | monomial i c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, hΦ.smul]
    congr 1
    induction i generalizing y with
    | zero => rfl
    | succ i ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hΦ.hecke]

theorem exists_monic_splits_aeval_TH_eq_zero [NeZero N] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ)
    (ℓ : ℕ) [NeZero ℓ] :
    ∃ P : κ[X], P.Monic ∧ P.Splits ∧ aeval (TH κ N n ℓ) P = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_isCoeffMap N n (algebraMap (ZMod p) κ)
  haveI : Module.Finite (ZMod p) (H1 (ZMod p) N n) := moduleFinite_coeffH1 N _
  let P₀ : (ZMod p)[X] := (TH (ZMod p) N n ℓ).charpoly
  refine ⟨P₀.map (algebraMap (ZMod p) κ), (LinearMap.charpoly_monic _).map _,
    splits_map_of_monic_zmod φ _ (LinearMap.charpoly_monic _), ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  have hx := mem_span_range hΦ x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [← hΦ.apply_aeval, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero]
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

end Annihilator

section LinAlg

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_apply_mem (T : V →ₗ[K] V) (W : Submodule K V) (hW : ∀ w ∈ W, T w ∈ W) (Q : K[X])
    {w : V} (hw : w ∈ W) : aeval T Q w ∈ W := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply]; exact W.add_mem hP hQ
  | monomial i c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine W.smul_mem c ?_
    induction i with
    | zero => exact hw
    | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih

theorem eq_zero_of_aeval_prod_eq_zero (T : V →ₗ[K] V) (W : Submodule K V) (hW : ∀ w ∈ W, T w ∈ W)
    (s : Multiset K) (hs : ∀ a ∈ s, ∀ w ∈ W, T w = a • w → w = 0) :
    ∀ w ∈ W, aeval T ((s.map fun a => X - C a).prod) w = 0 → w = 0 := by
  induction s using Multiset.induction with
  | empty =>
    intro w _ h
    rwa [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_apply] at h
  | cons a s ih =>
    intro w hw h
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C,
      LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h
    have hmem : aeval T ((s.map fun a => X - C a).prod) w ∈ W := aeval_apply_mem T W hW _ hw
    have h0 := hs a (Multiset.mem_cons_self a s) _ hmem h
    exact ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb)) w hw h0

theorem exists_common_eigenvector_of_splits [FiniteDimensional K V] {ι : Type*} (T : ι → V →ₗ[K] V)
    (hT : ∀ i j, Commute (T i) (T j))
    (hann : ∀ i, ∃ P : K[X], P.Monic ∧ P.Splits ∧ aeval (T i) P = 0) :
    ∀ (d : ℕ) (W : Submodule K V), Module.finrank K W = d → W ≠ ⊥ → (∀ i, ∀ w ∈ W, T i w ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hstab
  by_cases hscalar : ∀ i, ∃ c : K, ∀ w ∈ W, T i w = c • w
  · obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    refine ⟨v, hvW, hv0, fun i => ?_⟩
    obtain ⟨c, hc⟩ := hscalar i
    exact ⟨c, hc v hvW⟩
  obtain ⟨i, hi⟩ := not_forall.mp hscalar
  obtain ⟨P, hPmonic, hPsplits, hPT⟩ := hann i

  have hroot : ∃ a ∈ P.roots, ∃ w ∈ W, T i w = a • w ∧ w ≠ 0 := by
    by_contra hnone
    have hinj : ∀ a ∈ P.roots, ∀ w ∈ W, T i w = a • w → w = 0 := by
      intro a ha w hw h
      by_contra hw0
      exact hnone ⟨a, ha, w, hw, h, hw0⟩
    have hall : ∀ w ∈ W, w = 0 := by
      intro w hw
      refine eq_zero_of_aeval_prod_eq_zero (T i) W (hstab i) P.roots hinj w hw ?_
      rw [← hPsplits.eq_prod_roots_of_monic hPmonic, hPT, LinearMap.zero_apply]
    exact hW ((Submodule.eq_bot_iff W).mpr hall)
  obtain ⟨a, -, w₀, hw₀W, hw₀, hw₀0⟩ := hroot

  let W' : Submodule K V := W ⊓ LinearMap.ker (T i - a • 1)
  have hW'le : W' ≤ W := inf_le_left
  have hmemW' : ∀ w, w ∈ W' ↔ w ∈ W ∧ T i w = a • w := by
    intro w
    change w ∈ W ⊓ LinearMap.ker (T i - a • 1) ↔ _
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hW'ne : W' ≠ ⊥ := by
    intro h
    have : w₀ ∈ W' := (hmemW' w₀).mpr ⟨hw₀W, hw₀⟩
    rw [h, Submodule.mem_bot] at this
    exact hw₀0 this
  have hW'lt : W' < W := by
    refine lt_of_le_of_ne hW'le fun heq => hi ⟨a, fun w hw => ?_⟩
    have : w ∈ W' := heq ▸ hw
    exact ((hmemW' w).mp this).2
  have hstab' : ∀ j, ∀ w ∈ W', T j w ∈ W' := by
    intro j w hw
    obtain ⟨hwW, hTw⟩ := (hmemW' w).mp hw
    refine (hmemW' _).mpr ⟨hstab j w hwW, ?_⟩
    rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply, hTw, map_smul]
  haveI : FiniteDimensional K W := inferInstance
  have hlt : Module.finrank K W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hW'lt
  obtain ⟨v, hvW', hv0, hv⟩ := ih _ hlt W' rfl hW'ne hstab'
  exact ⟨v, hW'le hvW', hv0, hv⟩

end LinAlg

section Main

variable (N : ℕ)

abbrev PrimeAway : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N}

scoped instance neZero_primeAway (i : PrimeAway N) : NeZero (i : ℕ) := ⟨i.2.1.ne_zero⟩

end Main

end EigenCompletion
p2m_reactivate "P2MW.S_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom.EigenCompletion"

open EigenCompletion CongruenceSubgroup HeckeEis Polynomial in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ mu : ℕ → κ,
      HeckeEis.IsEigensystemH1 N
        ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) ∅ mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → mu ℓ = lam ℓ := by
  classical
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  obtain ⟨x, hx0, hxT⟩ := hocc

  let T : PrimeAway N → H1 κ N n →ₗ[κ] H1 κ N n := fun i => TH κ N n (i : ℕ)
  have hTcomm : ∀ i j : PrimeAway N, Commute (T i) (T j) := fun i j =>
    TH_comm κ N n i.2.1 j.2.1 i.2.2 j.2.2
  have hann : ∀ i : PrimeAway N, ∃ P : κ[X], P.Monic ∧ P.Splits ∧ aeval (T i) P = 0 := fun i =>
    exists_monic_splits_aeval_TH_eq_zero φ (i : ℕ)

  have hxeig : ∀ i : PrimeAway N, (i : ℕ) ∉ S₀ → T i x = lam i • x := by
    intro i hi
    obtain ⟨T', hT', hT'x⟩ := hxT i i.2.1 i.2.2 hi
    have heq : T' = TH κ N n (i : ℕ) := unique_of_isCoeffHeckeOnH1 hT' (isCoeffHeckeOnH1_TH κ N n i)
    rw [← hT'x, heq]

  let W : Submodule κ (H1 κ N n) :=
    ⨅ i : {i : PrimeAway N // (i : ℕ) ∉ S₀}, LinearMap.ker (T i.1 - lam (i.1 : ℕ) • 1)
  have hmemW : ∀ y, y ∈ W ↔ ∀ i : PrimeAway N, (i : ℕ) ∉ S₀ → T i y = lam i • y := by
    intro y
    change y ∈ ⨅ i : {i : PrimeAway N // (i : ℕ) ∉ S₀}, LinearMap.ker (T i.1 - lam (i.1 : ℕ) • 1) ↔ _
    rw [Submodule.mem_iInf]
    constructor
    · intro h i hi
      have := h ⟨i, hi⟩
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at this
    · intro h i
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
      exact h i.1 i.2
  have hxW : x ∈ W := (hmemW x).mpr hxeig
  have hWne : W ≠ ⊥ := fun h => hx0 (by rw [h, Submodule.mem_bot] at hxW; exact hxW)
  have hstab : ∀ j : PrimeAway N, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    rw [hmemW] at hy ⊢
    intro i hi
    rw [← Module.End.mul_apply, (hTcomm i j).eq, Module.End.mul_apply, hy i hi, map_smul]
  haveI : Module.Finite κ (H1 κ N n) := moduleFinite_coeffH1 N _
  obtain ⟨v, hvW, hv0, hv⟩ :=
    exists_common_eigenvector_of_splits T hTcomm hann _ W rfl hWne hstab
  choose c hc using hv
  let mu : ℕ → κ := fun ℓ => if h : ℓ.Prime ∧ ¬ ℓ ∣ N then c ⟨ℓ, h⟩ else 0
  have hmu : ∀ i : PrimeAway N, mu i = c i := fun i => by
    simp only [mu, dif_pos i.2]
  refine ⟨mu, ⟨v, hv0, fun ℓ hℓ hℓN _ => ?_⟩, fun ℓ hℓ hℓN hℓS => ?_⟩
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    refine ⟨TH κ N n ℓ, isCoeffHeckeOnH1_TH κ N n ℓ, ?_⟩
    have h := hc ⟨ℓ, hℓ, hℓN⟩
    rw [hmu ⟨ℓ, hℓ, hℓN⟩]
    exact h
  · have h1 := hc ⟨ℓ, hℓ, hℓN⟩
    have h2 := (hmemW v).mp hvW ⟨ℓ, hℓ, hℓN⟩ hℓS
    rw [hmu ⟨ℓ, hℓ, hℓN⟩]
    have h3 : c ⟨ℓ, hℓ, hℓN⟩ • v = lam ℓ • v := h1.symm.trans h2
    exact smul_left_injective κ hv0 h3

end S_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
end P2MW
export P2MW.S_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom (solution)
