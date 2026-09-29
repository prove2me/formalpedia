-- Prove2me | solution 1 for HeckeEis.mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0e639083-f23a-56b5-836d-c2fe68878f82

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt

set_option autoImplicit false

noncomputable section

namespace ATHC13Tor

open CategoryTheory CategoryTheory.Limits CongruenceSubgroup HeckeEis MvPolynomial
open scoped MatrixGroups

universe u

section Forms

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ)

theorem map_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (binarySubst R M P) = binarySubst R' M (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map φ).comp (binarySubst R M : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R)
      = (binarySubst R' M : MvPolynomial (Fin 2) R' →+* MvPolynomial (Fin 2) R').comp
          (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, binarySubst_C, map_C]
    · simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, binarySubst_X, map_X,
        map_sum, map_mul, map_intCast]
  exact RingHom.congr_fun h P

noncomputable def mapBF : ↥(BinaryForm R n) →ₛₗ[φ] ↥(BinaryForm R' n) where
  toFun P := ⟨MvPolynomial.map φ (P : MvPolynomial (Fin 2) R),
    (mem_homogeneousSubmodule n _).mpr (((mem_homogeneousSubmodule n _).mp P.2).map φ)⟩
  map_add' P Q := by
    ext1
    simp only [Submodule.coe_add, map_add]
  map_smul' c P := by
    ext1
    simp only [SetLike.val_smul, smul_eq_C_mul, map_mul, map_C]

@[scoped simp] theorem coe_mapBF (P : ↥(BinaryForm R n)) :
    ((mapBF φ n P : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = MvPolynomial.map φ P := rfl

theorem mapBF_binaryFormRepSL (g : SL(2, ℤ)) (P : ↥(BinaryForm R n)) :
    mapBF φ n (binaryFormRepSL R n g P) = binaryFormRepSL R' n g (mapBF φ n P) := by
  ext1
  simp only [coe_mapBF, binaryFormRepSL_apply_coe, map_binarySubst]

theorem mapBF_surjective (hφ : Function.Surjective φ) : Function.Surjective (mapBF φ n) := by
  intro Q
  classical

  obtain ⟨s, hs⟩ : ∃ s : R' → R, ∀ y, φ (s y) = y := ⟨fun y => (hφ y).choose, fun y => (hφ y).choose_spec⟩
  let P : MvPolynomial (Fin 2) R :=
    ∑ d ∈ (Q : MvPolynomial (Fin 2) R').support, monomial d (s (coeff d (Q : MvPolynomial (Fin 2) R')))
  have hPhom : P.IsHomogeneous n := by
    refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    refine isHomogeneous_monomial _ ?_
    have hQ := (mem_homogeneousSubmodule n _).mp Q.2
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hd)
  refine ⟨⟨P, (mem_homogeneousSubmodule n _).mpr hPhom⟩, ?_⟩
  ext1
  simp only [coe_mapBF, P, map_sum, map_monomial, hs]
  exact (as_sum (Q : MvPolynomial (Fin 2) R')).symm

end Forms

end ATHC13Tor
p2m_reactivate "P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.ATHC13Tor"

namespace ATHC13Tor

open CategoryTheory CategoryTheory.Limits CongruenceSubgroup HeckeEis MvPolynomial
open scoped MatrixGroups

section Coef

variable {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (n N : ℕ)

def Coef (_φ : R →+* R') (n : ℕ) : Type := ↥(BinaryForm R' n)

scoped instance : AddCommGroup (Coef φ n) := inferInstanceAs (AddCommGroup ↥(BinaryForm R' n))

noncomputable scoped instance : Module R (Coef φ n) := Module.compHom (↥(BinaryForm R' n)) φ

def toCoef : ↥(BinaryForm R' n) ≃+ Coef φ n := AddEquiv.refl _

theorem smul_toCoef (r : R) (v : ↥(BinaryForm R' n)) :
    r • toCoef φ n v = toCoef φ n (φ r • v) := rfl

noncomputable def rho' : Representation R (Gamma0 N) (Coef φ n) where
  toFun g :=
    { toFun := fun v => toCoef φ n (binaryFormRepSL R' n (g : SL(2, ℤ)) ((toCoef φ n).symm v))
      map_add' := fun v w => by
        change toCoef φ n (binaryFormRepSL R' n (g : SL(2, ℤ)) ((toCoef φ n).symm v + (toCoef φ n).symm w)) = _
        rw [map_add, map_add]
      map_smul' := fun r v => by
        change toCoef φ n (binaryFormRepSL R' n (g : SL(2, ℤ)) (φ r • (toCoef φ n).symm v)) = _
        rw [map_smul, RingHom.id_apply, smul_toCoef] }
  map_one' := by
    apply LinearMap.ext
    intro v
    simp only [OneMemClass.coe_one, map_one, Module.End.one_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rfl

theorem rho'_apply (g : Gamma0 N) (v : Coef φ n) :
    rho' φ n N g v = toCoef φ n (binaryFormRepSL R' n (g : SL(2, ℤ)) ((toCoef φ n).symm v)) := rfl

noncomputable abbrev rhoR : Representation R (Gamma0 N) ↥(BinaryForm R n) :=
  (binaryFormRepSL R n).comp (Gamma0 N).subtype

noncomputable abbrev rhoR' : Representation R' (Gamma0 N) ↥(BinaryForm R' n) :=
  (binaryFormRepSL R' n).comp (Gamma0 N).subtype

noncomputable def redLin : ↥(BinaryForm R n) →ₗ[R] Coef φ n where
  toFun P := toCoef φ n (mapBF φ n P)
  map_add' P Q := by rw [map_add, map_add]
  map_smul' r P := by rw [LinearMap.map_smulₛₗ, RingHom.id_apply, smul_toCoef]

theorem redLin_apply (P : ↥(BinaryForm R n)) : redLin φ n P = toCoef φ n (mapBF φ n P) := rfl

theorem redLin_comm (g : Gamma0 N) (P : ↥(BinaryForm R n)) :
    redLin φ n (rhoR n N g P) = rho' φ n N g (redLin φ n P) := by
  rw [redLin_apply, rho'_apply, redLin_apply]
  change toCoef φ n (mapBF φ n (binaryFormRepSL R n (g : SL(2, ℤ)) P)) = _
  rw [mapBF_binaryFormRepSL]
  rfl

noncomputable abbrev A2 : Rep R (Gamma0 N) := Rep.of (rhoR (R := R) n N)
noncomputable abbrev A3 : Rep R (Gamma0 N) := Rep.of (rho' φ n N)

noncomputable def red : A2 (R := R) n N ⟶ A3 φ n N :=
  Rep.ofHom
    { toLinearMap := redLin φ n
      isIntertwining' := fun g => LinearMap.ext fun P => redLin_comm φ n N g P }

theorem red_hom_apply (P : ↥(BinaryForm R n)) : (red φ n N).hom P = toCoef φ n (mapBF φ n P) := rfl

theorem epi_red (hφ : Function.Surjective φ) : Epi (red φ n N) := by
  rw [Rep.epi_iff_surjective]
  intro v
  obtain ⟨P, hP⟩ := mapBF_surjective φ n hφ ((toCoef φ n).symm v)
  exact ⟨P, by rw [red_hom_apply, hP]; rfl⟩

noncomputable def X : ShortComplex (Rep R (Gamma0 N)) :=
  ShortComplex.mk (kernel.ι (red φ n N)) (red φ n N) (kernel.condition _)

theorem X_shortExact (hφ : Function.Surjective φ) : (X φ n N).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (red φ n N))
  mono_f := by dsimp [X]; infer_instance
  epi_g := epi_red φ n N hφ

end Coef
p2m_reactivate "P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.ATHC13Tor"

section Torsion

variable {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (n N : ℕ)

open groupCohomology

theorem smul_injective_binaryForm {π : R} (hπ : IsSMulRegular R π) (m : ℕ) :
    Function.Injective (fun P : ↥(BinaryForm R m) => π • P) := by
  intro P Q h
  apply Subtype.ext
  refine MvPolynomial.ext _ _ fun d => hπ ?_
  have := congrArg (fun F : ↥(BinaryForm R m) => coeff d (F : MvPolynomial (Fin 2) R)) h
  simpa only [SetLike.val_smul, coeff_smul, smul_eq_mul] using this

noncomputable def smulHom (π : R) : A2 (R := R) n N ⟶ A2 (R := R) n N :=
  Rep.ofHom
    { toLinearMap := π • LinearMap.id
      isIntertwining' := fun g => by
        rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id] }

theorem smulHom_hom_apply (π : R) (P : ↥(BinaryForm R n)) : (smulHom n N π).hom P = π • P := rfl

noncomputable def Y (π : R) (hker : ∀ r : R, φ r = 0 ↔ π ∣ r) : ShortComplex (Rep R (Gamma0 N)) :=
  ShortComplex.mk (smulHom n N π) (red φ n N) (by
    ext P : 3
    change toCoef φ n (mapBF φ n (π • P)) = 0
    have : mapBF φ n (π • P) = 0 := by
      rw [LinearMap.map_smulₛₗ, (hker π).mpr (dvd_refl π), zero_smul]
    rw [this]
    rfl)

theorem exists_eq_smul_of_mapBF_eq_zero (π : R) (hker : ∀ r : R, φ r = 0 ↔ π ∣ r)
    (P : ↥(BinaryForm R n)) (hP : mapBF φ n P = 0) : ∃ Q : ↥(BinaryForm R n), π • Q = P := by
  classical
  have hcoeff : ∀ d, π ∣ coeff d (P : MvPolynomial (Fin 2) R) := by
    intro d
    apply (hker _).mp
    have := congrArg (fun F : ↥(BinaryForm K n) => coeff d (F : MvPolynomial (Fin 2) K)) hP
    simpa only [coe_mapBF, coeff_map, ZeroMemClass.coe_zero, coeff_zero] using this
  choose q hq using hcoeff
  let Q : MvPolynomial (Fin 2) R := ∑ d ∈ (P : MvPolynomial (Fin 2) R).support, monomial d (q d)
  have hQhom : Q.IsHomogeneous n := by
    refine IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact ((mem_homogeneousSubmodule n _).mp P.2) (mem_support_iff.mp hd)
  refine ⟨⟨Q, (mem_homogeneousSubmodule n _).mpr hQhom⟩, Subtype.ext ?_⟩
  change π • Q = (P : MvPolynomial (Fin 2) R)
  rw [Finset.smul_sum]
  conv_rhs => rw [(P : MvPolynomial (Fin 2) R).as_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_monomial, smul_eq_mul, ← hq d]

theorem Y_shortExact (π : R) (hker : ∀ r : R, φ r = 0 ↔ π ∣ r) (hπ : IsSMulRegular R π)
    (hφ : Function.Surjective φ) : (Y φ n N π hker).ShortExact where
  exact := (forget₂ (Rep R (Gamma0 N)) (ModuleCat R)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      obtain ⟨Q, hQ⟩ := exists_eq_smul_of_mapBF_eq_zero φ n π hker x
        (by
          have hx' : toCoef φ n (mapBF φ n x) = 0 := hx
          exact hx')
      exact ⟨Q, hQ⟩
  mono_f := (Rep.mono_iff_injective _).2 fun P Q h => by
    have h' : π • P = π • Q := h
    exact smul_injective_binaryForm hπ n h'
  epi_g := epi_red φ n N hφ

theorem isZero_H0_A3 {p : ℕ} [Fact p.Prime] [CharP K p] (hn : 0 < n) (hnp : n < p) (hpN : ¬ p ∣ N) :
    IsZero (groupCohomology (A3 φ n N) 0) := by
  haveI : Subsingleton ((A3 φ n N).ρ.invariants) := by
    refine ⟨fun v w => Subtype.ext ?_⟩
    have hv : ∀ u : (A3 φ n N).ρ.invariants, (u : Coef φ n) = 0 := by
      intro u
      have hu := u.2
      rw [Representation.mem_invariants] at hu
      have := HeckeEis.eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self p K N n hn hnp hpN
        ((toCoef φ n).symm (u : Coef φ n)) (fun g => hu g)
      exact this
    rw [hv v, hv w]
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (groupCohomology.H0Iso (A3 φ n N))

theorem mem_cocycles₁_A2 (z : ↥(coeffCocycles (rhoR (R := R) n N))) :
    (z : Gamma0 N → ↥(BinaryForm R n)) ∈ cocycles₁ (A2 (R := R) n N) := by
  rw [mem_cocycles₁_iff]
  intro g h
  rw [z.2 g h, add_comm]

theorem mem_coboundaries₁_A2_iff (w : Gamma0 N → ↥(BinaryForm R n)) :
    w ∈ coboundaries₁ (A2 (R := R) n N) ↔ w ∈ coeffCoboundaries (rhoR (R := R) n N) := by
  rw [mem_coeffCoboundaries_iff, coboundaries₁, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [← hv]; rfl⟩

theorem main {p : ℕ} [Fact p.Prime] [CharP K p] (hφ : Function.Surjective φ) (π : R)
    (hker : ∀ r : R, φ r = 0 ↔ π ∣ r) (hπ : IsSMulRegular R π) (hnp : n < p) (hpN : ¬ p ∣ N)
    (z : ↥(coeffCocycles (rhoR (R := R) n N)))
    (hz : π • (z : Gamma0 N → ↥(BinaryForm R n)) ∈ coeffCoboundaries (rhoR (R := R) n N)) :
    (z : Gamma0 N → ↥(BinaryForm R n)) ∈ coeffCoboundaries (rhoR (R := R) n N) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have htriv : ∀ (g : Gamma0 N) (P : ↥(BinaryForm R 0)), binaryFormRepSL R 0 (g : SL(2, ℤ)) P = P := by
      intro g P
      apply Subtype.ext
      change binarySubst R ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) = P
      have hP : (P : MvPolynomial (Fin 2) R) = C (coeff 0 (P : MvPolynomial (Fin 2) R)) := by
        have h0 : (P : MvPolynomial (Fin 2) R).totalDegree = 0 := by
          apply le_antisymm _ (Nat.zero_le _)
          exact ((mem_homogeneousSubmodule 0 _).mp P.2).totalDegree_le
        exact (totalDegree_eq_zero_iff_eq_C.mp h0)
      rw [hP, binarySubst_C]
    have hcob : ∀ w : Gamma0 N → ↥(BinaryForm R 0), w ∈ coeffCoboundaries (rhoR (R := R) 0 N) → w = 0 := by
      intro w hw
      obtain ⟨v, rfl⟩ := (mem_coeffCoboundaries_iff _ _).mp hw
      funext g
      change binaryFormRepSL R 0 (g : SL(2, ℤ)) v - v = 0
      rw [htriv g v, sub_self]
    have hπz : π • (z : Gamma0 N → ↥(BinaryForm R 0)) = 0 := hcob _ hz
    have hz0 : (z : Gamma0 N → ↥(BinaryForm R 0)) = 0 := by
      funext g
      have := congrFun hπz g
      simp only [Pi.smul_apply, Pi.zero_apply] at this
      exact smul_injective_binaryForm hπ 0 (by simpa using this)
    rw [hz0]
    exact Submodule.zero_mem _
  ·
    have hX := Y_shortExact φ n N π hker hπ hφ
    have hexact := groupCohomology.mapShortComplex₁_exact hX (i := 0) (j := 1) rfl
    have hzero := isZero_H0_A3 φ n N hn hnp hpN
    have hf : (groupCohomology.mapShortComplex₁ hX (i := 0) (j := 1) rfl).f = 0 := hzero.eq_of_src _ _
    have hmono : Mono (groupCohomology.mapShortComplex₁ hX (i := 0) (j := 1) rfl).g := hexact.mono_g hf
    have hmono' : Mono ((groupCohomology.functor R (Gamma0 N) 1).map (smulHom n N π)) := hmono
    have hinj := (ModuleCat.mono_iff_injective _).mp hmono'
    let z2 : cocycles₁ (A2 (R := R) n N) := ⟨_, mem_cocycles₁_A2 n N z⟩

    have hmap : mapCocycles₁ (MonoidHom.id (Gamma0 N)) (smulHom n N π) z2 = π • z2 := by
      apply cocycles₁_ext
      intro g
      rfl
    have hπz : H1π (A2 (R := R) n N) (π • z2) = 0 := by
      rw [H1π_eq_zero_iff, mem_coboundaries₁_A2_iff]
      have hcoe : ((π • z2 : cocycles₁ (A2 (R := R) n N)) : Gamma0 N → ↥(BinaryForm R n))
          = π • (z : Gamma0 N → ↥(BinaryForm R n)) := rfl
      rw [hcoe]
      exact hz
    have key := H1π_comp_map_apply (A := A2 n N) (B := A2 n N) (MonoidHom.id _) (smulHom n N π) z2
    rw [hmap, hπz] at key
    have h0 : (groupCohomology.functor R (Gamma0 N) 1).map (smulHom n N π) (H1π (A2 (R := R) n N) z2) = 0 := by
      rw [groupCohomology.functor_map]
      exact key
    have h1 : H1π (A2 (R := R) n N) z2 = 0 := hinj (by rw [h0]; exact (map_zero _).symm)
    rw [H1π_eq_zero_iff, mem_coboundaries₁_A2_iff] at h1
    exact h1

end Torsion
p2m_reactivate "P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.ATHC13Tor"

end ATHC13Tor
p2m_reactivate "P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.ATHC13Tor"

end
p2m_reactivate "P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.ATHC13Tor"

theorem solution
    {R K : Type} [CommRing R] [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (φ : R →+* K) (hφ : Function.Surjective φ) (π : R) (hker : ∀ r : R, φ r = 0 ↔ π ∣ r)
    (hπ : IsSMulRegular R π) (n N : ℕ) (hnp : n < p) (hpN : ¬ p ∣ N)
    (z : ↥(HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
    (hz : π • (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) ∈
      HeckeEis.coeffCoboundaries
        ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) ∈
      HeckeEis.coeffCoboundaries
        ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) :=
  ATHC13Tor.main φ n N hφ π hker hπ hnp hpN z hz

end S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
end P2MW
export P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt (solution)
