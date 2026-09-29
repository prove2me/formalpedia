-- Prove2me | solution 1 for MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8817a3dd-54d1-537f-a832-0e80ec7b994c

import Mathlib
import Theorems.Thm_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField
import Theorems.Thm_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift

set_option autoImplicit false

open MvPolynomial IsLocalRing

namespace A6Aux

def LiftProp (R : Type) [CommRing R] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R)) : Prop :=
  ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m

theorem step (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
    (hlift : LiftProp R I) (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (_ : IsScalarTower R ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D)
      (_ : Module.FaithfullyFlat ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (σ : ((MvPolynomial (Fin n) R) ⧸ I) →ₐ[R] D),
      ∀ f : (MvPolynomial (Fin n) R), σ (Ideal.Quotient.mk I f) - algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
        Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) := by
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI := hJ

  have hKJ : (J ^ N ⊔ J * I) ≤ J := sup_le (Ideal.pow_le_self hN) Ideal.mul_le_left
  have hJne : J ≠ ⊤ := hJ.ne_top
  haveI : Nontrivial ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hJne hKJ)
  have hnilJ : ∀ j ∈ J, IsNilpotent (Ideal.Quotient.mk (J ^ N ⊔ J * I) j) := by
    intro j hj
    refine ⟨N, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.pow_mem_pow hj N)
  have hunit : ∀ f : (MvPolynomial (Fin n) R), f ∉ J → IsUnit (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) := by
    intro f hf
    obtain ⟨g, j, hj, hgj⟩ := hJ.exists_inv hf
    have : Ideal.Quotient.mk (J ^ N ⊔ J * I) f * Ideal.Quotient.mk (J ^ N ⊔ J * I) g = 1 - Ideal.Quotient.mk (J ^ N ⊔ J * I) j := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (J ^ N ⊔ J * I)), ← map_sub]
      congr 1
      linear_combination hgj
    exact isUnit_of_mul_isUnit_left (this ▸ (hnilJ j hj).isUnit_one_sub)
  haveI : IsLocalRing ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    by_cases hf : f ∈ J
    · right
      rw [← map_one (Ideal.Quotient.mk (J ^ N ⊔ J * I)), ← map_sub]
      exact hunit _ fun h1 => hJne (J.eq_top_of_isUnit_mem (by simpa using J.add_mem h1 hf) isUnit_one)
    · exact Or.inl (hunit f hf)
  have hJbar : (J.map (Ideal.Quotient.mk (J ^ N ⊔ J * I))).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (J ^ N ⊔ J * I)) Ideal.Quotient.mk_surjective hJ with h | h
    · exfalso
      have hcm := Ideal.comap_map_of_surjective (Ideal.Quotient.mk (J ^ N ⊔ J * I)) Ideal.Quotient.mk_surjective J
      rw [h, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hKJ] at hcm
      exact hJne hcm.symm
    · exact h
  have hmax : maximalIdeal ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) = J.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) := (IsLocalRing.eq_maximalIdeal hJbar).symm
  haveI : IsArtinianRing ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) := by
    refine (isArtinianRing_iff_isNilpotent_maximalIdeal ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I))).mpr ⟨N, ?_⟩
    rw [hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left ha
  haveI : Finite (ResidueField ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I))) := by
    have algext : ∀ (i₁ i₂ : Algebra ℤ (MvPolynomial (Fin n) R)), i₁ = i₂ := fun i₁ i₂ =>
      Algebra.algebra_ext _ _ fun r => RingHom.congr_fun (RingHom.ext_int (@algebraMap ℤ _ _ _ i₁) (@algebraMap ℤ _ _ _ i₂)) r
    have i0 : Algebra.FiniteType ℤ (MvPolynomial (Fin n) R) := inferInstance
    obtain ⟨hfinJ, -⟩ := @Algebra.FiniteType.finite_quotient_and_exists_charP_of_isMaximal_int (MvPolynomial (Fin n) R) _ (by convert i0 <;> first | rfl | exact algext _ _) J hJ
    haveI := hfinJ
    let r : (MvPolynomial (Fin n) R) ⧸ J →+* ResidueField ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) :=
      Ideal.Quotient.lift J ((IsLocalRing.residue ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I))).comp (Ideal.Quotient.mk (J ^ N ⊔ J * I))) (by
        intro a ha
        show IsLocalRing.residue ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) (Ideal.Quotient.mk (J ^ N ⊔ J * I) a) = 0
        rw [IsLocalRing.residue_eq_zero_iff, hmax]
        exact Ideal.mem_map_of_mem _ ha)
    refine Finite.of_surjective r fun y => ?_
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨Ideal.Quotient.mk J f, rfl⟩

  obtain ⟨D, iD, iLD, iAD, iAlg, ℓ, iℓ, hFF, hloc, hmD, hac, hchar⟩ := IsArtinianRing.exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I))
  letI : CommRing D := iD
  haveI : IsLocalRing D := iLD
  haveI : IsArtinianRing D := iAD
  letI : Algebra ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D := iAlg
  haveI : Fact ℓ.Prime := iℓ
  haveI : Module.FaithfullyFlat ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D := hFF
  haveI : IsAlgClosed (ResidueField D) := hac
  haveI : CharP (ResidueField D) ℓ := hchar
  letI algRD : Algebra R D := ((algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D).comp (algebraMap R ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)))).toAlgebra
  haveI : IsScalarTower R ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D := IsScalarTower.of_algebraMap_eq (R := R) (S := ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I))) (A := D) (fun r => rfl)

  have hAJ : J ^ N ⊔ I ≤ J := sup_le (Ideal.pow_le_self hN) hIJ
  haveI : (Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I))).IsTwoSided := inferInstance
  have hane : Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) ≠ ⊤ := by
    intro h
    have hle : Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) ≤ maximalIdeal D := by
      rw [← hmD, hmax, Ideal.map_map, Ideal.map_map]
      exact Ideal.map_mono hAJ
    rw [h, top_le_iff] at hle
    exact (maximalIdeal.isMaximal D).ne_top hle
  haveI : Nontrivial (D ⧸ Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I))) :=
    Ideal.Quotient.nontrivial_iff.mpr hane
  let p : D →ₐ[R] D ⧸ Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) :=
    Ideal.Quotient.mkₐ R _
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective R _
  have hpker : RingHom.ker p.toRingHom = Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) :=
    Ideal.mk_ker
  have hsmall : RingHom.ker p.toRingHom * maximalIdeal D = ⊥ := by
    rw [hpker, ← hmD, hmax, Ideal.map_map, Ideal.map_map, ← Ideal.map_mul, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_bot, RingHom.comp_apply, ← RingHom.mem_ker]
    have : (J ^ N ⊔ I) * J ≤ (J ^ N ⊔ J * I) := by
      rw [Ideal.sup_mul]
      refine sup_le ?_ ?_
      · exact le_sup_of_le_left (by rw [← pow_succ]; exact Ideal.pow_le_pow_right (Nat.le_succ N))
      · rw [mul_comm]; exact le_sup_right
    have hk : Ideal.Quotient.mk (J ^ N ⊔ J * I) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (this ha)
    rw [RingHom.mem_ker, hk, map_zero]

  let m : ((MvPolynomial (Fin n) R) ⧸ I) →ₐ[R] D ⧸ Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) :=
    Ideal.Quotient.liftₐ I (p.comp ((IsScalarTower.toAlgHom R ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D).comp (Ideal.Quotient.mkₐ R (J ^ N ⊔ J * I)))) (by
      intro a ha
      show p (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D (Ideal.Quotient.mk (J ^ N ⊔ J * I) a)) = 0
      rw [← RingHom.mem_ker, show RingHom.ker p = RingHom.ker p.toRingHom from rfl, hpker]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right ha)))
  obtain ⟨m', hm'⟩ := hlift D _ ℓ p hp hsmall m
  refine ⟨D, iD, algRD, iAlg, inferInstance, hFF, m', fun f => ?_⟩
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  show p (m' (Ideal.Quotient.mk I f)) = p (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D (Ideal.Quotient.mk (J ^ N ⊔ J * I) f))
  rw [← AlgHom.comp_apply, hm']
  rfl

end A6Aux

theorem solution
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
    (hlift : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m) :
    ∃ (D : ℕ → Type) (_ : ∀ N, CommRing (D N)) (_ : ∀ N, Algebra R (D N))
      (_ : ∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N),
      ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
        σ N (Ideal.Quotient.mk I f) -
            algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
          Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
            (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) := by
  classical
  have perN : ∀ N : ℕ, ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (_ : IsScalarTower R ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D)
      (_ : Module.FaithfullyFlat ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (σ : ((MvPolynomial (Fin n) R) ⧸ I) →ₐ[R] D),
      ∀ f : (MvPolynomial (Fin n) R), σ (Ideal.Quotient.mk I f) - algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
        Ideal.map (algebraMap ((MvPolynomial (Fin n) R) ⧸ (J ^ N ⊔ J * I)) D) (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    ·
      subst hN
      have htop : (J ^ 0 ⊔ J * I) = ⊤ := by rw [pow_zero, Ideal.one_eq_top, top_sup_eq]
      haveI : Subsingleton ((MvPolynomial (Fin n) R) ⧸ (J ^ 0 ⊔ J * I)) := Ideal.Quotient.subsingleton_iff.mpr htop
      refine ⟨((MvPolynomial (Fin n) R) ⧸ (J ^ 0 ⊔ J * I)), inferInstance, inferInstance, inferInstance, inferInstance, Module.FaithfullyFlat.self _,
        Ideal.Quotient.factorₐ R (by rw [htop]; exact le_top), fun f => ?_⟩
      rw [Subsingleton.elim (_ - _ : ((MvPolynomial (Fin n) R) ⧸ (J ^ 0 ⊔ J * I))) 0]
      exact Submodule.zero_mem _
    · exact A6Aux.step R I J hIJ hJ hlift N (Nat.pos_iff_ne_zero.mp hN)
  choose D iR iA iC iT iF σ hσ using perN
  exact ⟨D, iR, iA, iC, iT, iF, σ, fun N f => hσ N f⟩

end S_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift
end P2MW
export P2MW.S_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift (solution)
