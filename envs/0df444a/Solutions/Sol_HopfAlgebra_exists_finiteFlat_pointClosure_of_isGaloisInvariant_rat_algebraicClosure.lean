-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e207370d-33f2-5430-a465-17c7bea0a732

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure

set_option autoImplicit false

namespace HopfAlgebra
p2m_export "HopfAlgebra" "exists_quotientFlag_of_galoisStableChain natCard_algHom_eq_finrank_of_charZero isUnit_withConv_algHom"
namespace PointClosureAux
p2m_open "HopfAlgebra"

open scoped TensorProduct

universe u

section Separate

variable (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
variable (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Flat R A]

theorem free : Module.Free R A := Module.free_of_finite_type_torsion_free'

omit [IsPrincipalIdealRing R] in
private theorem _root_.HopfAlgebra.PointClosureAux.finrank_pos : 0 < Module.finrank R A := by
  haveI : Nontrivial A := (Bialgebra.counitAlgHom R A).toRingHom.domain_nontrivial
  exact Module.finrank_pos

p2m_export "HopfAlgebra.PointClosureAux" "finrank_pos"

theorem finite_algHom : Finite (A →ₐ[R] K) := by
  haveI := free R A
  refine Nat.finite_of_card_ne_zero ?_
  rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R A K]
  exact (finrank_pos R A).ne'

variable {R K A} in

theorem algHom_eq_of_ker_eq {S : Type} [CommRing S] [Algebra K S] (χ χ' : S →ₐ[K] K)
    (h : RingHom.ker χ = RingHom.ker χ') : χ = χ' := by
  ext x
  have hx : x - algebraMap K S (χ x) ∈ RingHom.ker χ := by
    simp [RingHom.mem_ker]
  rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hx
  simpa using hx.symm

theorem eq_zero_of_forall_algHom (hRK : Function.Injective (algebraMap R K)) (y : A)
    (hy : ∀ g : A →ₐ[R] K, g y = 0) : y = 0 := by
  classical
  haveI := free R A
  haveI := finite_algHom R K A
  letI := Fintype.ofFinite (A →ₐ[R] K)
  set n := Module.finrank R A with hn
  have hcard : Fintype.card (A →ₐ[R] K) = n := by
    rw [← Nat.card_eq_fintype_card, HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R A K]

  let X := A →ₐ[R] K
  let Φ : K ⊗[R] A →ₐ[K] (X → K) :=
    Algebra.TensorProduct.lift (Algebra.ofId K (X → K)) (Pi.algHom R _ fun g : X => g)
      (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (k : K) (a : A) (g : X), Φ (k ⊗ₜ a) g = k * g a := by
    intro k a g
    simp [Φ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Pi.algHom_apply]

  let G : X → (K ⊗[R] A →ₐ[K] K) := fun g => (Pi.evalAlgHom K (fun _ : X => K) g).comp Φ
  have hG : ∀ (g : X) (k : K) (a : A), G g (k ⊗ₜ a) = k * g a := fun g k a => hΦ k a g
  have hGinj : Function.Injective G := by
    intro g g' hgg'
    ext a
    have := congrArg (fun χ => χ ((1 : K) ⊗ₜ a)) hgg'
    simpa [hG] using this
  have hGsurj : ∀ g : X, Function.Surjective (G g) := fun g k =>
    ⟨algebraMap K _ k, AlgHom.commutes _ _⟩
  have hmax : ∀ g : X, (RingHom.ker (G g)).IsMaximal := fun g =>
    RingHom.ker_isMaximal_of_surjective _ (hGsurj g)
  have hne : ∀ g g' : X, g ≠ g' → RingHom.ker (G g) ≠ RingHom.ker (G g') := fun g g' hgg' h =>
    hgg' (hGinj (algHom_eq_of_ker_eq _ _ h))

  have hcrt : ∀ g : X, ∃ b : K ⊗[R] A, G g b = 1 ∧ ∀ g' : X, g' ≠ g → G g' b = 0 := by
    intro g
    have htop : RingHom.ker (G g) ⊔ ⨅ g' ∈ (Finset.univ.erase g : Finset X), RingHom.ker (G g') = ⊤ :=
      Ideal.sup_iInf_eq_top fun g' hg' =>
        (hmax g).coprime_of_ne (hmax g') (hne g g' (Finset.ne_of_mem_erase hg').symm)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : K ⊗[R] A) ∈ _)
    refine ⟨b, ?_, fun g' hg' => ?_⟩
    · have := congrArg (G g) hab
      rwa [map_add, map_one, (RingHom.mem_ker).mp ha, zero_add] at this
    · have hb' := (Submodule.mem_iInf _).mp hb g'
      have hb'' := (Submodule.mem_iInf _).mp hb' (Finset.mem_erase.mpr ⟨hg', Finset.mem_univ _⟩)
      exact (RingHom.mem_ker).mp hb''
  choose b hb1 hb0 using hcrt
  have hΦb : ∀ g : X, Φ (b g) = Pi.single g 1 := by
    intro g
    funext g'
    by_cases h : g' = g
    · subst h; (have h__af := hb1 g'; simp at h__af ⊢; exact h__af)
    · rw [Pi.single_eq_of_ne h]; exact hb0 g g' h

  have hsurj : Function.Surjective Φ.toLinearMap := by
    intro v
    refine ⟨∑ g, v g • b g, ?_⟩
    rw [AlgHom.toLinearMap_apply, map_sum]
    simp_rw [map_smul, hΦb]
    ext g'
    simp [Finset.sum_apply, Pi.single_apply]
  have hdim : Module.finrank K (K ⊗[R] A) = Module.finrank K (X → K) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, hcard]
  have hinj : Function.Injective Φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj

  have h1 : Φ ((1 : K) ⊗ₜ y) = 0 := by
    funext g
    rw [hΦ, one_mul, hy g, Pi.zero_apply]
  have h2 : (1 : K) ⊗ₜ[R] y = 0 := hinj (by rw [AlgHom.toLinearMap_apply, h1, map_zero])
  exact Algebra.TensorProduct.includeRight_injective hRK
    (by rw [Algebra.TensorProduct.includeRight_apply, h2, map_zero])

end Separate

section UnitsPackaging

variable {P : Type*} [CommMonoid P]

noncomputable def unitEquiv (h : ∀ x : P, IsUnit x) : P ≃ Additive Pˣ where
  toFun x := Additive.ofMul (h x).unit
  invFun m := ((Additive.toMul m : Pˣ) : P)
  left_inv x := (h x).unit_spec
  right_inv m := by
    apply Additive.toMul.injective
    ext
    exact (h _).unit_spec

theorem unitEquiv_symm_apply (h : ∀ x : P, IsUnit x) (m : Additive Pˣ) :
    (unitEquiv h).symm m = ((Additive.toMul m : Pˣ) : P) := rfl

theorem unitEquiv_mul (h : ∀ x : P, IsUnit x) (x y : P) :
    unitEquiv h (x * y) = unitEquiv h x + unitEquiv h y := by
  apply (unitEquiv h).symm.injective
  rw [Equiv.symm_apply_apply, unitEquiv_symm_apply, toMul_add, Units.val_mul]
  change x * y = ((Additive.toMul (Additive.ofMul (h x).unit) : Pˣ) : P) *
    ((Additive.toMul (Additive.ofMul (h y).unit) : Pˣ) : P)
  rw [toMul_ofMul, toMul_ofMul, (h x).unit_spec, (h y).unit_spec]

theorem inv_mem_of_finite {G : Type*} [Group G] [Finite G] (S : Submonoid G) {x : G}
    (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpos : 0 < orderOf x := orderOf_pos x
  have hx' : x ^ (orderOf x - 1) * x = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← eq_inv_of_mul_eq_one_left hx']
  exact pow_mem hx _

end UnitsPackaging

end HopfAlgebra.PointClosureAux

open HopfAlgebra.PointClosureAux in

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (Γ : Submonoid (WithConv (H →ₐ[R] AlgebraicClosure ℚ)))
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ν : WithConv (H →ₐ[R] AlgebraicClosure ℚ)), ν ∈ Γ →
      WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars R).comp
        (WithConv.ofConv ν)) ∈ Γ) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H') (π : H →ₐc[R] H'),
      Function.Surjective π ∧ Module.Finite R H' ∧ Module.Flat R H' ∧
      Coalgebra.IsCocomm R H' ∧
      (RingHom.ker π = ⨅ ν ∈ Γ, RingHom.ker (WithConv.ofConv ν)) ∧
      ∀ (T : Type) [CommRing T] [Algebra R T] (ι : T →ₐ[R] AlgebraicClosure ℚ),
        Function.Injective ι →
        ∀ φ : H →ₐ[R] T,
          (∃ φ' : H' →ₐ[R] T, φ'.comp (π : H →ₐ[R] H') = φ) ↔
            WithConv.toConv (ι.comp φ) ∈ Γ := by
  classical

  have hRK : Function.Injective (algebraMap R (AlgebraicClosure ℚ)) := by
    intro a b h
    apply IsFractionRing.injective R ℚ
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    simpa only [← IsScalarTower.algebraMap_apply] using h

  haveI : Finite (H →ₐ[R] AlgebraicClosure ℚ) := finite_algHom R (AlgebraicClosure ℚ) H
  haveI : Finite (WithConv (H →ₐ[R] AlgebraicClosure ℚ)) :=
    Finite.of_equiv (H →ₐ[R] AlgebraicClosure ℚ)
      ⟨WithConv.toConv, WithConv.ofConv, WithConv.ofConv_toConv, WithConv.toConv_ofConv⟩
  have hunit : ∀ x : WithConv (H →ₐ[R] AlgebraicClosure ℚ), IsUnit x := fun x =>
    HopfAlgebra.isUnit_withConv_algHom x
  let e := unitEquiv hunit

  let act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      Additive (WithConv (H →ₐ[R] AlgebraicClosure ℚ))ˣ →
      Additive (WithConv (H →ₐ[R] AlgebraicClosure ℚ))ˣ := fun σ m =>
    e (WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars R).comp
      (WithConv.ofConv (e.symm m))))
  have hact : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[R] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f) := by
    intro σ f g hfg
    simp only [act, Equiv.symm_apply_apply]
    congr 1
    rw [← WithConv.toConv_ofConv g]
    congr 1
    ext h
    exact hfg h

  let N0 : AddSubgroup (Additive (WithConv (H →ₐ[R] AlgebraicClosure ℚ))ˣ) :=
    { carrier := {m | e.symm m ∈ Γ}
      zero_mem' := by
        change e.symm 0 ∈ Γ
        rw [unitEquiv_symm_apply, toMul_zero, Units.val_one]
        exact Γ.one_mem
      add_mem' := fun {a b} ha hb => by
        change e.symm (a + b) ∈ Γ
        rw [unitEquiv_symm_apply, toMul_add, Units.val_mul]
        exact Γ.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        change e.symm (-a) ∈ Γ
        rw [unitEquiv_symm_apply, toMul_neg]
        exact inv_mem_of_finite (Γ.comap (Units.coeHom _)) ha }
  have hN0 : ∀ m, m ∈ N0 ↔ e.symm m ∈ Γ := fun m => Iff.rfl
  let N : Fin (1 + 1) → AddSubgroup (Additive (WithConv (H →ₐ[R] AlgebraicClosure ℚ))ˣ) := ![N0, ⊤]
  have hmono : ∀ i : Fin 1, N i.castSucc ≤ N i.succ := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact le_top
  have htop : N (Fin.last 1) = ⊤ := rfl
  have hstab : ∀ (i : Fin (1 + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x : Additive (WithConv (H →ₐ[R] AlgebraicClosure ℚ))ˣ), x ∈ N i → act σ x ∈ N i := by
    intro i σ x hx
    refine Fin.cases ?_ (fun j => ?_) i hx
    · intro hx0
      change act σ x ∈ N0
      rw [hN0]
      simp only [act, Equiv.symm_apply_apply]
      exact hgal σ (e.symm x) hx0
    · intro _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact AddSubgroup.mem_top _

  obtain ⟨B, _, _, π, φ, -, hflat, hπsurj, -, -, -, hfac, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain R hRK H
      (Additive (WithConv (H →ₐ[R] AlgebraicClosure ℚ))ˣ) e (unitEquiv_mul hunit) act hact
      1 N hmono htop hstab
  haveI : Module.Finite R (B 0) := (hfin inferInstance 0).1
  haveI : Module.Flat R (B 0) := hflat 0
  haveI : Coalgebra.IsCocomm R (B 0) := hcocomm inferInstance 0

  have hcrit : ∀ f : H →ₐ[R] AlgebraicClosure ℚ,
      (∃ g : B 0 →ₐ[R] AlgebraicClosure ℚ, g.comp (π 0 : H →ₐ[R] B 0) = f) ↔
        WithConv.toConv f ∈ Γ := by
    intro f
    rw [hfac 0 f]
    change e (WithConv.toConv f) ∈ N0 ↔ _
    rw [hN0, Equiv.symm_apply_apply]
  refine ⟨B 0, inferInstance, inferInstance, π 0, hπsurj 0, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  ·
    apply le_antisymm
    · refine le_iInf₂ fun ν hν => ?_
      obtain ⟨g, hg⟩ := (hcrit (WithConv.ofConv ν)).mpr (by rwa [WithConv.toConv_ofConv])
      intro x hx
      rw [RingHom.mem_ker] at hx ⊢
      have := AlgHom.congr_fun hg x
      rw [AlgHom.comp_apply] at this
      rw [← this]
      change g (π 0 x) = 0
      rw [hx, map_zero]
    · intro x hx
      rw [RingHom.mem_ker]
      apply eq_zero_of_forall_algHom R (AlgebraicClosure ℚ) (B 0) hRK
      intro g
      have hmem : WithConv.toConv (g.comp (π 0 : H →ₐ[R] B 0)) ∈ Γ := (hcrit _).mp ⟨g, rfl⟩
      have hx' := (Submodule.mem_iInf _).mp hx (WithConv.toConv (g.comp (π 0 : H →ₐ[R] B 0)))
      have hx'' := (Submodule.mem_iInf _).mp hx' hmem
      rw [WithConv.ofConv_toConv, RingHom.mem_ker, AlgHom.comp_apply] at hx''
      exact hx''
  ·
    intro T _ _ ι hι ψ
    constructor
    · rintro ⟨ψ', hψ'⟩
      rw [← hcrit]
      exact ⟨ι.comp ψ', by rw [AlgHom.comp_assoc, hψ']⟩
    · intro hmem
      obtain ⟨g, hg⟩ := (hcrit _).mpr hmem
      have hker : RingHom.ker (π 0 : H →ₐ[R] B 0).toRingHom ≤ RingHom.ker ψ.toRingHom := by
        intro x hx
        rw [RingHom.mem_ker] at hx ⊢
        apply hι
        rw [map_zero]
        have := AlgHom.congr_fun hg x
        rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
        change ι (ψ x) = 0
        rw [← this]
        change g ((π 0 : H →ₐ[R] B 0) x) = 0
        rw [show (π 0 : H →ₐ[R] B 0) x = 0 from hx, map_zero]
      refine ⟨AlgHom.liftOfSurjective _ (hπsurj 0) ψ hker, ?_⟩
      ext x
      rw [AlgHom.comp_apply]
      exact AlgHom.liftOfSurjective_apply _ (hπsurj 0) ψ hker x

end S_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure (solution)
