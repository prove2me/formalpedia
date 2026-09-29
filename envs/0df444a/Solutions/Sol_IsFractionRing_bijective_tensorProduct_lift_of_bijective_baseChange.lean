-- Prove2me | solution 1 for IsFractionRing.bijective_tensorProduct_lift_of_bijective_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b25ef9e2-21bc-5eab-840d-379bbcf08169

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct

namespace FracBC

theorem isLocalization_algebraMapSubmonoid_nonZeroDivisors
    (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [FaithfulSMul A B] [Field L] [Algebra B L] [IsFractionRing B L] :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
    (nonZeroDivisors B) (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B le_rfl) ?_).2 inferInstance
  intro b hb
  have hint : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  obtain ⟨a, ha, hdvd⟩ := (hint.isAlgebraic).exists_nonzero_dvd hb
  exact ⟨algebraMap A B a, Algebra.mem_algebraMapSubmonoid_of_mem
    (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ : nonZeroDivisors A), hdvd⟩

end FracBC

open FracBC in
theorem solution
    {R S Rhat T K₁ K E F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [CommRing Rhat] [IsDomain Rhat]
    [CommRing T] [IsDomain T] [Field K₁] [Field K] [Field E] [Field F]

    [Algebra R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra S K] [IsFractionRing S K]
    [Algebra R K] [Algebra K₁ K] [IsScalarTower R S K] [IsScalarTower R K₁ K]

    [Algebra R Rhat] [Algebra Rhat E] [IsFractionRing Rhat E]
    [Algebra R E] [Algebra K₁ E] [IsScalarTower R Rhat E] [IsScalarTower R K₁ E]

    [Algebra Rhat T] [Algebra S T] [Algebra R T] [IsScalarTower R Rhat T] [IsScalarTower R S T]
    (hT : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId Rhat T) (IsScalarTower.toAlgHom R S T)
        (fun _ _ => Commute.all _ _) : Rhat ⊗[R] S →ₐ[Rhat] T))
    [Algebra T F] [IsFractionRing T F]

    [Algebra E F] [Algebra Rhat F] [IsScalarTower Rhat E F] [IsScalarTower Rhat T F]
    [Algebra K F] [Algebra S F] [IsScalarTower S K F] [IsScalarTower S T F]
    [Algebra K₁ F] [IsScalarTower K₁ E F] [IsScalarTower K₁ K F] :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
        (fun _ _ => Commute.all _ _) : E ⊗[K₁] K →ₐ[E] F) := by
  classical

  set liftT : Rhat ⊗[R] S →ₐ[Rhat] T := Algebra.TensorProduct.lift (Algebra.ofId Rhat T)
    (IsScalarTower.toAlgHom R S T) (fun _ _ => Commute.all _ _) with hliftT
  set Φ : E ⊗[K₁] K →ₐ[E] F := Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
    (fun _ _ => Commute.all _ _) with hΦ

  haveI : FaithfulSMul R S := inferInstance
  have hRhatF : Function.Injective (algebraMap Rhat F) := by
    rw [IsScalarTower.algebraMap_eq Rhat E F]
    exact (algebraMap E F).injective.comp (IsFractionRing.injective Rhat E)
  haveI : FaithfulSMul Rhat T := by
    refine (faithfulSMul_iff_algebraMap_injective Rhat T).mpr fun a b hab => hRhatF ?_
    rw [IsScalarTower.algebraMap_apply Rhat T F a, IsScalarTower.algebraMap_apply Rhat T F b, hab]

  haveI : Module.Finite Rhat T := Module.Finite.of_surjective liftT.toLinearMap hT.2

  have hKloc : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) K :=
    isLocalization_algebraMapSubmonoid_nonZeroDivisors R S K
  have hFloc : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors Rhat)) F :=
    isLocalization_algebraMapSubmonoid_nonZeroDivisors Rhat T F
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors Rhat)) (T ⊗[Rhat] E) :=
    IsLocalization.tensor E (nonZeroDivisors Rhat)

  have hb : IsBaseChange K₁ (IsScalarTower.toAlgHom R S K).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K₁ _).mp
      (isLocalizedModule_iff_isLocalization.mpr hKloc)

  let Θa : E ⊗[K₁] (K₁ ⊗[R] S) ≃ₗ[K₁] E ⊗[K₁] K := LinearEquiv.lTensor E hb.equiv
  let Θb : E ⊗[K₁] (K₁ ⊗[R] S) ≃ₗ[E] E ⊗[R] S := TensorProduct.AlgebraTensorModule.cancelBaseChange R K₁ E E S
  let Θc : E ⊗[Rhat] (Rhat ⊗[R] S) ≃ₗ[E] E ⊗[R] S := TensorProduct.AlgebraTensorModule.cancelBaseChange R Rhat E E S
  let eT : Rhat ⊗[R] S ≃ₗ[Rhat] T := (AlgEquiv.ofBijective liftT hT).toLinearEquiv
  let Θd : E ⊗[Rhat] (Rhat ⊗[R] S) ≃ₗ[Rhat] E ⊗[Rhat] T := LinearEquiv.lTensor E eT
  let Θe : E ⊗[Rhat] T ≃ₗ[Rhat] T ⊗[Rhat] E := TensorProduct.comm Rhat E T
  let ι : T ⊗[Rhat] E ≃ₐ[T] F :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid T (nonZeroDivisors Rhat)) (T ⊗[Rhat] E) F

  have hιT : ∀ t : T, ι (t ⊗ₜ[Rhat] (1 : E)) = algebraMap T F t := by
    intro t
    have h1 : algebraMap T (T ⊗[Rhat] E) t = t ⊗ₜ[Rhat] (1 : E) := by
      rw [Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [← h1, AlgEquiv.commutes]
  have htm : ∀ a : Rhat, (1 : T) ⊗ₜ[Rhat] algebraMap Rhat E a = algebraMap Rhat T a ⊗ₜ[Rhat] (1 : E) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one (A := E) a, Algebra.algebraMap_eq_smul_one (A := T) a,
      TensorProduct.smul_tmul]
  have hιE : ∀ e : E, ι ((1 : T) ⊗ₜ[Rhat] e) = algebraMap E F e := by
    let g : E →+* F := (ι : T ⊗[Rhat] E ≃ₐ[T] F).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[Rhat] T ⊗[Rhat] E).toRingHom
    have hg : ∀ e : E, g e = ι ((1 : T) ⊗ₜ[Rhat] e) := fun e => rfl
    have hext : g = algebraMap E F := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors Rhat) ?_
      ext a
      show ι ((1 : T) ⊗ₜ[Rhat] algebraMap Rhat E a) = algebraMap E F (algebraMap Rhat E a)
      rw [← IsScalarTower.algebraMap_apply Rhat E F a, htm, hιT, ← IsScalarTower.algebraMap_apply Rhat T F a]
    intro e
    rw [← hg, hext]
  have hι : ∀ (t : T) (e : E), ι (t ⊗ₜ[Rhat] e) = algebraMap T F t * algebraMap E F e := by
    intro t e
    have h : t ⊗ₜ[Rhat] e = (t ⊗ₜ[Rhat] (1 : E)) * ((1 : T) ⊗ₜ[Rhat] e) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, hιT, hιE]

  have htt : ∀ (e : E) (k : K₁) (s : S), Φ (Θa (e ⊗ₜ[K₁] (k ⊗ₜ[R] s))) =
      ι (Θe (Θd (Θc.symm (Θb (e ⊗ₜ[K₁] (k ⊗ₜ[R] s)))))) := by
        intro e k s
        simp only [Θa, Θb, Θc, Θd, Θe, LinearEquiv.lTensor_tmul, IsBaseChange.equiv_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.comm_tmul, hΦ,
          Algebra.TensorProduct.lift_tmul, hι]
        simp only [eT, AlgEquiv.toLinearEquiv_apply, AlgEquiv.ofBijective_apply, hliftT,
          Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.toLinearMap_apply,
          IsScalarTower.coe_toAlgHom', Algebra.ofId_apply, Algebra.smul_def, map_mul]
        rw [← IsScalarTower.algebraMap_apply K₁ K F, ← IsScalarTower.algebraMap_apply S K F,
          ← IsScalarTower.algebraMap_apply K₁ E F, IsScalarTower.algebraMap_apply S T F]
        ring
  have htmul : ∀ (e : E) (y : K₁ ⊗[R] S), Φ (Θa (e ⊗ₜ[K₁] y)) = ι (Θe (Θd (Θc.symm (Θb (e ⊗ₜ[K₁] y))))) := by
    intro e y
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [show (0 : K₁ ⊗[R] S) = (0 : K₁) ⊗ₜ[R] (0 : S) from (TensorProduct.zero_tmul K₁ (0 : S)).symm]
      exact htt e 0 0
    | tmul k s => exact htt e k s
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  have hcomp : ∀ x : E ⊗[K₁] (K₁ ⊗[R] S), Φ (Θa x) = ι (Θe (Θd (Θc.symm (Θb x)))) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [show (0 : E ⊗[K₁] (K₁ ⊗[R] S)) = (0 : E) ⊗ₜ[K₁] (0 : K₁ ⊗[R] S) from
        (TensorProduct.zero_tmul E (0 : K₁ ⊗[R] S)).symm]
      exact htmul 0 0
    | tmul e y => exact htmul e y
    | add x y hx hy => simp only [map_add, hx, hy]

  have hfun : (Φ : E ⊗[K₁] K → F) = fun z => ι (Θe (Θd (Θc.symm (Θb (Θa.symm z))))) := by
    funext z
    rw [← hcomp (Θa.symm z), LinearEquiv.apply_symm_apply]
  show Function.Bijective (Φ : E ⊗[K₁] K → F)
  rw [hfun]
  exact ι.bijective.comp (Θe.bijective.comp (Θd.bijective.comp (Θc.symm.bijective.comp
    (Θb.bijective.comp Θa.symm.bijective))))

end S_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange
end P2MW
export P2MW.S_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange (solution)
