-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b429693a-e641-5739-b58b-583d506d00a5

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_HopfAlgebra_surjective_of_surjective_baseChange_of_pow_eq_one
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
import Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul"
open ModularCurve

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace RigN

theorem eq_of_forall_point_eq (R K Ω : Type) [CommRing R] [IsDomain R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {X : Type} [CommRing X] [HopfAlgebra R X] [Module.Finite R X] [Module.Flat R X]
    {x y : X} (h : ∀ f : X →ₐ[R] Ω, f x = f y) : x = y := by
  haveI : Algebra.Etale K (K ⊗[R] X) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero K (K ⊗[R] X)
  refine Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := X)
    (IsFractionRing.injective R K) ?_
  refine Algebra.Etale.eq_of_forall_algHom_apply_eq (K := K) (Ω := Ω) ?_
  intro χ
  simpa using h ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)

theorem e_one {R Ω X N : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
    [CommRing X] [HopfAlgebra R X] [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g) : e 1 = 0 := by
  have h : e 1 + 0 = e 1 + e 1 := by rw [add_zero, ← he, one_mul]
  exact (add_left_cancel h).symm

theorem e_pow {R Ω X N : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
    [CommRing X] [HopfAlgebra R X] [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g)
    (f : WithConv (X →ₐ[R] Ω)) (n : ℕ) : e (f ^ n) = n • e f := by
  induction n with
  | zero => rw [pow_zero, zero_smul, e_one e he]
  | succ n ih => rw [pow_succ, he, ih, succ_nsmul]

theorem point_pow_eq_one {R Ω X N : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
    [CommRing X] [HopfAlgebra R X] [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g)
    (n : ℕ) (htors : ∀ f, n • e f = 0) (f : WithConv (X →ₐ[R] Ω)) : f ^ n = 1 :=
  e.injective (by rw [e_pow e he, htors, e_one e he])

theorem point_mul_comm {R Ω X N : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
    [CommRing X] [HopfAlgebra R X] [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g)
    (f g : WithConv (X →ₐ[R] Ω)) : f * g = g * f :=
  e.injective (by rw [he, he, add_comm])

theorem comp_convPow {R X T : Type} [CommRing R] [CommRing X] [HopfAlgebra R X]
    [CommRing T] [Algebra R T] (g : X →ₐ[R] T) (u : WithConv (X →ₐ[R] X)) (n : ℕ) :
    g.comp (u ^ n).ofConv = (WithConv.toConv (g.comp u.ofConv) ^ n).ofConv := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    ext x
    exact g.commutes (Coalgebra.counit (R := R) x)
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih, WithConv.toConv_ofConv]

theorem univ_pow_eq_one (R K Ω : Type) [CommRing R] [IsDomain R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {X : Type} [CommRing X] [HopfAlgebra R X] [Module.Finite R X] [Module.Flat R X]
    {N : Type} [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g)
    (n : ℕ) (htors : ∀ f, n • e f = 0) :
    (WithConv.toConv (AlgHom.id R X) : WithConv (X →ₐ[R] X)) ^ n = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply eq_of_forall_point_eq R K Ω
  intro f
  have h1 : f (((WithConv.toConv (AlgHom.id R X) : WithConv (X →ₐ[R] X)) ^ n).ofConv x) =
      (f.comp ((WithConv.toConv (AlgHom.id R X) : WithConv (X →ₐ[R] X)) ^ n).ofConv) x := rfl
  rw [h1, comp_convPow, WithConv.ofConv_toConv, AlgHom.comp_id, point_pow_eq_one e he n htors]
  exact (f.commutes (Coalgebra.counit (R := R) x)).symm

theorem point_pow_eq_one_of_forall (R K Ω : Type) [CommRing R] [IsDomain R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {X : Type} [CommRing X] [HopfAlgebra R X] [Module.Finite R X] [Module.Flat R X]
    {N : Type} [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g)
    (n : ℕ) (htors : ∀ f, n • e f = 0)
    (T : Type) [CommRing T] [Algebra R T] (g : WithConv (X →ₐ[R] T)) : g ^ n = 1 := by
  have h := comp_convPow g.ofConv (WithConv.toConv (AlgHom.id R X)) n
  rw [univ_pow_eq_one R K Ω e he n htors, WithConv.ofConv_toConv, AlgHom.comp_id,
    WithConv.toConv_ofConv] at h
  apply WithConv.ext
  rw [← h]
  ext x
  exact g.ofConv.commutes (Coalgebra.counit (R := R) x)

theorem convPow_ofConv_comp_bialgHom {R A B C : Type} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [HopfAlgebra R B] [CommRing C] [HopfAlgebra R C]
    (u : WithConv (C →ₐ[R] A)) (h : B →ₐc[R] C) (n : ℕ) :
    (u ^ n).ofConv.comp (h : B →ₐ[R] C) =
      (WithConv.toConv (u.ofConv.comp (h : B →ₐ[R] C)) ^ n).ofConv := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    ext x
    exact congrArg (algebraMap R A) (CoalgHomClass.counit_comp_apply h x)
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.convMul_comp_bialgHom_distrib, ih, WithConv.toConv_ofConv]

theorem algHom_ext_of_surjective_baseChange (R K : Type) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {H C D : Type} [CommRing H] [Algebra R H] [CommRing C] [Algebra R C]
    [CommRing D] [Algebra R D] [Module.Flat R D]
    (j : H →ₐ[R] C) (hjK : Function.Surjective (j.toLinearMap.baseChange K))
    {F G : C →ₐ[R] D} (hFG : F.comp j = G.comp j) : F = G := by
  ext c
  apply Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := D)
    (IsFractionRing.injective R K)
  obtain ⟨z, hz⟩ := hjK ((1 : K) ⊗ₜ[R] c)
  have key : ∀ Φ : C →ₐ[R] D,
      (Algebra.TensorProduct.includeRight : D →ₐ[R] K ⊗[R] D) (Φ c) =
        (Φ.comp j).toLinearMap.baseChange K z := by
    intro Φ
    simp only [Algebra.TensorProduct.includeRight_apply, AlgHom.comp_toLinearMap,
      LinearMap.baseChange_comp, LinearMap.comp_apply, hz, LinearMap.baseChange_tmul,
      AlgHom.toLinearMap_apply]
  rw [key F, key G, hFG]

theorem point_pow_eq_one_of_surjective_baseChange (R K : Type) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type} [CommRing H] [HopfAlgebra R H]
    {C : Type} [CommRing C] [HopfAlgebra R C] [Module.Flat R C]
    (j : H →ₐc[R] C) (hjK : Function.Surjective ((j : H →ₐ[R] C).toLinearMap.baseChange K))
    (n : ℕ) (hH : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1)
    (T : Type) [CommRing T] [Algebra R T] (g : WithConv (C →ₐ[R] T)) : g ^ n = 1 := by
  have hu : (WithConv.toConv (AlgHom.id R C) : WithConv (C →ₐ[R] C)) ^ n = 1 := by
    apply WithConv.ext
    apply algHom_ext_of_surjective_baseChange R K (j : H →ₐ[R] C) hjK
    have h0 := convPow_ofConv_comp_bialgHom (WithConv.toConv (AlgHom.id R C)) j 0
    rw [pow_zero, pow_zero] at h0
    rw [convPow_ofConv_comp_bialgHom, h0, hH C]
  have h := comp_convPow g.ofConv (WithConv.toConv (AlgHom.id R C)) n
  rw [hu, WithConv.ofConv_toConv, AlgHom.comp_id, WithConv.toConv_ofConv] at h
  apply WithConv.ext
  rw [← h]
  ext x
  exact g.ofConv.commutes (Coalgebra.counit (R := R) x)

theorem points_clause_of_lam (R K Ω : Type) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {H₀ H C : Type} [CommRing H₀] [HopfAlgebra R H₀] [CommRing H] [HopfAlgebra R H]
    [CommRing C] [HopfAlgebra R C]
    {N : Type} (e : WithConv (H →ₐ[R] Ω) ≃ N) (e₀ : WithConv (H₀ →ₐ[R] Ω) ≃ N)
    (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))
    (hlam : ∀ f : WithConv (H →ₐ[R] Ω),
      e₀ (WithConv.toConv ((((Algebra.TensorProduct.lift (Algebra.ofId K Ω) f.ofConv
        (fun _ _ => Commute.all _ _)).comp lam.toAlgHom).restrictScalars R).comp
          Algebra.TensorProduct.includeRight)) = e f)
    (j₀ : H₀ →ₐc[R] C) (j : H →ₐc[R] C) (hj : Function.Injective j)
    (hcompat : ∀ y : H₀, (1 : K) ⊗ₜ[R] (j₀ y) =
      ((j : H →ₐ[R] C).toLinearMap.baseChange K) (lam ((1 : K) ⊗ₜ[R] y)))
    (ι : H₀ ≃ₐ[R] H) (hι : ∀ x, j (ι x) = j₀ x)
    (f : WithConv (H →ₐ[R] Ω)) : e₀ (WithConv.toConv (f.ofConv.comp ι.toAlgHom)) = e f := by
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hinj : Function.Injective ((j : H →ₐ[R] C).toLinearMap.baseChange K) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K) (j : H →ₐ[R] C).toLinearMap hj
  have hlam_tmul : ∀ y : H₀, lam ((1 : K) ⊗ₜ[R] y) = (1 : K) ⊗ₜ[R] ι y := fun y => hinj (by
    rw [← hcompat y, LinearMap.baseChange_tmul]
    show (1 : K) ⊗ₜ[R] j₀ y = (1 : K) ⊗ₜ[R] j (ι y)
    rw [hι y])
  rw [← hlam f]
  refine congrArg e₀ (congrArg WithConv.toConv ?_)
  ext y
  simp [hlam_tmul]

theorem isCocomm_of_points (R K Ω : Type) [CommRing R] [IsDomain R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {X : Type} [CommRing X] [HopfAlgebra R X] [Module.Finite R X] [Module.Flat R X]
    {N : Type} [AddCommGroup N]
    (e : WithConv (X →ₐ[R] Ω) ≃ N) (he : ∀ f g, e (f * g) = e f + e g) :
    Coalgebra.IsCocomm R X := by
  refine ⟨LinearMap.ext fun x => ?_⟩
  show TensorProduct.comm R X X (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) x
  apply eq_of_forall_point_eq R K Ω
  intro P
  obtain ⟨f, hf⟩ : ∃ f : X →ₐ[R] Ω, f = P.comp Algebra.TensorProduct.includeLeft := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : X →ₐ[R] Ω, g = P.comp Algebra.TensorProduct.includeRight := ⟨_, rfl⟩
  have hP : P = Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) := by
    refine Algebra.TensorProduct.ext' (fun a b => ?_)
    rw [Algebra.TensorProduct.lift_tmul, hf, hg, AlgHom.comp_apply, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have key : ∀ z : X ⊗[R] X,
      Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (TensorProduct.comm R X X z) =
        Algebra.TensorProduct.lift g f (fun _ _ => Commute.all _ _) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mul_comm]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hgf : Algebra.TensorProduct.lift g f (fun _ _ => Commute.all _ _) (Coalgebra.comul x) =
      (WithConv.toConv g * WithConv.toConv f : WithConv (X →ₐ[R] Ω)) x :=
    (AlgHom.convMul_apply _ _ _).symm
  have hfg : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (Coalgebra.comul x) =
      (WithConv.toConv f * WithConv.toConv g : WithConv (X →ₐ[R] Ω)) x :=
    (AlgHom.convMul_apply _ _ _).symm
  rw [hP, key, hgf, hfg, point_mul_comm e he]

theorem nsmul_eq_zero_of_torsionBy {P M : Type} [AddCommGroup M] [Module ℤ M] {b : ℤ}
    (e : P ≃ ↥(Submodule.torsionBy ℤ M b)) (a : ℕ) (hb : b = (a : ℤ)) (f : P) : a • e f = 0 := by
  subst hb
  exact Subtype.ext ((Nat.cast_smul_eq_nsmul ℤ a (e f).1).symm.trans
    ((Submodule.mem_torsionBy_iff (a : ℤ) (e f).1).mp (e f).2))

theorem exists_algEquiv_of_lam (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hirr : Irreducible (q : R))
    {H₀ : Type} [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Flat R H₀]
    [Coalgebra.IsCocomm R H₀]
    {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {N : Type} (e : WithConv (H →ₐ[R] Ω) ≃ N) (e₀ : WithConv (H₀ →ₐ[R] Ω) ≃ N)
    (hH : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ q = 1)
    (hH₀ : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H₀ →ₐ[R] T)), f ^ q = 1)
    (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))
    (hlam_comul : ∀ x, Coalgebra.comul (R := K) (lam x) =
      (TensorProduct.map lam.toLinearMap lam.toLinearMap) (Coalgebra.comul (R := K) x))
    (hlam_counit : ∀ x, Coalgebra.counit (R := K) (lam x) = Coalgebra.counit (R := K) x)
    (hlam : ∀ f : WithConv (H →ₐ[R] Ω),
      e₀ (WithConv.toConv ((((Algebra.TensorProduct.lift (Algebra.ofId K Ω) f.ofConv
        (fun _ _ => Commute.all _ _)).comp lam.toAlgHom).restrictScalars R).comp
          Algebra.TensorProduct.includeRight)) = e f) :
    ∃ ι : H₀ ≃ₐ[R] H,
      (Bialgebra.counitAlgHom R H).comp ι.toAlgHom = Bialgebra.counitAlgHom R H₀ ∧
      ∀ f : WithConv (H →ₐ[R] Ω), e₀ (WithConv.toConv (f.ofConv.comp ι.toAlgHom)) = e f := by
  have hsup :=
    HopfAlgebra.exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange K lam
      hlam_comul hlam_counit
  obtain ⟨C, _, _, _, _, _, j₀, j, hj₀, hj, hj₀K, hjK, hcompat⟩ := hsup
  have hC : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (C →ₐ[R] T)), f ^ q ^ 1 = 1 :=
    fun T _ _ f => by
      rw [pow_one]
      exact point_pow_eq_one_of_surjective_baseChange R K j hjK q hH T f
  have hH' : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ q ^ 1 = 1 :=
    fun T _ _ f => by rw [pow_one]; exact hH T f
  have hH₀' : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H₀ →ₐ[R] T)), f ^ q ^ 1 = 1 :=
    fun T _ _ f => by rw [pow_one]; exact hH₀ T f
  have hjs : Function.Surjective j :=
    HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one K q hq2 hirr 1 hH' hC j hjK
  have hj₀s : Function.Surjective j₀ :=
    HopfAlgebra.surjective_of_surjective_baseChange_of_pow_eq_one K q hq2 hirr 1 hH₀' hC j₀ hj₀K
  have hjb : Function.Bijective (j : H →ₐ[R] C) := ⟨hj, hjs⟩
  have hj₀b : Function.Bijective (j₀ : H₀ →ₐ[R] C) := ⟨hj₀, hj₀s⟩
  let ι : H₀ ≃ₐ[R] H := (AlgEquiv.ofBijective _ hj₀b).trans (AlgEquiv.ofBijective _ hjb).symm
  have hι : ∀ x, j (ι x) = j₀ x := fun x =>
    AlgEquiv.ofBijective_apply_symm_apply (j : H →ₐ[R] C) hjb (j₀ x)
  refine ⟨ι, ?_, fun f => points_clause_of_lam R K Ω e e₀ lam hlam j₀ j hj hcompat ι hι f⟩
  ext x
  have h1 : Coalgebra.counit (R := R) (j (ι x)) = Coalgebra.counit (R := R) (ι x) :=
    CoalgHomClass.counit_comp_apply j (ι x)
  have h2 : Coalgebra.counit (R := R) (j₀ x) = Coalgebra.counit (R := R) x :=
    CoalgHomClass.counit_comp_apply j₀ x
  rw [hι x] at h1
  exact h1.symm.trans h2

theorem comp_eq_comp_of_points (R K Ω : Type) [CommRing R] [IsDomain R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {H₀ : Type} [CommRing H₀] [HopfAlgebra R H₀]
    {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    {N M A : Type} (e : WithConv (H →ₐ[R] Ω) ≃ N) (e₀ : WithConv (H₀ →ₐ[R] Ω) ≃ N)
    (v : N → M) (hv : Function.Injective v) (act : A → M → M)
    (φ : A → (H →ₐ[R] H)) (φ₀ : A → (H₀ →ₐ[R] H₀))
    (hφ : ∀ (t : A) (f g : WithConv (H →ₐ[R] Ω)),
      (∀ h : H, g.ofConv h = f.ofConv (φ t h)) → v (e g) = act t (v (e f)))
    (hφ₀ : ∀ (t : A) (f g : WithConv (H₀ →ₐ[R] Ω)),
      (∀ h : H₀, g.ofConv h = f.ofConv (φ₀ t h)) → v (e₀ g) = act t (v (e₀ f)))
    (ι : H₀ ≃ₐ[R] H)
    (hpts : ∀ f : WithConv (H →ₐ[R] Ω), e₀ (WithConv.toConv (f.ofConv.comp ι.toAlgHom)) = e f)
    (t : A) : ι.toAlgHom.comp (φ₀ t) = (φ t).comp ι.toAlgHom := by
  ext x
  apply eq_of_forall_point_eq R K Ω
  intro f
  have hb : v (e₀ (WithConv.toConv ((f.comp ι.toAlgHom).comp (φ₀ t)))) =
      act t (v (e₀ (WithConv.toConv (f.comp ι.toAlgHom)))) :=
    hφ₀ t _ _ (fun _ => rfl)
  have hc : v (e (WithConv.toConv (f.comp (φ t)))) = act t (v (e (WithConv.toConv f))) :=
    hφ t _ _ (fun _ => rfl)
  have h2a : e₀ (WithConv.toConv (f.comp ι.toAlgHom)) = e (WithConv.toConv f) :=
    hpts (WithConv.toConv f)
  have h2c : e₀ (WithConv.toConv ((f.comp (φ t)).comp ι.toAlgHom)) =
      e (WithConv.toConv (f.comp (φ t))) :=
    hpts (WithConv.toConv (f.comp (φ t)))
  have hpt : WithConv.toConv ((f.comp ι.toAlgHom).comp (φ₀ t)) =
      WithConv.toConv ((f.comp (φ t)).comp ι.toAlgHom) := by
    apply e₀.injective
    apply hv
    rw [hb, h2a, ← hc, ← h2c]
  exact congrArg (fun g : WithConv (H₀ →ₐ[R] Ω) => g.ofConv x) hpt

end RigN

namespace RigN

section Pts

variable {q : ℕ} {X : Type} [CommRing X] [HopfAlgebra (GaloisRep.ratLocalizedAt q) X]

def res (F : (ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ) :
    X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ :=
  (F.restrictScalars (GaloisRep.ratLocalizedAt q)).comp Algebra.TensorProduct.includeRight

theorem res_apply (F : (ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ) (x : X) :
    res F x = F ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] x) := rfl

private def _root_.RigN.ext (f : X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) :
    (ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ (AlgebraicClosure ℚ)) f (fun _ _ => Commute.all _ _)

p2m_export "RigN" "ext"
theorem ext_tmul (f : X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) (r : ℚ) (x : X) :
    ext f (r ⊗ₜ[GaloisRep.ratLocalizedAt q] x) = algebraMap ℚ (AlgebraicClosure ℚ) r * f x :=
  Algebra.TensorProduct.lift_tmul _ _ _ r x

theorem res_ext (f : X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) : res (ext f) = f := by
  apply AlgHom.ext
  intro x
  rw [res_apply, ext_tmul, map_one, one_mul]

theorem ext_res (F : (ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ) :
    ext (res F) = F := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AlgHom.ext
    intro x
    show ext (res F) ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] x) =
      F ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] x)
    rw [ext_tmul, map_one, one_mul, res_apply]

theorem ext_comp_apply {Y : Type} [CommRing Y] [HopfAlgebra (GaloisRep.ratLocalizedAt q) Y]
    (u : X →ₐ[GaloisRep.ratLocalizedAt q] Y) (g : Y →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)
    (z : ℚ ⊗[GaloisRep.ratLocalizedAt q] X) :
    ext (g.comp u) z = ext g (u.toLinearMap.baseChange ℚ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r x => rw [LinearMap.baseChange_tmul, ext_tmul, ext_tmul]; rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

def ptsEquiv : WithConv ((ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ) ≃
    WithConv (X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) where
  toFun F := WithConv.toConv (res F.ofConv)
  invFun f := WithConv.toConv (ext f.ofConv)
  left_inv F := by
    show WithConv.toConv (ext (res F.ofConv)) = F
    rw [ext_res]
  right_inv f := by
    show WithConv.toConv (res (ext f.ofConv)) = f
    rw [res_ext]

theorem ptsEquiv_apply (F : WithConv ((ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ))
    (x : X) : (ptsEquiv F) x = F ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] x) := rfl

theorem ptsEquiv_symm_apply (f : WithConv (X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
    (z : ℚ ⊗[GaloisRep.ratLocalizedAt q] X) : (ptsEquiv.symm f) z = ext f.ofConv z := rfl

theorem ptsEquiv_mul (F G : WithConv ((ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ)) :
    ptsEquiv (F * G) = ptsEquiv F * ptsEquiv G := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  show (F * G).ofConv ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] x) = (ptsEquiv F * ptsEquiv G).ofConv x
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def]
  induction Coalgebra.comul (R := GaloisRep.ratLocalizedAt q) x with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero]
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | tmul a b =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl

theorem ptsEquiv_symm_mul (f g : WithConv (X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) :
    ptsEquiv.symm (f * g) = ptsEquiv.symm f * ptsEquiv.symm g := by
  apply ptsEquiv.injective
  rw [ptsEquiv_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem ptsEquiv_act (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (F G : WithConv ((ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∀ a, G a = σ (F a)) : ∀ x : X, (ptsEquiv G) x = σ ((ptsEquiv F) x) :=
  fun _ => h _

end Pts

section Graph

variable {q : ℕ} {H₀ H C : Type} [CommRing H₀] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H₀]
  [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [CommRing C] [HopfAlgebra (GaloisRep.ratLocalizedAt q) C]

theorem comp_eq_ptsEquiv_of_compat
    (lam : (ℚ ⊗[GaloisRep.ratLocalizedAt q] H₀) ≃ₐ[ℚ] (ℚ ⊗[GaloisRep.ratLocalizedAt q] H))
    (j₀ : H₀ →ₐ[GaloisRep.ratLocalizedAt q] C) (j : H →ₐ[GaloisRep.ratLocalizedAt q] C)
    (hcompat : ∀ y : H₀, (1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] (j₀ y) =
      (j.toLinearMap.baseChange ℚ) (lam ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] y)))
    (g : C →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) :
    WithConv.toConv (g.comp j₀) =
      ptsEquiv (WithConv.toConv ((ext (g.comp j)).comp lam.toAlgHom)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  show g (j₀ y) = ext (g.comp j) (lam ((1 : ℚ) ⊗ₜ[GaloisRep.ratLocalizedAt q] y))
  rw [ext_comp_apply, ← hcompat, ext_tmul, map_one, one_mul]

end Graph

section Gal

open ModularCurve

variable (p : ℕ) (q : ℕ)

@[reducible]
def torsionAction :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ↥(Submodule.torsionBy ℤ (JZero p) ((q : ℤ) ^ 1)) where
  smul σ x := ⟨σ • (x : JZero p), by
    have hx := x.2
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    show ((q : ℤ) ^ 1) • (DistribSMul.toAddMonoidHom (JZero p) σ (x : JZero p)) = 0
    rw [← map_zsmul, hx, map_zero]⟩
  one_smul x := Subtype.ext
    (one_smul (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : JZero p))
  smul_zero σ := Subtype.ext (smul_zero (A := JZero p) σ)
  smul_add σ x y := Subtype.ext (smul_add σ (x : JZero p) (y : JZero p))

theorem torsionAction_smul_coe (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : ↥(Submodule.torsionBy ℤ (JZero p) ((q : ℤ) ^ 1))) :
    letI := torsionAction p q
    ((σ • x : ↥(Submodule.torsionBy ℤ (JZero p) ((q : ℤ) ^ 1))) : JZero p) = σ • (x : JZero p) :=
  rfl

end Gal

section Gen

open ModularCurve

scoped instance ratAlgClosure_isGalois :
    @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _

scoped instance ratAlgClosure_isAlgebraic :
    @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ DivisionRing.toRatAlgebra :=
  AlgebraicClosure.isAlgebraic ℚ

variable {q : ℕ}

theorem etale_baseChange (X : Type) [CommRing X] [HopfAlgebra (GaloisRep.ratLocalizedAt q) X]
    [Module.Finite (GaloisRep.ratLocalizedAt q) X] :
    Algebra.Etale ℚ (ℚ ⊗[GaloisRep.ratLocalizedAt q] X) :=
  HopfAlgebra.algebra_etale_of_module_finite_of_charZero ℚ (ℚ ⊗[GaloisRep.ratLocalizedAt q] X)

theorem ptsEquiv_add_of {X : Type} [CommRing X] [HopfAlgebra (GaloisRep.ratLocalizedAt q) X] {M : Type} [Add M]
    (e : WithConv (X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (F G : WithConv ((ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ)) :
    e (ptsEquiv (F * G)) = e (ptsEquiv F) + e (ptsEquiv G) := by
  rw [ptsEquiv_mul, he]

theorem ptsEquiv_act_of (p q : ℕ) {X : Type} [CommRing X] [HopfAlgebra (GaloisRep.ratLocalizedAt q) X]
    (e : WithConv (X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero p) ((q : ℤ) ^ 1)))
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (X →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ h : X, g h = σ (f h)) → ((e g : JZero p)) = σ • (e f : JZero p))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (F G : WithConv ((ℚ ⊗[GaloisRep.ratLocalizedAt q] X) →ₐ[ℚ] AlgebraicClosure ℚ)) (hFG : ∀ a, G a = σ (F a)) :
    letI := torsionAction p q
    e (ptsEquiv G) = σ • e (ptsEquiv F) :=
  Subtype.ext (he_act σ (ptsEquiv F) (ptsEquiv G) (ptsEquiv_act σ F G hFG))

theorem exists_lam_of_models (p : ℕ) (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero p) ((q : ℤ) ^ 1)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : JZero p)) = σ • (e f : JZero p))
    (H₀ : Type) [CommRing H₀] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H₀]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H₀] [Module.Flat (GaloisRep.ratLocalizedAt q) H₀]
    (e₀ : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero p) ((q : ℤ) ^ 1)))
    (he₀_add : ∀ f g, e₀ (f * g) = e₀ f + e₀ g)
    (he₀_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = σ (f h)) → ((e₀ g : JZero p)) = σ • (e₀ f : JZero p)) :
    ∃ lam : (ℚ ⊗[GaloisRep.ratLocalizedAt q] H₀) ≃ₐ[ℚ] (ℚ ⊗[GaloisRep.ratLocalizedAt q] H),
      (∀ x, Coalgebra.comul (R := ℚ) (lam x) =
        (TensorProduct.map lam.toLinearMap lam.toLinearMap) (Coalgebra.comul (R := ℚ) x)) ∧
      (∀ x, Coalgebra.counit (R := ℚ) (lam x) = Coalgebra.counit (R := ℚ) x) ∧
      ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
        e₀ (WithConv.toConv ((((Algebra.TensorProduct.lift (Algebra.ofId ℚ (AlgebraicClosure ℚ))
            f.ofConv (fun _ _ => Commute.all _ _)).comp lam.toAlgHom).restrictScalars
            (GaloisRep.ratLocalizedAt q)).comp Algebra.TensorProduct.includeRight)) = e f := by
  letI := torsionAction p q
  haveI := etale_baseChange (q := q) H
  haveI := etale_baseChange (q := q) H₀
  obtain ⟨lam, hcomul, hcounit, hpts⟩ :=
    HopfAlgebra.exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
      ℚ (AlgebraicClosure ℚ) (ℚ ⊗[GaloisRep.ratLocalizedAt q] H) (ptsEquiv.trans e) (ptsEquiv_add_of e he_add)
      (ptsEquiv_act_of p q e he_act) (ℚ ⊗[GaloisRep.ratLocalizedAt q] H₀) (ptsEquiv.trans e₀)
      (ptsEquiv_add_of e₀ he₀_add) (ptsEquiv_act_of p q e₀ he₀_act)
  refine ⟨lam, hcomul, hcounit, fun f => ?_⟩
  have h : e₀ (ptsEquiv (WithConv.toConv
      ((WithConv.ofConv (ptsEquiv.symm f)).comp lam.toAlgHom))) = e (ptsEquiv (ptsEquiv.symm f)) :=
    hpts (ptsEquiv.symm f)
  exact h.trans (congrArg e (Equiv.apply_symm_apply ptsEquiv f))

end Gen

end RigN
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero.RigN"

open ModularCurve in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N))
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφI : ∀ t : HeckeAlg,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ t))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N))
    (H₀ : Type) [CommRing H₀] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₀]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₀] [Module.Flat (GaloisRep.ratLocalizedAt p) H₀]
    (e₀ : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
    (he₀_add : ∀ f g, e₀ (f * g) = e₀ f + e₀ g)
    (he₀_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = σ (f h)) → ((e₀ g : JZero N)) = σ • (e₀ f : JZero N))
    (φ₀ : HeckeAlg → (H₀ →ₐ[GaloisRep.ratLocalizedAt p] H₀))
    (hφ₀I : ∀ t : HeckeAlg,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀)).comap (φ₀ t))
    (hφ₀ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = f (φ₀ t h)) → ((e₀ g : JZero N)) = t • (e₀ f : JZero N)) :
    ∃ ι : H₀ ≃ₐ[GaloisRep.ratLocalizedAt p] H,
      (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H).comp ι.toAlgHom =
        Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀ ∧
      (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₀ (WithConv.toConv (f.ofConv.comp ι.toAlgHom)) = e f) ∧
      ∀ t : HeckeAlg, ι.toAlgHom.comp (φ₀ t) = (φ t).comp ι.toAlgHom := by
  classical
  have _ := hφI
  have _ := hφ₀I
  letI := heckeModuleBar N

  haveI hdvr : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt p) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI hfr : IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ :=
    GaloisRep.isFractionRing_ratLocalizedAt p
  have hirr : Irreducible ((p : ℕ) : GaloisRep.ratLocalizedAt p) :=
    GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out

  have htors : ∀ f, p • e f = 0 := RigN.nsmul_eq_zero_of_torsionBy e p (pow_one _)
  have htors₀ : ∀ f, p • e₀ f = 0 := RigN.nsmul_eq_zero_of_torsionBy e₀ p (pow_one _)
  haveI hcc : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H :=
    RigN.isCocomm_of_points (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) e he_add
  haveI hcc₀ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₀ :=
    RigN.isCocomm_of_points (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) e₀ he₀_add
  have hH : ∀ (T : Type) [CommRing T] [Algebra (GaloisRep.ratLocalizedAt p) T]
      (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] T)), f ^ p = 1 := fun T _ _ f =>
    RigN.point_pow_eq_one_of_forall (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) e he_add p
      htors T f
  have hH₀ : ∀ (T : Type) [CommRing T] [Algebra (GaloisRep.ratLocalizedAt p) T]
      (f : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] T)), f ^ p = 1 := fun T _ _ f =>
    RigN.point_pow_eq_one_of_forall (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) e₀ he₀_add p
      htors₀ T f

  have hlam := RigN.exists_lam_of_models N p H e he_add he_act H₀ e₀ he₀_add he₀_act
  obtain ⟨lam, hlam_comul, hlam_counit, hlam_pts⟩ := hlam

  have hiota := RigN.exists_algEquiv_of_lam (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) p
    hp2 hirr e e₀ hH hH₀ lam hlam_comul hlam_counit hlam_pts
  obtain ⟨ι, hcounit, hpts⟩ := hiota

  refine ⟨ι, hcounit, hpts, fun t => ?_⟩
  exact RigN.comp_eq_comp_of_points (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ) e e₀
    (fun x => (x : JZero N)) Subtype.val_injective (fun (t : HeckeAlg) (x : JZero N) => t • x) φ φ₀
    hφ hφ₀ ι hpts t

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero.RigN"

end S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero (solution)
