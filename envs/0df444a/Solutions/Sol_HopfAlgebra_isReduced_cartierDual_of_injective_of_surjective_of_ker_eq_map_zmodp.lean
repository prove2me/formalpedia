-- Prove2me | solution 1 for HopfAlgebra.isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/184bbcc3-e29f-57ff-87a8-29403d6fa9c5

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgHom_exists_comp_eq_of_faithfullyFlat_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_faithfullyFlat_of_isReduced_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false
set_option linter.unusedSectionVars false

open scoped TensorProduct

universe u v w

noncomputable section

namespace HopfAlgebra
p2m_export "HopfAlgebra" "faithfullyFlat_of_isReduced_of_isAlgClosed"
namespace ExtRed
p2m_open "HopfAlgebra"

abbrev Kb (p : ℕ) [Fact p.Prime] : Type := AlgebraicClosure (ZMod p)

section Gen

variable {F : Type} [Field F]

theorem map_injective_of_surjective
    {A : Type v} [CommRing A] [Bialgebra F A] [Module.Finite F A]
    {B : Type v} [CommRing B] [Bialgebra F B] [Module.Finite F B]
    (f : A →ₐc[F] B) (hf : Function.Surjective f) : Function.Injective (CartierDual.map f) := by
  intro φ ψ h
  apply CartierDual.ext
  intro b
  obtain ⟨a, rfl⟩ := hf b
  have := congrArg (fun χ : CartierDual F A => χ a) h
  simpa only [CartierDual.map_apply] using this

theorem map_surjective_of_injective
    {A : Type v} [CommRing A] [Bialgebra F A] [Module.Finite F A]
    {B : Type v} [CommRing B] [Bialgebra F B] [Module.Finite F B]
    (f : A →ₐc[F] B) (hf : Function.Injective f) : Function.Surjective (CartierDual.map f) := by
  intro ψ
  obtain ⟨φ, hφ⟩ := (f : A →ₗ[F] B).dualMap_surjective_of_injective hf (CartierDual.toDual F A ψ)
  refine ⟨(CartierDual.toDual F B).symm φ, ?_⟩
  apply (CartierDual.toDual F A).injective
  rw [CartierDual.toDual_map, LinearEquiv.apply_symm_apply, hφ]

theorem apply_apply_eq_of_ker_eq_map
    {K : Type v} [CommRing K] [Bialgebra F K] {B : Type v} [CommRing B] [Bialgebra F B]
    {Q : Type v} [CommRing Q] [Bialgebra F Q]
    (j : K →ₐc[F] B) (π : B →ₐc[F] Q)
    (hex : RingHom.ker (π : B →ₐ[F] Q) = Ideal.map (j : K →ₐ[F] B) (RingHom.ker (Bialgebra.counitAlgHom F K)))
    (x : K) : π (j x) = algebraMap F Q (Coalgebra.counit (R := F) x) := by
  have hx : x - algebraMap F K (Coalgebra.counit (R := F) x) ∈ RingHom.ker (Bialgebra.counitAlgHom F K) := by
    rw [RingHom.mem_ker, map_sub, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Bialgebra.counit_algebraMap, sub_self]
  have hjx : (j : K →ₐ[F] B) (x - algebraMap F K (Coalgebra.counit (R := F) x)) ∈ RingHom.ker (π : B →ₐ[F] Q) := by
    rw [hex]
    exact Ideal.mem_map_of_mem _ hx
  rw [RingHom.mem_ker, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_eq_zero] at hjx
  exact hjx

theorem map_map_apply
    {K : Type v} [CommRing K] [Bialgebra F K] [Module.Finite F K]
    {B : Type v} [CommRing B] [Bialgebra F B] [Module.Finite F B]
    {Q : Type v} [CommRing Q] [Bialgebra F Q] [Module.Finite F Q]
    (j : K →ₐc[F] B) (π : B →ₐc[F] Q)
    (hex : RingHom.ker (π : B →ₐ[F] Q) = Ideal.map (j : K →ₐ[F] B) (RingHom.ker (Bialgebra.counitAlgHom F K)))
    (φ : CartierDual F Q) :
    CartierDual.map j (CartierDual.map π φ) =
      algebraMap F (CartierDual F K) (Coalgebra.counit (R := F) φ) := by
  apply CartierDual.ext
  intro x
  rw [CartierDual.map_apply, CartierDual.map_apply, apply_apply_eq_of_ker_eq_map j π hex,
    CartierDual.algebraMap_apply, CartierDual.counit_apply]

  rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]

end Gen

section Count

variable {F : Type} [Field F] (L : Type) [Field L] [Algebra F L]
  {K : Type v} [CommRing K] [HopfAlgebra F K] [Coalgebra.IsCocomm F K] [Module.Finite F K]
  {B : Type v} [CommRing B] [HopfAlgebra F B] [Coalgebra.IsCocomm F B] [Module.Finite F B]
  {Q : Type v} [CommRing Q] [HopfAlgebra F Q] [Coalgebra.IsCocomm F Q] [Module.Finite F Q]
  (j : K →ₐc[F] B) (π : B →ₐc[F] Q)

def res (φ : CartierDual F B →ₐ[F] L) : CartierDual F Q →ₐ[F] L :=
  φ.comp (CartierDual.map π : CartierDual F Q →ₐ[F] CartierDual F B)

def pull (ψ : CartierDual F K →ₐ[F] L) : CartierDual F B →ₐ[F] L :=
  ψ.comp (CartierDual.map j : CartierDual F B →ₐ[F] CartierDual F K)

def combine (σ : (CartierDual F Q →ₐ[F] L) → (CartierDual F B →ₐ[F] L))
    (x : (CartierDual F Q →ₐ[F] L) × (CartierDual F K →ₐ[F] L)) : CartierDual F B →ₐ[F] L :=
  (WithConv.toConv (σ x.1) * WithConv.toConv (pull L j x.2)).ofConv

theorem res_pull
    (hex : RingHom.ker (π : B →ₐ[F] Q) = Ideal.map (j : K →ₐ[F] B) (RingHom.ker (Bialgebra.counitAlgHom F K)))
    (ψ : CartierDual F K →ₐ[F] L) :
    WithConv.toConv (res L π (pull L j ψ)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun θ => ?_)
  change ψ (CartierDual.map j (CartierDual.map π θ)) = (1 : WithConv (CartierDual F Q →ₐ[F] L)).ofConv θ
  rw [map_map_apply j π hex, AlgHom.commutes, AlgHom.convOne_apply]

theorem res_combine (σ : (CartierDual F Q →ₐ[F] L) → (CartierDual F B →ₐ[F] L)) (hσ : ∀ χ, res L π (σ χ) = χ)
    (hex : RingHom.ker (π : B →ₐ[F] Q) = Ideal.map (j : K →ₐ[F] B) (RingHom.ker (Bialgebra.counitAlgHom F K)))
    (x : (CartierDual F Q →ₐ[F] L) × (CartierDual F K →ₐ[F] L)) :
    res L π (combine L j σ x) = x.1 := by
  have h1 : WithConv.toConv (res L π (combine L j σ x)) =
      PDivisibleGroup.Hopf.convCompMonoidHom L (CartierDual.map π) (WithConv.toConv (σ x.1)) *
        PDivisibleGroup.Hopf.convCompMonoidHom L (CartierDual.map π) (WithConv.toConv (pull L j x.2)) := by
    rw [← map_mul]
    rfl
  have h2 : PDivisibleGroup.Hopf.convCompMonoidHom L (CartierDual.map π) (WithConv.toConv (pull L j x.2)) = 1 :=
    res_pull L j π hex x.2
  have h3 : PDivisibleGroup.Hopf.convCompMonoidHom L (CartierDual.map π) (WithConv.toConv (σ x.1)) =
      WithConv.toConv x.1 := by
    rw [PDivisibleGroup.Hopf.convCompMonoidHom_apply]
    exact congrArg WithConv.toConv (hσ x.1)
  apply WithConv.toConv_injective
  rw [h1, h2, mul_one, h3]

theorem pull_injective (hj : Function.Injective j) : Function.Injective (pull L j) := by
  intro ψ ψ' h
  refine AlgHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := map_surjective_of_injective j hj y
  exact AlgHom.congr_fun h x

theorem combine_injective (hj : Function.Injective j)
    (hex : RingHom.ker (π : B →ₐ[F] Q) = Ideal.map (j : K →ₐ[F] B) (RingHom.ker (Bialgebra.counitAlgHom F K)))
    (σ : (CartierDual F Q →ₐ[F] L) → (CartierDual F B →ₐ[F] L)) (hσ : ∀ χ, res L π (σ χ) = χ) :
    Function.Injective (combine L j σ) := by
  rintro ⟨χ, ψ⟩ ⟨χ', ψ'⟩ h
  have hχ : χ = χ' := by
    have e1 := res_combine L j π σ hσ hex (χ, ψ)
    have e2 := res_combine L j π σ hσ hex (χ', ψ')
    dsimp only at e1 e2
    rw [← e1, ← e2, h]
  subst hχ
  have h' : WithConv.toConv (σ χ) * WithConv.toConv (pull L j ψ) =
      WithConv.toConv (σ χ) * WithConv.toConv (pull L j ψ') := congrArg WithConv.toConv h
  have hc := (PDivisibleGroup.Hopf.isUnit_toConv_algHom (σ χ)).mul_left_cancel h'
  have := pull_injective L j hj (WithConv.toConv_injective hc)
  rw [this]

end Count

section Sec3

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in

theorem etale_of_isReduced_of_perfectField (K A : Type*) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced A] : Algebra.Etale K A := by
  haveI : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  refine ⟨MaximalSpectrum A, inferInstance, fun I => A ⧸ I.asIdeal, inferInstance, inferInstance,
    (IsArtinianRing.equivPi A).restrictScalars K, fun I => ⟨inferInstance, ?_⟩⟩
  haveI : Module.Finite K (A ⧸ I.asIdeal) := inferInstance
  haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
  infer_instance

theorem isReduced_baseChange_of_isReduced_zmodp (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Algebra (ZMod p) k]
    (E : Type*) [CommRing E] [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [IsReduced E] :
    IsReduced (k ⊗[ZMod p] E) := by
  haveI : Algebra.Etale (ZMod p) E := etale_of_isReduced_of_perfectField (ZMod p) E
  haveI : Algebra.Etale k (k ⊗[ZMod p] E) := Algebra.Etale.baseChange (ZMod p) E k
  haveI : Algebra.EssFiniteType k (k ⊗[ZMod p] E) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ZMod p] E)

theorem cartierDual_map_injective_of_surjective {k : Type*} [CommRing k]
    {A : Type*} [CommRing A] [Bialgebra k A] [Module.Finite k A] [Module.Free k A]
    {B : Type*} [CommRing B] [Bialgebra k B] [Module.Finite k B] [Module.Free k B]
    (f : A →ₐc[k] B) (hf : Function.Surjective f) :
    Function.Injective (CartierDual.map f) := by
  intro φ ψ h
  refine CartierDual.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hf b
  have := congrArg (fun χ : CartierDual k A => χ a) h
  simpa only [CartierDual.map_apply] using this

theorem exists_comp_eq_of_injective {k : Type u} [Field k] [IsAlgClosed k]
    {R : Type v} [CommRing R] [HopfAlgebra k R] {S : Type w} [CommRing S] [HopfAlgebra k S]
    (hR : @Module.Finite k R _ _ Algebra.toModule) (hRred : IsReduced R) (hS : @Module.Finite k S _ _ Algebra.toModule)
    (f : R →ₐc[k] S) (hf : Function.Injective f) (x : R →ₐ[k] k) :
    ∃ y : S →ₐ[k] k, y.comp (f : R →ₐ[k] S) = x := by
  haveI := hR
  haveI := hRred
  haveI := hS
  letI := (f : R →ₐ[k] S).toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := R) (A := S) fun c => ((f : R →ₐ[k] S).commutes c).symm
  have hf' : ∀ r : R, algebraMap R S r = f r := fun _ => rfl
  have hcomul : ∀ r : R, Coalgebra.comul (R := k) (algebraMap R S r) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R S) (IsScalarTower.toAlgHom k R S)
        (Coalgebra.comul (R := k) r) := by
    intro r
    rw [hf', ← CoalgHomClass.map_comp_comul_apply f r]
    induction Coalgebra.comul (R := k) r using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcounit : ∀ r : R, Coalgebra.counit (R := k) (algebraMap R S r) = Coalgebra.counit (R := k) r := by
    intro r
    rw [hf']
    exact CoalgHomClass.counit_comp_apply f r
  haveI := HopfAlgebra.faithfullyFlat_of_isReduced_of_isAlgClosed (k := k) (K := R) (H := S) hcomul hcounit hf
  obtain ⟨y, hy⟩ := AlgHom.exists_comp_eq_of_faithfullyFlat_of_isAlgClosed k R S x
  exact ⟨y, hy⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem comp_map_surjective (p : ℕ) [Fact p.Prime]
    {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {Q : Type v} [CommRing Q] [HopfAlgebra (ZMod p) Q] [Coalgebra.IsCocomm (ZMod p) Q] [Module.Finite (ZMod p) Q]
    (π : B →ₐc[ZMod p] Q) (hπ : Function.Surjective π) (hQ : IsReduced (CartierDual (ZMod p) Q)) :
    Function.Surjective (fun φ : CartierDual (ZMod p) B →ₐ[ZMod p] Kb p =>
      φ.comp (CartierDual.map π : CartierDual (ZMod p) Q →ₐ[ZMod p] CartierDual (ZMod p) B)) := by
  intro χ
  have hπd : Function.Injective (CartierDual.map π) := cartierDual_map_injective_of_surjective π hπ

  let fB := Bialgebra.TensorProduct.map (BialgHom.id (Kb p) (Kb p)) (CartierDual.map π)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (CartierDual.map π : CartierDual (ZMod p) Q →ₗ[ZMod p] CartierDual (ZMod p) B) (LinearMap.ker_eq_bot.mpr hπd)
  have hG : Function.LeftInverse (g.baseChange (Kb p)) fB := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      calc g.baseChange (Kb p) (fB 0) = g.baseChange (Kb p) 0 := congrArg _ (map_zero fB)
        _ = 0 := map_zero _
    | tmul a d =>
      have e1 : fB (a ⊗ₜ[ZMod p] d) = a ⊗ₜ[ZMod p] CartierDual.map π d := Bialgebra.TensorProduct.map_tmul _ _ a d
      calc g.baseChange (Kb p) (fB (a ⊗ₜ[ZMod p] d))
          = g.baseChange (Kb p) (a ⊗ₜ[ZMod p] CartierDual.map π d) := congrArg _ e1
        _ = a ⊗ₜ[ZMod p] g (CartierDual.map π d) := LinearMap.baseChange_tmul _ _ _
        _ = a ⊗ₜ[ZMod p] d := congrArg (fun t => a ⊗ₜ[ZMod p] t) (LinearMap.congr_fun hg d)
    | add x y hx hy =>
      calc g.baseChange (Kb p) (fB (x + y)) = g.baseChange (Kb p) (fB x + fB y) := congrArg _ (map_add fB x y)
        _ = g.baseChange (Kb p) (fB x) + g.baseChange (Kb p) (fB y) := map_add _ _ _
        _ = x + y := by rw [hx, hy]
  have hinj : Function.Injective fB := hG.injective
  haveI : IsReduced (CartierDual (ZMod p) Q) := hQ
  have hRred := isReduced_baseChange_of_isReduced_zmodp p (Kb p) (CartierDual (ZMod p) Q)
  have hfinR : Module.Finite (Kb p) (Kb p ⊗[ZMod p] CartierDual (ZMod p) Q) := inferInstance
  have hfinS : Module.Finite (Kb p) (Kb p ⊗[ZMod p] CartierDual (ZMod p) B) := inferInstance

  have key0 := @exists_comp_eq_of_injective (Kb p) _ _ (Kb p ⊗[ZMod p] CartierDual (ZMod p) Q) _ _ (Kb p ⊗[ZMod p] CartierDual (ZMod p) B) _ _
  have key := key0 hfinR hRred hfinS fB hinj
  obtain ⟨y, hy⟩ := key (Algebra.TensorProduct.lift (AlgHom.id (Kb p) (Kb p)) χ (fun _ _ => Commute.all _ _))
  let φ : CartierDual (ZMod p) B →ₐ[ZMod p] Kb p :=
    { toFun := fun d => y ((1 : Kb p) ⊗ₜ[ZMod p] d)
      map_one' := (congrArg y Algebra.TensorProduct.one_def.symm).trans (map_one y)
      map_mul' := fun d e => by rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
      map_add' := fun d e => by rw [TensorProduct.tmul_add, map_add]
      commutes' := fun c => by
        have h1 : ((1 : Kb p) ⊗ₜ[ZMod p] algebraMap (ZMod p) (CartierDual (ZMod p) B) c) =
            (algebraMap (ZMod p) (Kb p) c) ⊗ₜ[ZMod p] (1 : CartierDual (ZMod p) B) := by
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        have h2 : (algebraMap (ZMod p) (Kb p) c) ⊗ₜ[ZMod p] (1 : CartierDual (ZMod p) B) =
            algebraMap (Kb p) _ (algebraMap (ZMod p) (Kb p) c) := rfl
        show y ((1 : Kb p) ⊗ₜ[ZMod p] algebraMap (ZMod p) (CartierDual (ZMod p) B) c) = algebraMap (ZMod p) (Kb p) c
        rw [h1, h2, AlgHom.commutes]
        rfl }
  refine ⟨φ, ?_⟩
  refine AlgHom.ext fun d => ?_
  show y ((1 : Kb p) ⊗ₜ[ZMod p] CartierDual.map π d) = χ d
  have h1 : fB ((1 : Kb p) ⊗ₜ[ZMod p] d) = (1 : Kb p) ⊗ₜ[ZMod p] CartierDual.map π d :=
    Bialgebra.TensorProduct.map_tmul _ _ (1 : Kb p) d
  have h2 := congrArg (fun g : _ →ₐ[Kb p] Kb p => g ((1 : Kb p) ⊗ₜ[ZMod p] d)) hy

  have h3 : Algebra.TensorProduct.lift (AlgHom.id (Kb p) (Kb p)) χ (fun _ _ => Commute.all _ _)
      ((1 : Kb p) ⊗ₜ[ZMod p] d) = χ d := by
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
  exact ((congrArg y h1.symm).trans h2).trans h3

end Sec3

end HopfAlgebra.ExtRed

end

open HopfAlgebra.ExtRed in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {K : Type v} [CommRing K] [HopfAlgebra (ZMod p) K] [Coalgebra.IsCocomm (ZMod p) K] [Module.Finite (ZMod p) K]
    {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {Q : Type v} [CommRing Q] [HopfAlgebra (ZMod p) Q] [Coalgebra.IsCocomm (ZMod p) Q] [Module.Finite (ZMod p) Q]
    (j : K →ₐc[ZMod p] B) (hj : Function.Injective j)
    (π : B →ₐc[ZMod p] Q) (hπ : Function.Surjective π)
    (hex : RingHom.ker (π : B →ₐ[ZMod p] Q) =
      Ideal.map (j : K →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) K)))
    (hrank : Module.finrank (ZMod p) B = Module.finrank (ZMod p) K * Module.finrank (ZMod p) Q)
    (hK : IsReduced (CartierDual (ZMod p) K)) (hQ : IsReduced (CartierDual (ZMod p) Q)) :
    IsReduced (CartierDual (ZMod p) B) := by
  classical
  haveI : PerfectField (ZMod p) := inferInstance

  have hKc := (Algebra.isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed (ZMod p) (Kb p)
    (CartierDual (ZMod p) K)).1 hK
  have hQc := (Algebra.isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed (ZMod p) (Kb p)
    (CartierDual (ZMod p) Q)).1 hQ
  rw [CartierDual.finrank_eq] at hKc hQc

  obtain ⟨σ, hσ⟩ := (comp_map_surjective p π hπ hQ).hasRightInverse

  have hle : Nat.card ((CartierDual (ZMod p) Q →ₐ[ZMod p] Kb p) × (CartierDual (ZMod p) K →ₐ[ZMod p] Kb p)) ≤
      Nat.card (CartierDual (ZMod p) B →ₐ[ZMod p] Kb p) :=
    Nat.card_le_card_of_injective _ (combine_injective (Kb p) j π hj hex σ hσ)
  rw [Nat.card_prod, hKc, hQc] at hle

  have hge := card_algHom_le_finrank (ZMod p) (CartierDual (ZMod p) B) (Kb p)
  rw [CartierDual.finrank_eq] at hge

  refine (Algebra.isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed (ZMod p) (Kb p)
    (CartierDual (ZMod p) B)).2 ?_
  rw [CartierDual.finrank_eq]
  refine le_antisymm hge ?_
  rw [hrank, mul_comm]
  exact hle

end S_HopfAlgebra_isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp
end P2MW
export P2MW.S_HopfAlgebra_isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp (solution)
