-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b66d932a-9cb2-560f-987a-668c90377975

import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_exists_finiteFlat_quotient_of_equivariant_surjection
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Mathlib.Algebra.Group.TypeTags.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped Classical
open WithConv

namespace E54ChildA

variable {p : ℕ} {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]

noncomputable def galAct (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
  WithConv.toConv ((σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv f))

@[scoped simp] lemma ofConv_galAct (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    WithConv.ofConv (galAct σ f) =
      (σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv f) := by
  rw [galAct, WithConv.ofConv_toConv]

@[scoped simp] lemma galAct_spec (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (h : H) :
    (WithConv.ofConv (galAct σ f)) h = σ ((WithConv.ofConv f) h) := by
  rw [ofConv_galAct]; rfl

lemma withConv_ext {f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)}
    (h : ∀ x : H, (WithConv.ofConv f) x = (WithConv.ofConv g) x) : f = g :=
  WithConv.ofConv_injective (AlgHom.ext h)

lemma galAct_eq_of (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
    (hfg : ∀ h : H, (WithConv.ofConv g) h = σ ((WithConv.ofConv f) h)) : g = galAct σ f :=
  withConv_ext fun x => (hfg x).trans (galAct_spec σ f x).symm

lemma galAct_mul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    galAct σ (f * g) = galAct σ f * galAct σ g := by
  apply withConv_ext
  intro h
  rw [galAct_spec, AlgHom.convMul_apply, AlgHom.convMul_apply,
    ofConv_galAct, ofConv_galAct]

  generalize (Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) h) = z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
      simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.coe_comp,
        Function.comp_apply]
      rfl

lemma galAct_one (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    galAct (H := H) (p := p) σ 1 = 1 := by
  apply withConv_ext
  intro h
  simp only [galAct_spec, AlgHom.convOne_apply]
  exact (σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt p)).commutes _

lemma galAct_id (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    galAct 1 f = f :=
  withConv_ext fun h => by simp [galAct_spec]

lemma galAct_comp (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    galAct (σ * τ) f = galAct σ (galAct τ f) :=
  withConv_ext fun h => by simp only [galAct_spec]; rfl

abbrev M : Type := Additive (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))

noncomputable scoped instance instDMA :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (M (p := p) (H := H)) where
  smul σ m := Additive.ofMul (galAct σ (Additive.toMul m))
  one_smul m := by
    show Additive.ofMul (galAct 1 (Additive.toMul m)) = m
    rw [galAct_id]; rfl
  mul_smul σ τ m := by
    show Additive.ofMul (galAct (σ * τ) (Additive.toMul m)) =
         Additive.ofMul (galAct σ (Additive.toMul (Additive.ofMul (galAct τ (Additive.toMul m)))))
    rw [galAct_comp]; rfl
  smul_zero σ := by
    show Additive.ofMul (galAct σ (Additive.toMul (0 : Additive _))) = 0
    show Additive.ofMul (galAct σ 1) = Additive.ofMul 1
    rw [galAct_one]
  smul_add σ m n := by
    show Additive.ofMul (galAct σ (Additive.toMul (m + n))) =
         Additive.ofMul (galAct σ (Additive.toMul m)) + Additive.ofMul (galAct σ (Additive.toMul n))
    show Additive.ofMul (galAct σ (Additive.toMul m * Additive.toMul n)) =
         Additive.ofMul (galAct σ (Additive.toMul m) * galAct σ (Additive.toMul n))
    rw [galAct_mul]

noncomputable def eM : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M (p := p) (H := H) :=
  Additive.ofMul

lemma eM_mul (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
    eM (f * g) = eM f + eM g := rfl

lemma eM_act (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
    (hfg : ∀ h : H, (WithConv.ofConv g) h = σ ((WithConv.ofConv f) h)) :
    eM g = σ • (eM f) := by
  show Additive.ofMul g = Additive.ofMul (galAct σ (Additive.toMul (Additive.ofMul f)))
  congr 1
  exact galAct_eq_of σ f g hfg

end E54ChildA
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E54ChildA"

namespace E55ConvGroup

open WithConv

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {C : Type} [CommRing C] [Algebra R C]

variable (R G) in

noncomputable def antipodeAlgHom : G →ₐ[R] G :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] lemma antipodeAlgHom_apply (g : G) : antipodeAlgHom R G g = HopfAlgebra.antipode R g := rfl

lemma convMul_comp_antipode_left (φ : WithConv (G →ₐ[R] C)) :
    toConv (φ.ofConv.comp (antipodeAlgHom R G)) * φ = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R g
  conv_lhs => rw [← ℛ.eq]
  simp only [map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
    antipodeAlgHom_apply]
  rw [← φ.ofConv.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul]

noncomputable scoped instance : Group (WithConv (G →ₐ[R] C)) where
  inv φ := toConv (φ.ofConv.comp (antipodeAlgHom R G))
  inv_mul_cancel φ := convMul_comp_antipode_left φ

noncomputable scoped instance [Coalgebra.IsCocomm R G] : CommGroup (WithConv (G →ₐ[R] C)) where
  mul_comm := mul_comm

end E55ConvGroup
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E54ChildA P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E55ConvGroup"

namespace E55

abbrev Gal := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable {M : Type} [AddCommGroup M] [DistribMulAction Gal M]

def IsStable (K : AddSubgroup M) : Prop := ∀ (σ : Gal), ∀ m ∈ K, σ • m ∈ K

section Sub
variable {K : AddSubgroup M} (hK : IsStable K)

noncomputable def subDMA : DistribMulAction Gal ↥K where
  smul σ x := ⟨σ • (x : M), hK σ x x.2⟩
  one_smul x := Subtype.ext (one_smul Gal (x : M))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : M))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ (x : M) (y : M))

lemma subDMA_coe (σ : Gal) (x : ↥K) :
    letI := subDMA hK; ((σ • x : ↥K) : M) = σ • (x : M) := rfl

end Sub
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E54ChildA P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E55ConvGroup"

section Quot
variable {K : AddSubgroup M} (hK : IsStable K)

noncomputable def quotDMA : DistribMulAction Gal (M ⧸ K) where
  smul σ := Quotient.map' (σ • ·) (fun a b hab => by
    rw [QuotientAddGroup.leftRel_apply] at hab ⊢
    have h := hK σ _ hab
    rwa [smul_add, smul_neg] at h)
  one_smul x := by induction x using QuotientAddGroup.induction_on with
    | H m => exact congrArg QuotientAddGroup.mk (one_smul Gal m)
  mul_smul σ τ x := by induction x using QuotientAddGroup.induction_on with
    | H m => exact congrArg QuotientAddGroup.mk (mul_smul σ τ m)
  smul_zero σ := congrArg QuotientAddGroup.mk (smul_zero σ)
  smul_add σ x y := by
    induction x using QuotientAddGroup.induction_on with
    | H a => induction y using QuotientAddGroup.induction_on with
      | H b => exact congrArg QuotientAddGroup.mk (smul_add σ a b)

lemma quotDMA_mk (σ : Gal) (m : M) :
    letI := quotDMA hK; (σ • (QuotientAddGroup.mk m : M ⧸ K)) = QuotientAddGroup.mk (σ • m) := rfl

end Quot
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E54ChildA P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E55ConvGroup"

end E55
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E54ChildA P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E55ConvGroup"

namespace E55

lemma e_pow_of_add {X : Type} [Monoid X] {Y : Type} [AddCommGroup Y]
    (e : X ≃ Y) (he_add : ∀ f g : X, e (f * g) = e f + e g) :
    ∀ (n : ℕ) (f : X), e (f^n) = n • e f := by
  have he1 : e 1 = 0 := by
    have h := (he_add 1 1).symm; rw [one_mul] at h
    exact add_left_cancel (h.trans (add_zero (e 1)).symm)
  intro n; induction n with
  | zero => intro f; rw [pow_zero, zero_nsmul]; exact he1
  | succ k ih => intro f; rw [pow_succ, he_add, ih, succ_nsmul, add_comm]

end E55
p2m_reactivate "P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E54ChildA P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.E55ConvGroup"

theorem E55.finite_algHom {R : Type} [CommRing R] {G : Type} [CommRing G] [Algebra R G]
    [Module.Finite R G] {K : Type} [Field K] [Algebra R K] :
    Finite (G →ₐ[R] K) := by

  have li0 := linearIndependent_monoidHom G K
  have hinj : Function.Injective (fun φ : G →ₐ[R] K => (φ : G →* K)) := by
    intro p q hpq; exact DFunLike.ext _ _ fun x => DFunLike.congr_fun hpq x
  have li1 : LinearIndependent K (fun φ : G →ₐ[R] K => ((φ : G →* K) : G → K)) :=
    li0.comp _ hinj

  let c : (G →ₗ[R] K) →ₗ[K] (G → K) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have li2 : LinearIndependent K (fun φ : G →ₐ[R] K => φ.toLinearMap) :=
    LinearIndependent.of_comp c li1

  obtain ⟨n, ℓ, hℓ⟩ := Module.Finite.exists_fin' R G
  let D : (G →ₗ[R] K) →ₗ[K] ((Fin n → R) →ₗ[R] K) :=
    { toFun := fun f => f.comp ℓ
      map_add' := fun f g => rfl
      map_smul' := fun a f => rfl }
  have hD : Function.Injective D := by
    intro f g hfg
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hℓ x
    exact DFunLike.congr_fun hfg y
  haveI : Module.Finite K ((Fin n → R) →ₗ[R] K) :=
    Module.Finite.equiv ((Pi.basisFun R (Fin n)).constr K)
  haveI : Module.Finite K (G →ₗ[R] K) := Module.Finite.of_injective D hD
  exact li2.finite

open E54ChildA E55

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Type) [AddCommGroup N] [Module (IsLocalRing.ResidueField P) N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N →ₗ[IsLocalRing.ResidueField P] N)
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (hFequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → F g = act σ (F f))
    (hFne : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F f ≠ 0) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H'),
      Module.Finite (GaloisRep.ratLocalizedAt p) H' ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H' ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H' ∧
      (∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1) ∧
      ∃ F' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N,
        (∀ f g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          F' (f * g) = F' f + F' g) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ∀ f g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H', g h = σ (f h)) → F' g = act σ (F' f)) ∧
        (∃ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F' f ≠ 0) ∧
        (∀ S : Submonoid (WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ f ∈ S,
            ∀ g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
              (∀ h : H', g h = σ (f h)) → g ∈ S) →
          S = ⊥ ∨ S = ⊤) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  haveI instFin : Finite (M (p := p) (H := H)) := by
    have hfin : Finite (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
      E55.finite_algHom
    have hfinW : Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
      Finite.of_equiv _ (WithConv.equiv _).symm
    exact Finite.of_equiv _ (Additive.ofMul (α := WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))

  have hF1 : F 1 = 0 := by
    have h := (hFmul 1 1).symm; rw [one_mul] at h
    exact add_left_cancel (h.trans (add_zero (F 1)).symm)
  let Ft : M (p := p) (H := H) →+ N :=
    { toFun := fun m => F (eM.symm m)
      map_zero' := hF1
      map_add' := fun a b => hFmul _ _ }
  have hFt_equiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ m : M (p := p) (H := H),
      Ft (σ • m) = act σ (Ft m) := by
    intro σ hσ m
    show F (eM.symm (σ • m)) = act σ (F (eM.symm m))
    have key : eM.symm (σ • m) = galAct σ (eM.symm m) := by
      apply eM.injective; rw [Equiv.apply_symm_apply]
      exact (eM_act σ (eM.symm m) (galAct σ (eM.symm m))
        (fun h => galAct_spec σ _ h)).symm
    rw [key]
    exact hFequiv σ hσ (eM.symm m) _ (fun h => galAct_spec σ _ h)

  have hMpM : ∀ m : M (p := p) (H := H), p • m = 0 := fun m => by
    have h := e_pow_of_add (eM (p := p) (H := H)) (eM_mul (p := p) (H := H)) p (eM.symm m)
    rw [Equiv.apply_symm_apply, hMp] at h
    have he1 : eM (p := p) (H := H) 1 = 0 := by
      have q := (eM_mul (p := p) (H := H) 1 1).symm; rw [one_mul] at q
      exact add_left_cancel (q.trans (add_zero _).symm)
    rw [he1] at h; exact h.symm

  obtain ⟨G', hG'stab, hG'ne, G₀, hG₀stab, hG₀le, hG₀ker, hQsimple⟩ :
      ∃ (G' : AddSubgroup (M (p := p) (H := H))) (_ : IsStable G')
        (_ : ∃ m ∈ G', Ft m ≠ 0)
        (G₀ : AddSubgroup (M (p := p) (H := H))) (_ : IsStable G₀) (_ : G₀ ≤ G')
        (_ : ∀ m ∈ G₀, Ft m = 0),
        ∀ (K : AddSubgroup (M (p := p) (H := H))), IsStable K → G₀ ≤ K → K ≤ G' →
          K = G₀ ∨ K = G' :=
    by

    haveI : Finite (Set (M (p := p) (H := H))) := inferInstance
    haveI : Finite (AddSubgroup (M (p := p) (H := H))) :=
      Finite.of_injective (fun K => (K : Set (M (p := p) (H := H)))) SetLike.coe_injective

    let Pset : Set (AddSubgroup (M (p := p) (H := H))) :=
      {K | IsStable K ∧ ∃ m ∈ K, Ft m ≠ 0}
    have hPtop : (⊤ : AddSubgroup (M (p := p) (H := H))) ∈ Pset := by
      refine ⟨fun σ m _ => trivial, ?_⟩
      obtain ⟨f, hf⟩ := hFne
      exact ⟨eM f, trivial, by show F (eM.symm (eM f)) ≠ 0; rw [Equiv.symm_apply_apply]; exact hf⟩

    obtain ⟨G', hG'P, hG'min⟩ :=
      Finite.to_wellFoundedLT.wf.has_min Pset ⟨⊤, hPtop⟩

    have hbotstab : IsStable (M := M (p := p) (H := H)) (⊥ : AddSubgroup _) := by
      intro σ m hm; rw [AddSubgroup.mem_bot] at hm ⊢; rw [hm]; exact smul_zero σ
    have hbotlt : (⊥ : AddSubgroup (M (p := p) (H := H))) < G' := by
      rw [bot_lt_iff_ne_bot]; intro h
      obtain ⟨m, hm, hmne⟩ := hG'P.2
      rw [h, AddSubgroup.mem_bot] at hm; rw [hm, map_zero] at hmne; exact hmne rfl
    let Qset : Set (AddSubgroup (M (p := p) (H := H))) := {K | IsStable K ∧ K < G'}

    obtain ⟨G₀, hG₀Q, hG₀max⟩ :=
      Finite.to_wellFoundedGT.wf.has_min Qset ⟨⊥, hbotstab, hbotlt⟩

    refine ⟨G', hG'P.1, hG'P.2, G₀, hG₀Q.1, hG₀Q.2.le, ?_, ?_⟩
    ·
      intro m hm
      by_contra hne
      exact hG'min G₀ ⟨hG₀Q.1, m, hm, hne⟩ hG₀Q.2
    ·
      intro K hKstab hG₀K hKG'
      rcases eq_or_lt_of_le hKG' with hKeq | hKlt
      · exact Or.inr hKeq
      · rcases lt_or_eq_of_le hG₀K with hlt | heq
        · exact absurd hlt (hG₀max K ⟨hKstab, hKlt⟩)
        · exact Or.inl heq.symm

  letI iG' : DistribMulAction Gal ↥G' := subDMA hG'stab
  let G₀' : AddSubgroup ↥G' := G₀.addSubgroupOf G'
  have hG₀'stab : IsStable (M := ↥G') G₀' := by
    intro σ x hx
    have hx' : (x : M (p := p) (H := H)) ∈ G₀ := hx
    exact hG₀stab σ _ hx'
  letI iQ : DistribMulAction Gal (↥G' ⧸ G₀') := quotDMA hG₀'stab

  obtain ⟨H₁, iCR₁, iHA₁, hFin₁, hFl₁, hCC₁, e₁, he₁_add, he₁_act⟩ :=
    GaloisRep.exists_finiteFlat_sub_of_equivariant_injection p H
      (eM (p := p) (H := H)) (eM_mul (p := p) (H := H))
      (fun σ f g hfg => eM_act σ f g hfg)
      (ι := G'.subtype) G'.subtype_injective
      (fun σ n => (subDMA_coe hG'stab σ n).symm)
  letI : CommRing H₁ := iCR₁
  letI : HopfAlgebra (GaloisRep.ratLocalizedAt p) H₁ := iHA₁
  haveI : Module.Finite (GaloisRep.ratLocalizedAt p) H₁ := hFin₁
  haveI : Module.Flat (GaloisRep.ratLocalizedAt p) H₁ := hFl₁
  haveI : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₁ := hCC₁

  have hπeq : ∀ (σ : Gal) (m : ↥G'),
      QuotientAddGroup.mk' G₀' (σ • m) = σ • QuotientAddGroup.mk' G₀' m :=
    fun σ m => rfl
  obtain ⟨H', iCR', iHA', hFin', hFl', hCC', e', he'_add, he'_act⟩ :=
    @GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection p H₁ iCR₁ iHA₁
      hFin₁ hFl₁ hCC₁ (↥G') _ iG' e₁ he₁_add he₁_act
      (↥G' ⧸ G₀') _ iQ (QuotientAddGroup.mk' G₀')
      (QuotientAddGroup.mk'_surjective G₀') hπeq
  letI : CommRing H' := iCR'
  letI : HopfAlgebra (GaloisRep.ratLocalizedAt p) H' := iHA'

  let Ftd : (↥G' ⧸ G₀') →+ N := QuotientAddGroup.lift G₀' (Ft.comp G'.subtype)
    (fun x hx => hG₀ker _ hx)
  let F' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N :=
    fun f => Ftd (e' f)

  have he'1 : e' 1 = 0 := by
    have h := e_pow_of_add e' he'_add 0 1; rwa [pow_zero, zero_nsmul] at h
  have hpQuot : ∀ q : ↥G' ⧸ G₀', p • q = 0 := by
    intro q; obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective G₀' q
    rw [← hx, ← map_nsmul, show p • x = 0 from Subtype.ext (hMpM _), map_zero]
  have hMp' : ∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1 := by
    intro f; apply e'.injective
    rw [e_pow_of_add e' he'_add p f, he'1]; exact hpQuot _

  refine ⟨H', iCR', iHA', hFin', hFl', hCC', hMp', F', ?_, ?_, ?_, ?_⟩
  ·
    intro f g
    show Ftd (e' (f * g)) = Ftd (e' f) + Ftd (e' g)
    rw [he'_add, map_add]
  ·
    intro σ hσ f g hfg
    show Ftd (e' g) = act σ (Ftd (e' f))
    rw [he'_act σ f g hfg]
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective G₀' (e' f)
    rw [← hx, ← hπeq σ x]
    exact hFt_equiv σ hσ (↑x)
  ·
    obtain ⟨m, hmG', hmne⟩ := hG'ne
    refine ⟨e'.symm (QuotientAddGroup.mk' G₀' ⟨m, hmG'⟩), ?_⟩
    show Ftd (e' (e'.symm _)) ≠ 0
    rw [Equiv.apply_symm_apply]
    exact hmne
  ·
    intro S hSclosed

    have hneg_pow : ∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e' (f ^ (p - 1)) = -(e' f) := by
      intro f
      rw [e_pow_of_add e' he'_add (p - 1) f]
      have h1 : (p - 1) • e' f + e' f = 0 := by
        have h2 : (p - 1) • e' f + 1 • e' f = p • e' f := by
          rw [← add_nsmul, Nat.sub_add_cancel hp.one_le]
        rw [one_nsmul] at h2; rw [h2]; exact hpQuot _
      exact eq_neg_of_add_eq_zero_left h1
    let KQ : AddSubgroup (↥G' ⧸ G₀') :=
      { carrier := e' '' ↑S
        zero_mem' := ⟨1, S.one_mem, he'1⟩
        add_mem' := by
          rintro a b ⟨fa, hfa, ha⟩ ⟨fb, hfb, hb⟩
          exact ⟨fa * fb, S.mul_mem hfa hfb, by rw [he'_add, ha, hb]⟩
        neg_mem' := by
          rintro a ⟨f, hf, hfa⟩
          exact ⟨f ^ (p - 1), pow_mem hf (p - 1), by rw [hneg_pow, hfa]⟩ }
    have hKQ_mem : ∀ f ∈ S, e' f ∈ KQ := fun f hf => ⟨f, hf, rfl⟩

    have hKQstab : IsStable (M := ↥G' ⧸ G₀') KQ := by
      rintro σ q ⟨f, hf, hfq⟩
      refine ⟨galAct (p := p) (H := H') σ f,
        hSclosed σ f hf (galAct (p := p) (H := H') σ f) (fun h => galAct_spec σ f h), ?_⟩
      rw [he'_act σ f (galAct (p := p) (H := H') σ f) (fun h => galAct_spec σ f h), hfq]

    let Kup : AddSubgroup ↥G' := AddSubgroup.comap (QuotientAddGroup.mk' G₀') KQ
    let K : AddSubgroup (M (p := p) (H := H)) := Kup.map G'.subtype
    have hKle : K ≤ G' := by
      rintro x ⟨y, _, hyx⟩; exact hyx ▸ y.2
    have hG₀K : G₀ ≤ K := by
      intro x hx
      refine ⟨⟨x, hG₀le hx⟩, ?_, rfl⟩
      show QuotientAddGroup.mk' G₀' ⟨x, hG₀le hx⟩ ∈ KQ
      have hx' : (⟨x, hG₀le hx⟩ : ↥G') ∈ G₀' := hx
      rw [show QuotientAddGroup.mk' G₀' ⟨x, hG₀le hx⟩ = 0 from
        (QuotientAddGroup.eq_zero_iff _).mpr hx']
      exact KQ.zero_mem
    have hKstab : IsStable K := by
      rintro σ m ⟨y, hy, hym⟩
      refine ⟨σ • y, ?_, ?_⟩
      · show QuotientAddGroup.mk' G₀' (σ • y) ∈ KQ
        rw [hπeq σ y]; exact hKQstab σ _ hy
      · rw [← hym]; exact subDMA_coe hG'stab σ y

    rcases hQsimple K hKstab hG₀K hKle with hK0 | hK1
    ·
      left
      refine le_antisymm (fun f hf => ?_) bot_le

      show f = 1
      obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective G₀' (e' f)
      have hyKup : y ∈ Kup := by show QuotientAddGroup.mk' G₀' y ∈ KQ; rw [hy]; exact hKQ_mem f hf
      have hyK : (↑y : M (p := p) (H := H)) ∈ K := ⟨y, hyKup, rfl⟩
      rw [hK0] at hyK
      have hyG₀' : y ∈ G₀' := hyK
      have h0 : e' f = 0 := by rw [← hy]; exact (QuotientAddGroup.eq_zero_iff _).mpr hyG₀'
      exact e'.injective (h0.trans he'1.symm)
    ·
      right
      refine le_antisymm le_top (fun g _ => ?_)

      obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective G₀' (e' g)
      have hyK : (↑y : M (p := p) (H := H)) ∈ K := by rw [hK1]; exact y.2
      obtain ⟨z, hzKup, hzy⟩ := hyK
      have hzy' : z = y := Subtype.ext hzy
      have hyKup : y ∈ Kup := hzy' ▸ hzKup
      have hKQg : e' g ∈ KQ := by rw [← hy]; exact hyKup
      obtain ⟨f, hfS, hfg⟩ := hKQg
      exact (e'.injective hfg) ▸ hfS

end S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map (solution)
